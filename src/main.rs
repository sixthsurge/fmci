mod parsing;

use std::cell::{Ref, RefCell};
use std::fmt::{Debug, Display, Formatter};
use std::process::exit;

use auto_impl::auto_impl;
use color_print::cprintln;
use derive_more::{Display, From, Into, IsVariant};
use dyn_clone::DynClone;
use itertools::Itertools;
use nom_language::error::convert_error;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet, FxHasher};
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;
use string_interner::backend::BucketBackend;
use string_interner::symbol::SymbolU32;
use string_interner::{DefaultBackend, StringInterner};
use thiserror::Error;

use crate::parsing::parse_term;

pub const DEFAULT_STACK_ID: &'static str = "Lambda";
pub const EMPTY_STACK_SYMBOL: &'static str = "Eps";
pub const EMPTY_SUM_SYMBOL: &'static str = "0";

pub type InternedSymbol = SymbolU32;
pub type Interner = StringInterner<BucketBackend<InternedSymbol>, FxBuildHasher>;

pub struct Storage {
    strings: RefCell<Interner>,
}

impl Storage {
    pub fn intern(&self, s: impl AsRef<str>) -> InternedSymbol {
        self.strings.borrow_mut().get_or_intern(s)
    }

    pub fn resolve<'s>(&'s self, s: InternedSymbol) -> Ref<'s, str> {
        Ref::map(self.strings.borrow(), |strings| {
            strings.resolve(s).expect("missing string for symbol")
        })
    }

    pub fn var(&self, name: impl AsRef<str>) -> Term {
        Term::Variable(self.intern(name).into())
    }

    pub fn app(&self, stack: impl AsRef<str>, n: Term, m: Term) -> Term {
        Term::Application(self.intern(stack).into(), Box::new(n), Box::new(m))
    }

    pub fn abs(
        &self,
        stack: impl AsRef<str>,
        x: impl AsRef<str>,
        m: Term,
        ty: Option<Type>,
    ) -> Term {
        Term::Abstraction(
            self.intern(stack).into(),
            self.intern(x).into(),
            Box::new(m),
            ty,
        )
    }

    pub fn abs_untyped(&self, stack: impl AsRef<str>, x: impl AsRef<str>, m: Term) -> Term {
        Term::Abstraction(
            self.intern(stack).into(),
            self.intern(x).into(),
            Box::new(m),
            None,
        )
    }

    pub fn abs_typed(&self, stack: impl AsRef<str>, x: impl AsRef<str>, m: Term, ty: Type) -> Term {
        Term::Abstraction(
            self.intern(stack).into(),
            self.intern(x).into(),
            Box::new(m),
            Some(ty),
        )
    }

    pub fn choice(&self, j: impl AsRef<str>) -> Term {
        Term::Choice(self.intern(j).into())
    }

    pub fn case(&self, m: Term, j: impl AsRef<str>, n: Term) -> Term {
        Term::Case(Box::new(m), self.intern(j).into(), Box::new(n))
    }

    pub fn loop_(&self, m: Term, j: impl AsRef<str>) -> Term {
        Term::Loop(Box::new(m), self.intern(j).into())
    }
}

impl Default for Storage {
    fn default() -> Self {
        Self {
            strings: RefCell::new(Interner::with_hasher(FxBuildHasher)),
        }
    }
}

pub struct WithStorage<'a, T>(&'a T, &'a Storage);

#[auto_impl(&, Box)]
pub trait DisplayWithStorage {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result;
}

impl<'a, T> Display for WithStorage<'a, T>
where
    T: DisplayWithStorage,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        let WithStorage(x, storage) = self;
        x.fmt_with_storage(f, storage)
    }
}

macro_rules! symbol_wrapper {
    ($name: ident) => {
        #[derive(Clone, Debug, PartialEq, Eq, Hash, From)]
        pub struct $name(InternedSymbol);

        impl $name {
            fn from_str(s: impl AsRef<str>, int: &mut Interner) -> Self {
                Self(int.get_or_intern(s))
            }

            fn as_str<'s>(&self, storage: &'s Storage) -> Ref<'s, str> {
                storage.resolve(self.0)
            }
        }

        impl DisplayWithStorage for $name {
            fn fmt_with_storage(
                &self,
                f: &mut Formatter<'_>,
                storage: &Storage,
            ) -> std::fmt::Result {
                write!(f, "{}", self.as_str(storage))
            }
        }
    };
}

symbol_wrapper!(Variable);
symbol_wrapper!(Choice);
symbol_wrapper!(StackIdentifier);

#[derive(Clone, Debug, PartialEq, Eq, IsVariant)]
pub enum Term {
    Variable(Variable),
    Application(StackIdentifier, Box<Term>, Box<Term>),
    Abstraction(StackIdentifier, Variable, Box<Term>, Option<Type>),
    Choice(Choice),
    Case(Box<Term>, Choice, Box<Term>),
    Loop(Box<Term>, Choice),
}

impl Term {
    /// Returns the set of variables that are named in `Self` but not bound.
    pub fn free_variables(&self) -> FxHashSet<Variable> {
        match self {
            Self::Variable(name) => std::iter::once(name).cloned().collect(),
            Self::Abstraction(_, name, body, _) => {
                let mut s = body.free_variables();
                s.remove(name);
                s
            }
            Self::Application(_, m, n) | Self::Case(m, _, n) => m
                .free_variables()
                .union(&n.free_variables())
                .cloned()
                .collect(),
            Self::Loop(m, _) => m.free_variables(),
            Self::Choice(_) => Default::default(),
        }
    }

    /// Capture-avoiding substitution `self <- {n/x}self`
    pub fn substitute(&mut self, storage: &Storage, x: &Variable, n: &Self) {
        match self {
            Self::Variable(y) => {
                if y == x {
                    *self = n.clone();
                }
            }
            Self::Abstraction(_, y, m, _) => {
                if y == x {
                    *y = x.clone();
                } else {
                    let fv_n = n.free_variables();
                    if !fv_n.contains(y) {
                        m.substitute(storage, x, n);
                    } else {
                        // Find fresh variable name.
                        let fv_m = m.free_variables();
                        let y_name = y.as_str(storage).to_string();
                        let y_dash = (0..)
                            .map(|i| Variable(storage.intern(format!("{}{}", y_name, i))))
                            .find(|name| !fv_n.contains(name) && !fv_m.contains(name))
                            .unwrap();

                        m.substitute(storage, y, &Self::Variable(y_dash.clone()));
                        *y = y_dash;
                        self.substitute(storage, x, n);
                    }
                }
            }
            Self::Application(_, m1, m2) | Self::Case(m1, _, m2) => {
                m1.substitute(storage, x, n);
                m2.substitute(storage, x, n);
            }
            Self::Loop(m, _) => m.substitute(storage, x, n),
            Self::Choice(_) => {}
        }
    }
}

impl DisplayWithStorage for Term {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        match self {
            Self::Variable(x) => WithStorage(x, storage).fmt(f),
            Self::Application(st, n, m) => write!(
                f,
                "[{}]{}. {}",
                WithStorage(n, storage),
                WithStorage(st, storage),
                WithStorage(m, storage),
            ),
            Self::Abstraction(st, x, m, ty) => write!(
                f,
                "{}<{}{}>. {}",
                WithStorage(st, storage),
                WithStorage(x, storage),
                if let Some(ty) = ty.as_ref() {
                    format!(": {}", WithStorage(ty, storage))
                } else {
                    String::new()
                },
                WithStorage(m, storage),
            ),
            Self::Choice(i) => WithStorage(i, storage).fmt(f),
            Self::Case(m, i, n) => write!(
                f,
                "{}; {} -> {}",
                WithStorage(m, storage),
                WithStorage(i, storage),
                WithStorage(n, storage)
            ),
            Self::Loop(m, i) => {
                write!(f, "{}^{}", WithStorage(m, storage), WithStorage(i, storage),)
            }
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct StackType(Vec<Type>);

impl StackType {
    fn display(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        storage: &Storage,
        reversed: bool,
    ) -> std::fmt::Result {
        let StackType(v) = self;
        if v.is_empty() {
            return f.write_str(EMPTY_STACK_SYMBOL);
        }
        if reversed {
            for (i, ty) in v.iter().rev().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                ty.fmt_with_storage(f, storage)?;
            }
        } else {
            for (i, ty) in v.iter().enumerate() {
                if i > 0 {
                    write!(f, " ")?;
                }
                ty.fmt_with_storage(f, storage)?;
            }
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct MemoryType(FxHashMap<StackIdentifier, StackType>);

impl MemoryType {
    fn singleton(stack: StackIdentifier, stack_type: StackType) -> Self {
        let mut m = FxHashMap::default();
        m.insert(stack, stack_type);
        Self(m)
    }

    fn display(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        storage: &Storage,
        reversed: bool,
    ) -> std::fmt::Result {
        let MemoryType(m) = self;
        if m.is_empty() {
            return f.write_str(EMPTY_STACK_SYMBOL);
        }
        for (i, (stack_id, stack_ty)) in m
            .iter()
            .sorted_by(|(left_name, _), (right_name, _)| {
                str::cmp(
                    storage.resolve(left_name.0).as_ref(),
                    storage.resolve(right_name.0).as_ref(),
                )
            })
            .enumerate()
        {
            if i > 0 {
                write!(f, " ")?;
            }
            write!(f, "{}(", WithStorage(stack_id, storage))?;
            stack_ty.display(f, storage, reversed)?;
            write!(f, ")")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct SumType(FxHashMap<Choice, MemoryType>);

impl SumType {
    fn singleton(choice: Choice, mem_type: MemoryType) -> Self {
        let mut m = FxHashMap::default();
        m.insert(choice, mem_type);
        Self(m)
    }

    fn plus(mut a: Self, b: Self) -> Self {
        a.0.extend(b.0.into_iter());
        a
    }

    fn display(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        storage: &Storage,
        reversed: bool,
    ) -> std::fmt::Result {
        let SumType(s) = self;
        if s.is_empty() {
            return f.write_str(EMPTY_SUM_SYMBOL);
        }
        for (i, (choice, mem_ty)) in s
            .iter()
            .sorted_by(|(left_name, _), (right_name, _)| {
                str::cmp(
                    storage.resolve(left_name.0).as_ref(),
                    storage.resolve(right_name.0).as_ref(),
                )
            })
            .enumerate()
        {
            if i > 0 {
                write!(f, " + ")?;
            }
            write!(f, "(")?;
            mem_ty.display(f, storage, reversed)?;
            write!(f, ")")?;
            write!(f, ".{}", WithStorage(choice, storage))?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct Type(MemoryType, SumType);

impl DisplayWithStorage for Type {
    fn fmt_with_storage(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        storage: &Storage,
    ) -> std::fmt::Result {
        let Type(input, output) = self;
        input.display(f, storage, false)?;
        f.write_str(" => ")?;
        output.display(f, storage, true)?;
        Ok(())
    }
}

#[derive(Clone, Debug, Default)]
pub struct TypingContext(Vec<(Variable, Type)>);

pub fn typecheck<'a>(
    term: &'a Term,
    context: &'a mut TypingContext,
    storage: &Storage,
) -> Result<Type, TypeError> {
    match term {
        Term::Variable(x) => context
            .0
            .iter()
            .rev()
            .find(|(id, _)| id == x)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| TypeError::UnboundVariable(storage.resolve(x.0).to_owned())),
        Term::Application(st, n, m) => {
            let t_n = typecheck(n, context, storage)?;
            let t_m = typecheck(m, context, storage)?;

            let Type(MemoryType(mut m), _) = t_m.clone();
            let popped = m.get_mut(st).and_then(|s| s.0.pop());
            if popped.as_ref() == Some(&t_n) {
                Ok(t_m)
            } else {
                Err(TypeError::BadApplication(
                    WithStorage(&t_m, storage).to_string(),
                    WithStorage(&t_n, storage).to_string(),
                ))
            }
        }
        Term::Abstraction(st, x, m, rho) => {
            let rho = rho
                .as_ref()
                .ok_or_else(|| TypeError::BindingMissingType(storage.resolve(x.0).to_owned()))?
                .clone();
            context.0.push((x.clone(), rho.clone()));
            let Type(mut sigma, tau) = typecheck(m, context, storage)?;
            context.0.pop();
            sigma.0.entry(st.clone()).or_default().0.push(rho);
            Ok(Type(sigma, tau))
        }
        Term::Choice(i) => Ok(Type(
            MemoryType::default(),
            SumType::singleton(i.clone(), MemoryType::default()),
        )),

        _ => todo!(),
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TypeError {
    #[error("Missing type in binding of '{_0}'.")]
    BindingMissingType(String),
    #[error("Variable '{_0}' appears unbound.")]
    UnboundVariable(String),
    #[error("Cannot apply {_0} to {_1}.")]
    BadApplication(String, String),
    #[error("{_0} is not a valid continuation after {_1}.")]
    BadCase(String, String),
}

pub trait Stack: Debug + DisplayWithStorage + DynClone {
    fn is_empty(&self) -> bool;
    fn push(&mut self, t: Term, storage: &Storage);
    fn pop(&mut self, storage: &Storage) -> Option<Term>;
}

dyn_clone::clone_trait_object!(Stack);

/// Regular stack that just stores terms. (Not a 'magic' IO stack.)
#[derive(Clone, Debug, Default)]
pub struct VecStack(Vec<Term>);

impl Stack for VecStack {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn push(&mut self, t: Term, _: &Storage) {
        self.0.push(t)
    }

    fn pop(&mut self, _: &Storage) -> Option<Term> {
        self.0.pop()
    }
}

impl DisplayWithStorage for VecStack {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        for (i, t) in self.0.iter().enumerate() {
            if i != 0 {
                f.write_str(" ")?;
            }
            WithStorage(t, storage).fmt(f)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, Display)]
pub struct InputStack;

impl Stack for InputStack {
    fn is_empty(&self) -> bool {
        false
    }

    fn push(&mut self, _: Term, _: &Storage) {}

    fn pop(&mut self, storage: &Storage) -> Option<Term> {
        let mut rl = DefaultEditor::new().unwrap();
        rl.load_history(HISTORY_PATH).ok();

        loop {
            cprintln!("<cyan>Input</>: Enter a term");
            let line = match rl.readline("> ") {
                Ok(line) => {
                    rl.add_history_entry(line.as_str()).unwrap();
                    line
                }
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    exit(1)
                }
                Err(ReadlineError::Eof) => {
                    println!("^D");
                    exit(1)
                }
                Err(err) => {
                    println!("<red>error</>: {:?}", err);
                    exit(1)
                }
            };
            rl.save_history(HISTORY_PATH).unwrap();

            return Some(match parse_term(&line, storage) {
                Ok((_, t)) => t,
                Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => {
                    cprintln!("<red>parse error</>: {}", convert_error(line.as_str(), e));
                    continue;
                }
                Err(e) => {
                    cprintln!("<red>parse error</>: {}", e);
                    continue;
                }
            });
        }
    }
}

impl DisplayWithStorage for InputStack {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        f.write_str("{magic input stack}")
    }
}

#[derive(Clone, Debug, Display)]
pub struct OutputStack;

impl Stack for OutputStack {
    fn is_empty(&self) -> bool {
        true
    }

    fn push(&mut self, t: Term, storage: &Storage) {
        cprintln!("<cyan>Output</>: <yellow>{}</>", WithStorage(&t, storage));
    }

    fn pop(&mut self, storage: &Storage) -> Option<Term> {
        None
    }
}

impl DisplayWithStorage for OutputStack {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        f.write_str("{magic output stack}")
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct Continuation(Choice, Term);

impl DisplayWithStorage for Continuation {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        let Continuation(i, n) = self;
        write!(
            f,
            "{} -> {}",
            WithStorage(i, storage),
            WithStorage(n, storage)
        )
    }
}

#[derive(Clone, Debug, Default)]
pub struct ContinuationStack(Vec<Continuation>);

impl DisplayWithStorage for ContinuationStack {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        for (i, t) in self.0.iter().enumerate() {
            if i != 0 {
                f.write_str(" ")?;
            }
            WithStorage(t, storage).fmt(f)?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug)]
struct State {
    memory: FxHashMap<StackIdentifier, Box<dyn Stack>>,
    term: Term,
    continuation_stack: ContinuationStack,
}

impl State {
    fn new(term: Term) -> Self {
        Self {
            term,
            memory: FxHashMap::default(),
            continuation_stack: ContinuationStack::default(),
        }
    }

    // "A _final_ state is of the form (S_A, i, epsilon)"
    fn is_final(&self) -> bool {
        self.term.is_choice() && self.continuation_stack.0.is_empty()
    }

    // "a _failure_ state is of the form (S_A, x, K) or (S_A, a<x>.M, K)"
    fn is_failure(&self) -> bool {
        match &self.term {
            Term::Variable(_) => true,
            Term::Abstraction(a, _, _, _) => self.memory.get(a).is_none_or(|s| s.is_empty()),
            _ => false,
        }
    }

    fn transition(mut self, storage: &Storage) -> Option<Self> {
        self.term = match self.term {
            Term::Application(a, n, m) => {
                self.memory
                    .entry(a)
                    .or_insert(Box::new(VecStack::default()))
                    .push(*n, storage);
                *m
            }
            Term::Abstraction(a, x, m, _) => {
                let Some(stack) = self.memory.get_mut(&a) else {
                    // Failure state.
                    return None;
                };
                let Some(n) = stack.pop(storage) else {
                    // Failure state.
                    return None;
                };

                let mut t = *m;
                t.substitute(storage, &x, &n);
                t
            }
            Term::Choice(i) => {
                let Some(Continuation(j, m)) = self.continuation_stack.0.pop() else {
                    // Final state.
                    return None;
                };

                if i == j {
                    m
                } else {
                    Term::Choice(i)
                }
            }
            Term::Case(n, i, m) => {
                self.continuation_stack.0.push(Continuation(i, *m));
                *n
            }
            Term::Loop(m, i) => {
                let v = m.as_ref().clone();
                self.continuation_stack
                    .0
                    .push(Continuation(i.clone(), Term::Loop(m, i)));
                v
            }
            t => t,
        };
        Some(self)
    }
}

impl DisplayWithStorage for State {
    fn fmt_with_storage(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        storage: &Storage,
    ) -> std::fmt::Result {
        write!(f, "Memory:\n")?;
        for (name, value) in self
            .memory
            .iter()
            .filter(|(_, stack)| !stack.is_empty())
            .sorted_by(|(left_name, _), (right_name, _)| {
                str::cmp(
                    storage.resolve(left_name.0).as_ref(),
                    storage.resolve(right_name.0).as_ref(),
                )
            })
        {
            write!(
                f,
                "- {} = {}\n",
                WithStorage(name, storage),
                WithStorage(value, storage)
            )?;
        }

        write!(f, "\nTerm: {}\n", WithStorage(&self.term, storage))?;

        write!(
            f,
            "Continuation Stack: {}\n",
            WithStorage(&self.continuation_stack, storage)
        )?;

        if self.is_final() {
            write!(f, "(FINAL)\n")?;
        }
        if self.is_failure() {
            write!(f, "(FAILURE)\n")?;
        }

        Ok(())
    }
}

mod args {
    use clap::Parser;

    #[derive(Parser)]
    pub struct Args {
        #[arg(default_value_t = "".into())]
        pub input: String,
    }
}

fn run_program(source: String) {
    let storage = Storage::default();

    let t = match parse_term(&source, &storage) {
        Ok((_, t)) => t,
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => {
            cprintln!("<red>Parse error</>: {}", convert_error(source.as_str(), e));
            return;
        }
        Err(e) => {
            cprintln!("<red>Parse error</>: {e}");
            return;
        }
    };
    cprintln!("<green>Parsed</>: <yellow>{}</>", WithStorage(&t, &storage));

    match typecheck(&t, &mut TypingContext::default(), &storage) {
        Ok(ty) => {
            cprintln!("<green>Type</>: <cyan>{}</>", WithStorage(&ty, &storage));
        }
        Err(e) => {
            cprintln!("<red>Type error</>: {e}");
            return;
        }
    }

    let mut state = State::new(t);
    state
        .memory
        .insert(storage.intern("input").into(), Box::new(InputStack));
    state
        .memory
        .insert(storage.intern("output").into(), Box::new(OutputStack));
    cprintln!("<dim>{}</>", WithStorage(&state, &storage));

    loop {
        if state.is_final() {
            cprintln!("<green>Success</>");
            break;
        }
        if state.is_failure() {
            cprintln!("<red>Failure</>");
            break;
        }
        state = state
            .transition(&storage)
            .expect("state should have a transition");
        println!("--------------------");
        cprintln!("<dim>{}</>", WithStorage(&state, &storage));
    }
}

const HISTORY_PATH: &'static str = ".fmc-history";

fn main() -> anyhow::Result<()> {
    let args = <args::Args as clap::Parser>::parse();

    let mut rl = DefaultEditor::new()?;
    rl.load_history(HISTORY_PATH).ok();

    if args.input.is_empty() {
        loop {
            let line = match rl.readline("> ") {
                Ok(line) => {
                    rl.add_history_entry(line.as_str())?;
                    line
                }
                Err(ReadlineError::Interrupted) => {
                    println!("^C");
                    break;
                }
                Err(ReadlineError::Eof) => {
                    println!("^D");
                    break;
                }
                Err(err) => {
                    println!("<red>error</>: {:?}", err);
                    break;
                }
            };
            rl.save_history(HISTORY_PATH)?;
            run_program(line);
        }
    } else {
        run_program(std::fs::read_to_string(&args.input)?);
    }

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_free_variables() {
        let cases = [("x", vec!["x"]), ("a<x>.x", vec![])];
        let storage = Storage::default();

        for (input, expected) in cases {
            assert_eq!(
                parse_term(input, &storage).unwrap().1.free_variables(),
                expected
                    .into_iter()
                    .map(|v| storage.intern(v).into())
                    .collect()
            );
        }
    }

    #[test]
    fn test_substitute() {
        // (M, x, N, expected) => expected == {N/x} M
        let cases = [
            ("x", "x", "y", "y"),
            ("a<x>.x", "x", "y", "a<x>.x"),
            ("a<x>.y", "y", "z", "a<x>.z"),
        ];
        let storage = Storage::default();

        for (m, x, n, expected) in cases {
            let mut t = parse_term(m, &storage).unwrap().1;
            let n = parse_term(n, &storage).unwrap().1;
            let x: Variable = storage.intern(x).into();
            t.substitute(&storage, &x, &n);
            assert_eq!(t, parse_term(expected, &storage).unwrap().1);
        }
    }
}
