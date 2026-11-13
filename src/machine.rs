use std::fmt::{Debug, Display, Formatter};
use std::process::exit;

use color_print::cprintln;
use derive_more::Display;
use dyn_clone::DynClone;
use itertools::Itertools;
use nom_language::error::convert_error;
use rustc_hash::FxHashMap;
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

use crate::parsing::parse_term;
use crate::storage::{DisplayWithStorage, Storage, WithStorage};
use crate::term::{Choice, StackIdentifier, Term};
use crate::types::{typecheck, Type, TypingContext};
use crate::HISTORY_PATH;

#[derive(Clone, Debug)]
pub struct State {
    memory: FxHashMap<StackIdentifier, Box<dyn Stack>>,
    term: Term,
    continuation_stack: ContinuationStack,
}

impl State {
    pub fn new(term: Term) -> Self {
        Self {
            term,
            memory: FxHashMap::default(),
            continuation_stack: ContinuationStack::default(),
        }
    }

    pub fn register_stack(
        &mut self,
        storage: &Storage,
        name: impl AsRef<str>,
        stack: impl Stack + 'static,
    ) {
        let id: StackIdentifier = storage.intern(name).into();
        self.memory.insert(id, Box::new(stack));
    }

    // "A _final_ state is of the form (S_A, i, epsilon)"
    pub fn is_final(&self) -> bool {
        self.term.is_choice() && self.continuation_stack.0.is_empty()
    }

    // "a _failure_ state is of the form (S_A, x, K) or (S_A, a<x>.M, K)"
    pub fn is_failure(&self) -> bool {
        match &self.term {
            Term::Variable(_) => true,
            Term::Abstraction(a, _, _, _) => self.memory.get(a).is_none_or(|s| s.is_empty()),
            _ => false,
        }
    }

    pub fn transition(mut self, storage: &Storage) -> Option<Self> {
        self.term = match self.term {
            Term::Application(a, n, m) => {
                self.memory
                    .entry(a)
                    .or_insert(Box::new(VecStack::default()))
                    .push(*n, storage);
                *m
            }
            Term::Abstraction(a, x, m, ty) => {
                let Some(stack) = self.memory.get_mut(&a) else {
                    // Failure state.
                    return None;
                };
                let Some(n) = stack.pop(storage, ty.as_ref()) else {
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

pub trait Stack: Debug + DisplayWithStorage + DynClone {
    fn is_empty(&self) -> bool;
    fn push(&mut self, t: Term, storage: &Storage);
    fn pop(&mut self, storage: &Storage, expected_type: Option<&Type>) -> Option<Term>;
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

    fn pop(&mut self, _: &Storage, _: Option<&Type>) -> Option<Term> {
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

    fn pop(&mut self, storage: &Storage, expected_ty: Option<&Type>) -> Option<Term> {
        let mut rl = DefaultEditor::new().unwrap();
        rl.load_history(HISTORY_PATH).ok();

        for i in 0.. {
            if i > 0 {
                cprintln!("(retry)");
            }
            if let Some(expected_type) = expected_ty {
                cprintln!(
                    "<blue>Input</>: Enter a term of type <cyan>{}</>",
                    WithStorage(expected_type, storage)
                );
            } else {
                cprintln!("<blue>Input</>: Enter a term");
            }
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
                Ok((_, term)) => {
                    let ty = match typecheck(&term, &mut TypingContext::default(), &storage) {
                        Ok(ty) => ty,
                        Err(e) => {
                            cprintln!("<red>Type error</>: {e}");
                            continue;
                        }
                    };
                    if let Some(expected_ty) = expected_ty && !ty.can_convert(expected_ty) {
                        cprintln!(
                            "<red>Type error</>: Can't convert {} to {}.",
                            WithStorage(&ty, storage),
                            WithStorage(expected_ty, storage)
                        );
                        continue;
                    }
                    term
                }
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
        unreachable!("previous loop never breaks")
    }
}

impl DisplayWithStorage for InputStack {
    fn fmt_with_storage(&self, f: &mut Formatter, _storage: &Storage) -> std::fmt::Result {
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
        cprintln!("<blue>Output</>: <yellow>{}</>", WithStorage(&t, storage));
    }

    fn pop(&mut self, _: &Storage, _: Option<&Type>) -> Option<Term> {
        None
    }
}

impl DisplayWithStorage for OutputStack {
    fn fmt_with_storage(&self, f: &mut Formatter, _storage: &Storage) -> std::fmt::Result {
        f.write_str("{magic output stack}")
    }
}
