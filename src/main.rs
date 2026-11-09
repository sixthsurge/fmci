use std::fmt::{Debug, Display};
use std::process::exit;

use color_print::cprintln;
use derive_more::{Display, IsVariant};
use dyn_clone::DynClone;
use itertools::Itertools;
use nom::Parser;
use nom::branch::alt;
use nom::bytes::complete::{is_not, tag, take_until};
use nom::character::complete::multispace1;
use nom::combinator::{all_consuming, opt, success, value, verify};
use nom::error::context;
use nom::multi::many0;
use nom::sequence::{preceded, terminated};
use nom::{
    IResult,
    character::complete::{alphanumeric1, char},
    combinator::map,
    sequence::delimited,
};
use nom_language::error::convert_error;
use nom_language::precedence::left_assoc;
use rustc_hash::{FxHashMap, FxHashSet};
use rustyline::DefaultEditor;
use rustyline::error::ReadlineError;

const DEFAULT_STACK_NAME: &'static str = "Lambda";

#[derive(Clone, Debug, Display, PartialEq, Eq)]
enum BaseType {
    #[display("Unit")]
    Unit,
}

#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct Type(FxHashMap<String, (Vec<BaseType>, Vec<BaseType>)>);

impl Type {
    fn get(desc: &[(&str, &[BaseType], &[BaseType])]) -> Self {
        let mut ty = Self::default();
        for (stack, pushed, popped) in desc.iter().copied() {
            ty.0.insert(stack.to_owned(), (pushed.to_owned(), popped.to_owned()));
        }
        ty
    }
}

impl Display for Type {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut right_names = vec![];
        for (stack, (left, right)) in self
            .0
            .iter()
            .sorted_by(|(left_name, _), (right_name, _)| String::cmp(left_name, right_name))
        {
            for popped in left.iter() {
                write!(f, "{stack}({popped}) ")?;
            }
            for pushed in right.iter() {
                right_names.push((stack, pushed));
            }
        }
        write!(f, "=>")?;
        for (stack, pushed) in right_names {
            write!(f, " {stack}({pushed})")?;
        }

        Ok(())
    }
}

#[derive(Clone, Debug, Display, PartialEq, Eq, IsVariant)]
enum Term {
    #[display("{_0}")]
    Variable(String),
    #[display("([{_1}]{_0}. {_2})")]
    Application(String, Box<Term>, Box<Term>),
    #[display("({}<{}{}>. {})", _0, _1, if let Some(ty) = _3 {format!(": {ty}")} else {String::new()}, _2)]
    Abstraction(String, String, Box<Term>, Option<Type>),
    #[display("\'{_0}")]
    Choice(String),
    #[display("({_0}; {_1} -> {_2})")]
    Case(Box<Term>, String, Box<Term>),
    #[display("{_0}^{_1}")]
    Loop(Box<Term>, String),
}

impl Term {
    fn var(name: impl Into<String>) -> Self {
        Self::Variable(name.into())
    }

    fn app(stack: impl Into<String>, n: Self, m: Self) -> Self {
        Self::Application(stack.into(), Box::new(n), Box::new(m))
    }

    fn abs(stack: impl Into<String>, x: impl Into<String>, m: Self, ty: Option<Type>) -> Self {
        Self::Abstraction(stack.into(), x.into(), Box::new(m), ty)
    }

    fn abs_untyped(stack: impl Into<String>, x: impl Into<String>, m: Self) -> Self {
        Self::Abstraction(stack.into(), x.into(), Box::new(m), None)
    }

    fn abs_typed(stack: impl Into<String>, x: impl Into<String>, m: Self, ty: Type) -> Self {
        Self::Abstraction(stack.into(), x.into(), Box::new(m), Some(ty))
    }

    fn choice(j: impl Into<String>) -> Self {
        Self::Choice(j.into())
    }

    fn case(m: Self, j: impl Into<String>, n: Self) -> Self {
        Self::Case(Box::new(m), j.into(), Box::new(n))
    }

    fn loop_(m: Self, j: impl Into<String>) -> Self {
        Self::Loop(Box::new(m), j.into())
    }

    /// Returns the set of variables that are named in `self` but not bound.
    fn free_variables(&self) -> FxHashSet<String> {
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
    fn substitute(&mut self, x: &str, n: &Term) {
        match self {
            Self::Variable(y) => {
                if y == x {
                    *self = n.clone();
                }
            }
            Self::Abstraction(_, y, m, _) => {
                if y == x {
                    *y = x.into();
                } else {
                    let fv_n = n.free_variables();
                    if !fv_n.contains(y) {
                        m.substitute(x, n);
                    } else {
                        // Find fresh variable name.
                        let fv_m = m.free_variables();
                        let y_dash = (0..)
                            .map(|i| format!("{}{}", y.as_str(), i))
                            .find(|name| !fv_n.contains(name) && !fv_m.contains(name))
                            .unwrap();

                        m.substitute(y, &Self::Variable(y_dash.clone()));
                        *y = y_dash;
                        self.substitute(x, n);
                    }
                }
            }
            Self::Application(_, m1, m2) | Self::Case(m1, _, m2) => {
                m1.substitute(x, n);
                m2.substitute(x, n);
            }
            Self::Loop(m, _) => m.substitute(x, n),
            Self::Choice(_) => {}
        }
    }
}

trait Stack: Debug + Display + DynClone {
    fn is_empty(&self) -> bool;
    fn push(&mut self, t: Term);
    fn pop(&mut self) -> Option<Term>;
}

dyn_clone::clone_trait_object!(Stack);

/// Regular stack that just stores terms. (Not a 'magic' IO stack.)
#[derive(Clone, Debug, Display, Default)]
#[display("{}", DisplayVec(&_0))]
struct VecStack(Vec<Term>);

impl Stack for VecStack {
    fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    fn push(&mut self, t: Term) {
        self.0.push(t)
    }

    fn pop(&mut self) -> Option<Term> {
        self.0.pop()
    }
}

#[derive(Clone, Debug, Display)]
#[display("{{magic input stack}}")]
struct InputStack;

impl Stack for InputStack {
    fn is_empty(&self) -> bool {
        false
    }

    fn push(&mut self, _: Term) {}

    fn pop(&mut self) -> Option<Term> {
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

            return Some(match all_consuming(parse_term).parse(&line) {
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

#[derive(Clone, Debug, Display)]
#[display("{{magic output stack}}")]
struct OutputStack;

impl Stack for OutputStack {
    fn is_empty(&self) -> bool {
        true
    }

    fn push(&mut self, t: Term) {
        cprintln!("<cyan>Output</>: <yellow>{t}</>");
    }

    fn pop(&mut self) -> Option<Term> {
        None
    }
}

#[derive(Clone, Debug, Display, PartialEq, Eq)]
#[display("{_0} -> {_1}")]
struct Continuation(String, Term);

#[derive(Clone, Debug)]
struct State {
    memory: FxHashMap<String, Box<dyn Stack>>,
    term: Term,
    continuation_stack: Vec<Continuation>,
}

impl State {
    fn new(term: Term) -> Self {
        Self {
            term,
            memory: FxHashMap::default(),
            continuation_stack: Vec::default(),
        }
    }

    // "A _final_ state is of the form (S_A, i, epsilon)"
    fn is_final(&self) -> bool {
        self.term.is_choice() && self.continuation_stack.is_empty()
    }

    // "a _failure_ state is of the form (S_A, x, K) or (S_A, a<x>.M, K)"
    fn is_failure(&self) -> bool {
        match &self.term {
            Term::Variable(_) => true,
            Term::Abstraction(a, _, _, _) => self.memory.get(a).is_none_or(|s| s.is_empty()),
            _ => false,
        }
    }

    fn transition(mut self) -> Option<Self> {
        self.term = match self.term {
            Term::Application(a, n, m) => {
                self.memory
                    .entry(a)
                    .or_insert(Box::new(VecStack::default()))
                    .push(*n);
                *m
            }
            Term::Abstraction(a, x, m, _) => {
                let Some(stack) = self.memory.get_mut(&a) else {
                    // Failure state.
                    return None;
                };
                let Some(n) = stack.pop() else {
                    // Failure state.
                    return None;
                };

                let mut t = *m;
                t.substitute(&x, &n);
                t
            }
            Term::Choice(i) => {
                let Some(Continuation(j, m)) = self.continuation_stack.pop() else {
                    // Final state.
                    return None;
                };

                if i == j { m } else { Term::Choice(i) }
            }
            Term::Case(n, i, m) => {
                self.continuation_stack.push(Continuation(i, *m));
                *n
            }
            Term::Loop(m, i) => {
                let v = m.as_ref().clone();
                self.continuation_stack
                    .push(Continuation(i.clone(), Term::Loop(m, i)));
                v
            }
            t => t,
        };
        Some(self)
    }
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Memory:\n")?;
        for (name, value) in self
            .memory
            .iter()
            .filter(|(_, stack)| !stack.is_empty())
            .sorted_by(|(left_name, _), (right_name, _)| String::cmp(left_name, right_name))
        {
            write!(f, "- {} = {}\n", name, value)?;
        }

        write!(f, "\nTerm: {}\n", self.term)?;

        write!(
            f,
            "Continuation Stack: {}\n",
            DisplayVec(&self.continuation_stack)
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

fn parse_term<'a>(
    s: &'a str,
) -> IResult<&'a str, Term, nom_language::error::VerboseError<&'a str>> {
    type E<'a> = nom_language::error::VerboseError<&'a str>;

    const RESERVED_WORDS: &[&'static str] = &["let", "in"];

    fn ignored<'a>() -> impl Parser<&'a str, Output = (), Error = E<'a>> {
        let line_comment = value((), (tag("//"), many0(is_not("\n\r"))));
        let inline_comment = value((), (tag("/*"), take_until("*/"), tag("*/")));
        value(
            (),
            many0(alt((value((), multispace1), line_comment, inline_comment))),
        )
    }

    fn sep<'a, F, O>(inner: F) -> impl Parser<&'a str, Output = O, Error = E<'a>>
    where
        F: Parser<&'a str, Output = O, Error = E<'a>>,
    {
        delimited(ignored(), inner, ignored())
    }

    fn base_ty<'a>() -> impl Parser<&'a str, Output = BaseType, Error = E<'a>> {
        context("base type", value(BaseType::Unit, sep(tag("Unit"))))
    }
    fn typevec_entry<'a>() -> impl Parser<&'a str, Output = (&'a str, BaseType), Error = E<'a>> {
        context(
            "type vec entry",
            sep(alt((
                map(base_ty(), |ty| (DEFAULT_STACK_NAME, ty)),
                (alphanumeric1, delimited(char('('), base_ty(), char(')'))),
            ))),
        )
    }
    fn ty<'a>() -> impl Parser<&'a str, Output = Type, Error = E<'a>> {
        context(
            "type",
            map(
                (
                    many0(sep(typevec_entry())),
                    preceded(tag("=>"), many0(sep(typevec_entry()))),
                ),
                |(popped, pushed)| {
                    let mut ty = Type::default();
                    for (stack, base_ty) in popped {
                        ty.0.entry(stack.into())
                            .or_insert(Default::default())
                            .0
                            .push(base_ty);
                    }
                    for (stack, base_ty) in pushed {
                        ty.0.entry(stack.into())
                            .or_insert(Default::default())
                            .1
                            .push(base_ty);
                    }
                    ty
                },
            ),
        )
    }
    fn var<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "var",
            map(
                sep(verify(alphanumeric1, |w: &str| {
                    !RESERVED_WORDS.iter().contains(&w)
                })),
                |s| Term::Variable(s.into()),
            ),
        )
    }
    fn app<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "app",
            map(
                (
                    delimited(char('['), sep(parse_term), char(']')),
                    opt(sep(alphanumeric1)),
                    preceded(char('.'), sep(parse_term)),
                ),
                |(n, stack, m)| {
                    Term::Application(
                        stack.unwrap_or(DEFAULT_STACK_NAME).into(),
                        Box::new(n),
                        Box::new(m),
                    )
                },
            ),
        )
    }
    fn abs<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "abs",
            map(
                (
                    opt(sep(alphanumeric1)),
                    delimited(
                        sep(char('<')),
                        (sep(alphanumeric1), opt(preceded(char(':'), sep(ty())))),
                        sep(char('>')),
                    ),
                    preceded(sep(char('.')), sep(parse_term)),
                ),
                |(stack, (x, ty), m)| Term::abs(stack.unwrap_or(DEFAULT_STACK_NAME), x, m, ty),
            ),
        )
    }
    fn paren<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "paren",
            delimited(sep(char('(')), parse_term, sep(char(')'))),
        )
    }
    fn choice<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "choice",
            map(
                sep(preceded(char('\''), alt((tag("*"), alphanumeric1)))),
                |s| Term::Choice(s.into()),
            ),
        )
    }
    fn let_in<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "let-in",
            map(
                // let x = n in m
                (
                    preceded(sep(tag("let")), alphanumeric1),
                    preceded(sep(char('=')), parse_term),
                    preceded(sep(tag("in")), parse_term),
                ),
                |(x, n, m)| {
                    Term::app(
                        DEFAULT_STACK_NAME,
                        n,
                        Term::abs_untyped(DEFAULT_STACK_NAME, x, m),
                    )
                },
            ),
        )
    }
    fn atom<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "atom",
            alt((app(), abs(), var(), choice(), paren(), let_in())),
        )
    }
    fn jux<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        // m n as sugar for [n]Lambda.m
        context(
            "jux",
            left_assoc(atom(), success(()), |m, _, n| {
                Term::app(DEFAULT_STACK_NAME, n, m)
            }),
        )
    }
    fn case<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "case",
            left_assoc(
                sep(jux()),
                preceded(
                    char(';'),
                    opt(terminated(sep(alphanumeric1), sep(tag("->")))),
                ),
                |m, j, n| Term::case(m, j.unwrap_or("*"), n),
            ),
        )
    }
    fn loop_<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "loop",
            map(
                (
                    sep(jux()),
                    sep(char('^')),
                    sep(alt((alphanumeric1, tag("*")))),
                ),
                |(m, _, j)| Term::Loop(Box::new(m), j.into()),
            ),
        )
    }

    context("term", alt((loop_(), case(), jux(), atom()))).parse(s)
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
    let t = match all_consuming(parse_term).parse(&source) {
        Ok((_, t)) => t,
        Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => {
            cprintln!("<red>parse error</>: {}", convert_error(source.as_str(), e));
            return;
        }
        Err(e) => {
            cprintln!("<red>parse error</>: {}", e);
            return;
        }
    };
    cprintln!("<green>parsed</>: <yellow>{t}</>");

    let mut state = State::new(t);
    state.memory.insert("input".into(), Box::new(InputStack));
    state.memory.insert("output".into(), Box::new(OutputStack));
    println!("{state}");

    loop {
        if state.is_final() {
            cprintln!("<green>Success</>");
            break;
        }
        if state.is_failure() {
            cprintln!("<yellow>Failure</>");
            break;
        }
        state = state.transition().expect("state should have a transition");
        println!("--------------------");
        cprintln!("<dim>{state}</>");
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

struct DisplayVec<'a, T>(&'a Vec<T>)
where
    T: Display;

impl<'a, T> Display for DisplayVec<'a, T>
where
    T: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (i, x) in self.0.iter().enumerate() {
            write!(f, "{}{}", if i == 0 { "" } else { ", " }, x)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_term() {
        let var = Term::var;
        let app = Term::app;
        let abs = Term::abs_untyped;
        let choice = Term::choice;
        let case = Term::case;
        let loop_ = Term::loop_;

        let cases = [
            ("x", Some(var("x"))),
            (" x ", Some(var("x"))),
            ("[N]a.M", Some(app("a", var("N"), var("M")))),
            ("([N]a.M)", Some(app("a", var("N"), var("M")))),
            ("[ N ] a . M", Some(app("a", var("N"), var("M")))),
            ("[N].M", Some(app(DEFAULT_STACK_NAME, var("N"), var("M")))),
            ("a<x>.M", Some(abs("a", "x", var("M")))),
            ("<x>.M", Some(abs(DEFAULT_STACK_NAME, "x", var("M")))),
            ("a < x > . M", Some(abs("a", "x", var("M")))),
            ("'j", Some(choice("j"))),
            ("' j", None),
            ("M;j->N", Some(case(var("M"), "j", var("N")))),
            // left-associativity of ;
            (
                "M;i->N;j->K",
                Some(case(case(var("M"), "i", var("N")), "j", var("K"))),
            ),
            (
                "M; i -> N; j -> K",
                Some(case(case(var("M"), "i", var("N")), "j", var("K"))),
            ),
            ("M ; j -> N", Some(case(var("M"), "j", var("N")))),
            ("M^j", Some(loop_(var("M"), "j"))),
            ("M ^ j", Some(loop_(var("M"), "j"))),
            ("let", None),
            ("in", None),
            (
                "let x = y in z",
                Some(app(
                    DEFAULT_STACK_NAME,
                    var("y"),
                    abs(DEFAULT_STACK_NAME, "x", var("z")),
                )),
            ),
            // application by juxtaposition
            (
                "a b c",
                Some(app(
                    DEFAULT_STACK_NAME,
                    var("c"),
                    app(DEFAULT_STACK_NAME, var("b"), var("a")),
                )),
            ),
            // comments
            ("a // line comment", Some(var("a"))),
            ("a// line comment", Some(var("a"))),
            ("a //", Some(var("a"))),
            ("// line comment\na", Some(var("a"))),
            ("//\na", Some(var("a"))),
            ("/* inline comment */ a", Some(var("a"))),
            // types
            (
                "<x: a(Unit) => a(Unit) b(Unit)>.x",
                Some(Term::abs_typed(
                    DEFAULT_STACK_NAME,
                    "x",
                    var("x"),
                    Type::get(&[
                        ("a", &[BaseType::Unit], &[BaseType::Unit]),
                        ("b", &[], &[BaseType::Unit]),
                    ]),
                )),
            ),
            (
                "<x: Unit => a(Unit) b(Unit)>.x",
                Some(Term::abs_typed(
                    DEFAULT_STACK_NAME,
                    "x",
                    var("x"),
                    Type::get(&[
                        (DEFAULT_STACK_NAME, &[BaseType::Unit], &[]),
                        ("a", &[], &[BaseType::Unit]),
                        ("b", &[], &[BaseType::Unit]),
                    ]),
                )),
            ),
        ];

        for (i, (input, expected)) in cases.into_iter().enumerate() {
            assert_eq!(parse_term(input).ok().map(|(_, t)| t), expected, "case {i}");
        }
    }

    #[test]
    fn test_free_variables() {
        let cases = [("x", vec!["x"]), ("a<x>.x", vec![])];

        for (input, expected) in cases {
            assert_eq!(
                parse_term(input).unwrap().1.free_variables(),
                expected.into_iter().map(str::to_string).collect()
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

        for (m, x, n, expected) in cases {
            let mut t = parse_term(m).unwrap().1;
            let n = parse_term(n).unwrap().1;
            t.substitute(x, &n);
            assert_eq!(t, parse_term(expected).unwrap().1);
        }
    }
}
