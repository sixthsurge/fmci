use std::fmt::{Debug, Display};
use std::sync::Arc;

use color_print::cprintln;
use derive_more::{Display, IsVariant};
use itertools::Itertools;
use nom::branch::alt;
use nom::bytes::complete::tag;
use nom::combinator::all_consuming;
use nom::error::context;
use nom::sequence::preceded;
use nom::Parser;
use nom::{
    character::complete::{alphanumeric1, char, multispace0},
    combinator::map,
    error::ParseError,
    sequence::delimited,
    IResult,
};
use nom_language::error::convert_error;
use rustc_hash::{FxHashMap, FxHashSet};
use rustyline::error::ReadlineError;
use rustyline::DefaultEditor;

#[derive(Clone, Debug, Display, PartialEq, Eq, IsVariant)]
enum Term {
    #[display("{_0}")]
    Variable(String),
    #[display("([{_1}]{_0}. {_2})")]
    Application(String, Box<Term>, Box<Term>),
    #[display("({_0}<{_1}>. {_2})")]
    Abstraction(String, String, Box<Term>),
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

    fn abs(stack: impl Into<String>, x: impl Into<String>, m: Self) -> Self {
        Self::Abstraction(stack.into(), x.into(), Box::new(m))
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
            Self::Abstraction(_, name, body) => {
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
            Self::Abstraction(_, y, m) => {
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

trait Stack: Debug + Display {
    fn is_empty(&self) -> bool;
    fn push(&mut self, t: Term);
    fn pop(&mut self) -> Option<Term>;
}

/// Regular stack that just stores terms. (Not a 'magic' IO stack.)
#[derive(Debug, Display, Default)]
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

#[derive(Clone, Debug, Display, PartialEq, Eq)]
#[display("{_0} -> {_1}")]
struct Continuation(String, Term);

#[derive(Debug)]
struct State {
    memory: FxHashMap<String, Box<dyn Stack>>,
    term: Term,
    continuation_stack: Vec<Continuation>,
}

impl State {
    // "A _final_ state is of the form (S_A, i, epsilon)"
    fn is_final(&self) -> bool {
        self.term.is_choice() && self.continuation_stack.is_empty()
    }

    // "a _failure_ state is of the form (S_A, x, K) or (S_A, a<x>.M, K)"
    fn is_failure(&self) -> bool {
        match &self.term {
            Term::Variable(_) => true,
            Term::Abstraction(a, _, _) => self.memory.get(a).is_none_or(|s| s.is_empty()),
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
            Term::Abstraction(a, x, m) => {
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
                let Some(Continuation(j, M)) = self.continuation_stack.pop() else {
                    // Final state.
                    return None;
                };

                if i == j {
                    M
                } else {
                    Term::Choice(i)
                }
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
        write!(f, "Memory:")?;
        for (name, value) in self
            .memory
            .iter()
            .filter(|(_, stack)| !stack.is_empty())
            .sorted_by(|(left_name, _), (right_name, _)| String::cmp(left_name, right_name))
        {
            write!(f, " {}({})", name, value)?;
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
    fn ws<'a, O, E: ParseError<&'a str>, F>(inner: F) -> impl Parser<&'a str, Output = O, Error = E>
    where
        F: Parser<&'a str, Output = O, Error = E>,
    {
        delimited(multispace0, inner, multispace0)
    }

    type E<'a> = nom_language::error::VerboseError<&'a str>;

    fn var<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context("var", map(ws(alphanumeric1), |s| Term::Variable(s.into())))
    }
    fn app<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "app",
            map(
                (
                    delimited(char('['), ws(parse_term), char(']')),
                    ws(alphanumeric1),
                    preceded(char('.'), ws(parse_term)),
                ),
                |(n, stack, m)| Term::Application(stack.into(), Box::new(n), Box::new(m)),
            ),
        )
    }
    fn abs<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "abs",
            map(
                (
                    ws(alphanumeric1),
                    delimited(ws(char('<')), ws(alphanumeric1), ws(char('>'))),
                    preceded(ws(char('.')), ws(parse_term)),
                ),
                |(stack, x, m)| Term::Abstraction(stack.into(), x.into(), m.into()),
            ),
        )
    }
    fn paren<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context("paren", delimited(ws(char('(')), parse_term, ws(char(')'))))
    }
    fn choice<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "choice",
            map(ws(preceded(char('\''), alphanumeric1)), |s| {
                Term::Choice(s.into())
            }),
        )
    }
    fn atom<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context("atom", alt((app(), abs(), var(), choice(), paren())))
    }
    fn case<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "case",
            map(
                (
                    ws(atom()),
                    delimited(ws(char(';')), alphanumeric1, ws(tag("->"))),
                    ws(parse_term),
                ),
                |(n, j, m)| Term::Case(Box::new(n), j.into(), Box::new(m)),
            ),
        )
    }
    fn loop_<'a>() -> impl Parser<&'a str, Output = Term, Error = E<'a>> {
        context(
            "loop",
            map(
                (ws(atom()), ws(char('^')), ws(alphanumeric1)),
                |(m, _, j)| Term::Loop(Box::new(m), j.into()),
            ),
        )
    }

    context("term", alt((case(), loop_(), atom()))).parse(s)
}

fn main() -> anyhow::Result<()> {
    const HISTORY_PATH: &'static str = ".fmc-history";
    let mut rl = DefaultEditor::new()?;
    rl.load_history(HISTORY_PATH).ok();

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

        let t = match all_consuming(parse_term).parse(&line) {
            Ok((_, t)) => t,
            Err(nom::Err::Error(e)) | Err(nom::Err::Failure(e)) => {
                cprintln!("<red>parse error</>: {}", convert_error(line.as_str(), e));
                continue;
            }
            Err(e) => {
                cprintln!("<red>parse error</>: {}", e);
                continue;
            }
        };
        println!("{t}");

        let mut state = State {
            memory: FxHashMap::default(),
            term: t,
            continuation_stack: vec![],
        };
        println!("{state}");

        loop {
            if state.is_final() {
                let Term::Choice(final_choice) = state.term else {
                    panic!();
                };
                cprintln!("<green>success</>: terminated with choice <cyan>{final_choice}</>");
                break;
            }
            if state.is_failure() {
                cprintln!(
                    "<yellow>failure</>: machine terminated with irreducible term <cyan>{}</>",
                    state.term
                );
                break;
            }
            state = state.transition().expect("state should have a transition");
            println!("{state}");
        }
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
        let abs = Term::abs;
        let choice = Term::choice;
        let case = Term::case;
        let loop_ = Term::loop_;

        let cases = [
            ("x", Some(var("x"))),
            (" x ", Some(var("x"))),
            ("[N]a.M", Some(app("a", var("N"), var("M")))),
            ("([N]a.M)", Some(app("a", var("N"), var("M")))),
            ("[ N ] a . M", Some(app("a", var("N"), var("M")))),
            ("a<x>.M", Some(abs("a", "x", var("M")))),
            ("a < x > . M", Some(abs("a", "x", var("M")))),
            ("'j", Some(choice("j"))),
            ("' j", None),
            ("M;j->N", Some(case(var("M"), "j", var("N")))),
            ("M ; j -> N", Some(case(var("M"), "j", var("N")))),
            ("M^j", Some(loop_(var("M"), "j"))),
            ("M ^ j", Some(loop_(var("M"), "j"))),
        ];

        for (input, expected) in cases {
            assert_eq!(parse_term(input).ok().map(|(_, t)| t), expected);
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
