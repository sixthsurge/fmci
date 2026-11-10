use std::collections::HashMap;

use itertools::Itertools;
use nom::branch::alt;
use nom::bytes::complete::{is_not, tag, take_until};
use nom::character::complete::multispace1;
use nom::combinator::{all_consuming, cut, opt, success, value, verify};
use nom::error::context;
use nom::multi::{many0, many1};
use nom::sequence::{preceded, terminated};
use nom::Parser;
use nom::{
    character::complete::{alphanumeric1, char},
    combinator::map,
    sequence::delimited,
    IResult,
};
use nom_language::precedence::left_assoc;
use rustc_hash::FxHashMap;

use crate::{
    storage::Storage,
    term::{StackIdentifier, Term},
    types::{MemoryType, StackType, SumType, Type},
    DEFAULT_STACK_ID, EMPTY_STACK_SYMBOL, EMPTY_SUM_SYMBOL,
};

/// Words that may not appear in identifiers.
const RESERVED_WORDS: &[&'static str] = &["let", "in"];

type ParseErr<'a> = nom_language::error::VerboseError<&'a str>;

fn ignored<'a>() -> impl Parser<&'a str, Output = (), Error = ParseErr<'a>> {
    let line_comment = value((), (tag("//"), many0(is_not("\n\r"))));
    let inline_comment = value((), (tag("/*"), take_until("*/"), tag("*/")));
    value(
        (),
        many0(alt((value((), multispace1), line_comment, inline_comment))),
    )
}

fn sep<'a, F, O>(inner: F) -> impl Parser<&'a str, Output = O, Error = ParseErr<'a>>
where
    F: Parser<&'a str, Output = O, Error = ParseErr<'a>>,
{
    delimited(ignored(), inner, ignored())
}

// Choices start with a digit or uppercase letter.
fn choice_name<'a>() -> impl Parser<&'a str, Output = &'a str, Error = ParseErr<'a>> {
    context(
        "choice name",
        alt((
            sep(tag("*")),
            verify(sep(alphanumeric1), |w: &str| {
                let c = w.chars().next().expect("should not be empty");
                (c.is_digit(10) || c.is_uppercase()) && !RESERVED_WORDS.iter().contains(&w)
            }),
        )),
    )
}

// Variables start with a lowercase letter.
fn var_name<'a>() -> impl Parser<&'a str, Output = &'a str, Error = ParseErr<'a>> {
    context(
        "var name",
        verify(sep(alphanumeric1), |w: &str| {
            let c = w.chars().next().expect("should not be empty");
            (c.is_lowercase()) && !RESERVED_WORDS.iter().contains(&w)
        }),
    )
}

fn term<'a>(s: &'a str, storage: &Storage) -> IResult<&'a str, Term, ParseErr<'a>> {
    let subterm = |s| term(s, storage);
    let ty = |s| ty(s, storage);
    let var = || context("var", map(var_name(), |s| storage.var(s)));
    let app = || {
        context(
            "app",
            map(
                (
                    delimited(char('['), sep(subterm), char(']')),
                    opt(sep(alphanumeric1)),
                    preceded(char('.'), sep(subterm)),
                ),
                |(n, stack, m)| storage.app(stack.unwrap_or(DEFAULT_STACK_ID), n, m),
            ),
        )
    };
    let abs = || {
        context(
            "abs",
            map(
                (
                    opt(sep(alphanumeric1)),
                    delimited(
                        sep(char('<')),
                        (var_name(), opt(preceded(char(':'), sep(ty)))),
                        sep(char('>')),
                    ),
                    preceded(sep(char('.')), sep(subterm)),
                ),
                |(stack, (x, ty), m)| storage.abs(stack.unwrap_or(DEFAULT_STACK_ID), x, m, ty),
            ),
        )
    };
    let paren = || context("paren", delimited(sep(char('(')), subterm, sep(char(')'))));
    let choice = || context("choice", map(choice_name(), |s| storage.choice(s)));
    let let_in = || {
        context(
            "let-in",
            map(
                // let x = n in m
                (
                    preceded(sep(tag("let")), var_name()),
                    cut((
                        opt(preceded(sep(char(':')), ty)),
                        preceded(sep(char('=')), subterm),
                        preceded(sep(tag("in")), subterm),
                    )),
                ),
                |(x, (ty, n, m))| {
                    storage.app(DEFAULT_STACK_ID, n, storage.abs(DEFAULT_STACK_ID, x, m, ty))
                },
            ),
        )
    };
    let atom = || {
        context(
            "atom",
            alt((app(), abs(), var(), choice(), paren(), let_in())),
        )
    };
    // m n as sugar for [n]Lambda.m
    let jux = || {
        context(
            "jux",
            left_assoc(atom(), success(()), |m, _, n| {
                storage.app(DEFAULT_STACK_ID, n, m)
            }),
        )
    };
    let case = || {
        context(
            "case",
            left_assoc(
                sep(jux()),
                preceded(char(';'), opt(terminated(choice_name(), sep(tag("->"))))),
                |m, j, n| storage.case(m, j.unwrap_or("*"), n),
            ),
        )
    };
    let loop_ = || {
        context(
            "loop",
            map((sep(jux()), sep(char('^')), choice_name()), |(m, _, j)| {
                storage.loop_(m, j)
            }),
        )
    };

    context("term", alt((loop_(), case(), jux(), atom()))).parse(s)
}

fn ty<'a>(
    s: &'a str,
    storage: &Storage,
) -> IResult<&'a str, Type, nom_language::error::VerboseError<&'a str>> {
    let subty = |s| ty(s, storage);
    let singleton = || {
        context(
            "singleton",
            (
                sep(alphanumeric1),
                delimited(sep(char('(')), subty, sep(char(')'))),
            ),
        )
    };

    let mem_ty = |rev: bool| {
        context(
            "memory type",
            alt((
                sep(value(MemoryType::default(), tag(EMPTY_STACK_SYMBOL))),
                map(many1(singleton()), move |mut v| {
                    if rev {
                        v.reverse();
                    }
                    let mut m = FxHashMap::<StackIdentifier, StackType>::default();
                    for (s, v) in v {
                        m.entry(storage.intern(s).into()).or_default().0.push(v);
                    }
                    MemoryType(m)
                }),
            )),
        )
    };

    let sum_ty = || {
        context(
            "sum type",
            alt((
                value(SumType::default(), sep(tag(EMPTY_SUM_SYMBOL))),
                left_assoc(
                    map(
                        (sep(mem_ty(false)), preceded(char('.'), sep(choice_name()))),
                        |(ty, choice)| SumType::singleton(storage.intern(choice).into(), ty),
                    ),
                    sep(char('+')),
                    |l, _, r| SumType::plus(l, r),
                ),
            )),
        )
    };

    context(
        "type",
        map(
            (sep(mem_ty(true)), preceded(sep(tag("=>")), sep(sum_ty()))),
            |(input, output)| Type(input, output),
        ),
    )
    .parse(s)
}

pub fn parse_term<'a>(
    s: &'a str,
    storage: &Storage,
) -> IResult<&'a str, Term, nom_language::error::VerboseError<&'a str>> {
    all_consuming(|s| term(s, storage)).parse(s)
}

pub fn parse_type<'a>(
    s: &'a str,
    storage: &Storage,
) -> IResult<&'a str, Type, nom_language::error::VerboseError<&'a str>> {
    all_consuming(|s| ty(s, storage)).parse(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_term() {
        let mut s = Storage::default();

        let cases = [
            ("x", Some(s.var("x"))),
            (" x ", Some(s.var("x"))),
            ("[n]a.m", Some(s.app("a", s.var("n"), s.var("m")))),
            ("([n]a.m)", Some(s.app("a", s.var("n"), s.var("m")))),
            ("[ n ] a . m", Some(s.app("a", s.var("n"), s.var("m")))),
            (
                "[n].m",
                Some(s.app(DEFAULT_STACK_ID, s.var("n"), s.var("m"))),
            ),
            ("a<x>.m", Some(s.abs_untyped("a", "x", s.var("m")))),
            (
                "<x>.m",
                Some(s.abs_untyped(DEFAULT_STACK_ID, "x", s.var("m"))),
            ),
            ("a < x > . m", Some(s.abs_untyped("a", "x", s.var("m")))),
            ("J", Some(s.choice("J"))),
            ("m;J->n", Some(s.case(s.var("m"), "J", s.var("n")))),
            // left-associativity of ;
            (
                "m;I->n;J->k",
                Some(s.case(s.case(s.var("m"), "I", s.var("n")), "J", s.var("k"))),
            ),
            (
                "m; I -> n; J -> k",
                Some(s.case(s.case(s.var("m"), "I", s.var("n")), "J", s.var("k"))),
            ),
            ("m ; J -> n", Some(s.case(s.var("m"), "J", s.var("n")))),
            ("m^J", Some(s.loop_(s.var("m"), "J"))),
            ("m ^ J", Some(s.loop_(s.var("m"), "J"))),
            ("let", None),
            ("in", None),
            (
                "let x = y in z",
                Some(s.app(
                    DEFAULT_STACK_ID,
                    s.var("y"),
                    s.abs_untyped(DEFAULT_STACK_ID, "x", s.var("z")),
                )),
            ),
            // application by juxtaposition
            (
                "a b c",
                Some(s.app(
                    DEFAULT_STACK_ID,
                    s.var("c"),
                    s.app(DEFAULT_STACK_ID, s.var("b"), s.var("a")),
                )),
            ),
            // comments
            ("a // line comment", Some(s.var("a"))),
            ("a// line comment", Some(s.var("a"))),
            ("a //", Some(s.var("a"))),
            ("// line comment\na", Some(s.var("a"))),
            ("//\na", Some(s.var("a"))),
            ("/* inline comment */ a", Some(s.var("a"))),
        ];

        for (i, (input, expected)) in cases.into_iter().enumerate() {
            assert_eq!(
                parse_term(input, &mut s).ok().map(|(_, t)| t),
                expected,
                "case {i}"
            );
        }
    }
}
