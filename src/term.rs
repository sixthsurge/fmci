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

use crate::storage::{DisplayWithStorage, InternedSymbol, Storage, WithStorage};
use crate::types::Type;

macro_rules! symbol_wrapper {
    ($name: ident) => {
        #[derive(Clone, Debug, PartialEq, Eq, Hash, From)]
        pub struct $name(pub InternedSymbol);

        impl $name {
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parsing::parse_term;

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
