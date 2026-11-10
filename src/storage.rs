use std::cell::{Ref, RefCell};
use std::fmt::{Debug, Display, Formatter};

use auto_impl::auto_impl;
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

use crate::{term::Term, types::Type};

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

pub struct WithStorage<'a, T>(pub &'a T, pub &'a Storage);

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
