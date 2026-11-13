use std::cell::{Ref, RefCell};
use std::fmt::{Display, Formatter};

use auto_impl::auto_impl;
use nom_locate::LocatedSpan;
use rustc_hash::{FxBuildHasher, FxHashMap};
use string_interner::backend::BucketBackend;
use string_interner::symbol::SymbolU32;
use string_interner::StringInterner;

use crate::{term::Term, types::Type};

pub type InternedSymbol = SymbolU32;
pub type Interner = StringInterner<BucketBackend<InternedSymbol>, FxBuildHasher>;

pub type Span<'a> = LocatedSpan<&'a str>;

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct TermId(usize);

struct SourceRegion {}

struct StorageInternal {
    strings: Interner,
    region_map: FxHashMap<TermId, SourceRegion>,
}

pub struct Storage {
    // antipattern, yes
    internal: RefCell<StorageInternal>,
}

impl Storage {
    pub fn intern(&self, s: impl AsRef<str>) -> InternedSymbol {
        self.internal.borrow_mut().strings.get_or_intern(s)
    }

    pub fn resolve<'s>(&'s self, s: InternedSymbol) -> Ref<'s, str> {
        Ref::map(self.internal.borrow(), |internal| {
            internal
                .strings
                .resolve(s)
                .expect("missing string for symbol")
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
            internal: RefCell::new(StorageInternal {
                strings: Interner::with_hasher(FxBuildHasher),
                region_map: FxHashMap::default(),
            }),
        }
    }
}

pub struct WithStorage<'a, T>(pub &'a T, pub &'a Storage)
where
    T: ?Sized;

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
