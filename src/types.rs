use std::fmt::Debug;

use itertools::Itertools;
use rustc_hash::FxHashMap;
use thiserror::Error;

use crate::storage::{DisplayWithStorage, Storage, WithStorage};
use crate::term::{Choice, StackIdentifier, Term, Variable};
use crate::{EMPTY_STACK_SYMBOL, EMPTY_SUM_SYMBOL};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct StackType(pub Vec<Type>);

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
pub struct MemoryType(pub FxHashMap<StackIdentifier, StackType>);

impl MemoryType {
    pub fn singleton(stack: StackIdentifier, stack_type: StackType) -> Self {
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
pub struct SumType(pub FxHashMap<Choice, MemoryType>);

impl SumType {
    pub fn singleton(choice: Choice, mem_type: MemoryType) -> Self {
        let mut m = FxHashMap::default();
        m.insert(choice, mem_type);
        Self(m)
    }

    pub fn plus(mut a: Self, b: Self) -> Self {
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
pub struct Type(pub MemoryType, pub SumType);

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
