use std::fmt::{Debug, Formatter};

use itertools::Itertools;
use log::trace;
use rustc_hash::{FxHashMap, FxHashSet};
use thiserror::Error;

use crate::storage::{DisplayWithStorage, Storage, WithStorage};
use crate::term::{Choice, StackIdentifier, Term, Variable};
use crate::{EMPTY_STACK_SYMBOL, EMPTY_SUM_SYMBOL};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct StackType(pub Vec<Type>);

impl StackType {
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

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

    fn peek(&self) -> Option<&Type> {
        if self.0.is_empty() {
            None
        } else {
            Some(&self.0[self.0.len() - 1])
        }
    }

    fn pop(&mut self) -> Option<Type> {
        self.0.pop()
    }

    fn can_convert(&self, other: &StackType) -> bool {
        if self.0.len() != other.0.len() {
            return false;
        }
        self.0
            .iter()
            .zip_eq(other.0.iter())
            .all(|(a, b)| a.can_convert(b))
    }

    fn stack_expand(&mut self, expansion: &StackType) {
        // FIXME: this is inefficient
        for ty in expansion.0.iter().rev() {
            self.0.insert(0, ty.clone());
        }
    }
}

impl DisplayWithStorage for StackType {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        self.display(f, storage, false)
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

    pub fn is_empty(&self) -> bool {
        self.0.is_empty() || self.0.iter().all(|(_, v)| v.0.is_empty())
    }

    fn stack_expand(&mut self, expansion: &MemoryType) {
        for (a, expansion_on_a) in expansion.0.iter() {
            let stack_on_a = self.0.entry(a.clone()).or_default();
            stack_on_a.stack_expand(expansion_on_a);
        }
    }

    fn display(
        &self,
        f: &mut std::fmt::Formatter<'_>,
        storage: &Storage,
        reversed: bool,
    ) -> std::fmt::Result {
        let MemoryType(m) = self;
        if self.is_empty() {
            return f.write_str(EMPTY_STACK_SYMBOL);
        }
        for (i, (stack_id, stack_ty)) in m
            .iter()
            .filter(|(_, v)| !v.0.is_empty())
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

    fn can_convert(&self, other: &MemoryType) -> bool {
        for (st, stack_ty) in self.0.iter() {
            if other
                .0
                .get(st)
                .is_none_or(|other_stack_ty| !stack_ty.can_convert(&other_stack_ty))
            {
                return false;
            }
        }
        true
    }
}

impl DisplayWithStorage for MemoryType {
    fn fmt_with_storage(&self, f: &mut Formatter, storage: &Storage) -> std::fmt::Result {
        self.display(f, storage, false)
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

    fn can_convert(&self, other: &SumType) -> bool {
        for (i, mem_ty) in self.0.iter() {
            if other
                .0
                .get(i)
                .is_none_or(|other_mem_ty| !mem_ty.can_convert(&other_mem_ty))
            {
                return false;
            }
        }
        true
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

impl Type {
    /// True if t1 can be converted to t2 using the expansion and inclusion rules:
    /// Expansion is implemented by can_expand.
    /// Inclusion is implemented by ensuring that t1's cases are a subset of t2's cases and,
    /// for each choice that they have in common, conversion by expansion is possible.
    pub fn can_convert(&self, other: &Self) -> bool {
        for (choice, source_output) in &self.1 .0 {
            if other.1 .0.get(choice).is_none_or(|dest_output| {
                !can_expand((&self.0, source_output), (&other.0, dest_output))
            }) {
                return false;
            }
        }
        true
    }

    pub fn stack_expand(&mut self, expansion: &MemoryType) {
        self.0.stack_expand(expansion);
        for (_, output_memory) in self.1 .0.iter_mut() {
            output_memory.stack_expand(expansion);
        }
    }
}

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
    let result = match term {
        Term::Variable(x) => context
            .0
            .iter()
            .rev()
            .find(|(id, _)| id == x)
            .map(|(_, ty)| ty.clone())
            .ok_or_else(|| TypeError::UnboundVariable(storage.resolve(x.0).to_owned())),
        Term::Application(a, n, m) => {
            // I think there are two cases where [N]a. M pushing is ok where N: rho and M: sigma=>tau_I:
            //
            // 1. rho is at the top of sigma|a: then the type of application is the type of M with
            //    rho popped off the a stack.
            // 2. sigma|a is empty: then we can stack-expand with a(rho), taking us to case 1.
            //    the type of the application will then be sigma => (a(rho) tau)_I

            let pushed_type = typecheck(n, context, storage)?; // rho in the push rule.
            let continuation_type = typecheck(m, context, storage)?; // a(rho) sigma => tau

            let Type(MemoryType(input_memory), _) = &continuation_type;
            let input_stack = input_memory.get(a);
            if input_stack
                .and_then(|stack_type| stack_type.peek())
                .is_some_and(|arg_type| pushed_type.can_convert(arg_type))
            {
                // Case 1.
                let mut result = continuation_type;
                result.0 .0.get_mut(a).expect("cannot be none").pop();
                Ok(result)
            } else if input_stack.is_none_or(|stack_type| stack_type.0.is_empty()) {
                // Case 2.
                let mut result = continuation_type;
                for (_, MemoryType(output_memory)) in result.1 .0.iter_mut() {
                    output_memory
                        .entry(a.clone())
                        .or_default()
                        .0
                        .insert(0, pushed_type.clone());
                }
                Ok(result)
            } else {
                Err(TypeError::BadApplication(
                    WithStorage(&continuation_type, storage).to_string(),
                    WithStorage(&pushed_type, storage).to_string(),
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
        Term::Case(m, i, n) => {
            // M needs to produce the input type of N on case i and the output type of N on any other case.
            // If M has no output stack for case i that's fine as the situation can be solved by inc,
            // but if it has a non-matching one then the type checking fails.
            // The overall type of the case statement is the input of M going to the outputs of N
            // summed with the outputs of M except its outputs on I.

            let m_type = typecheck(m, context, storage)?;
            let mut n_type = typecheck(n, context, storage)?;

            // If try_types fails, the situation may still be resolveable by stack-expanding N
            // with M's output on i.
            fn try_types(i: &Choice, m_type: &Type, n_type: &Type) -> Option<Type> {
                // Project M onto the outputs cases of N, as these are the only cases we care about.
                let mut proj_type = m_type.clone();
                proj_type.1 .0 = proj_type
                    .1
                     .0
                    .into_iter()
                    .filter(|(j, _)| n_type.1 .0.contains_key(j))
                    .collect();

                // Create the type we want proj_type to be convertible to.
                let mut wanted_type = Type(m_type.0.clone(), n_type.1.clone());
                wanted_type.1 .0.remove(i);
                wanted_type.1 .0.insert(i.clone(), n_type.0.clone());

                // See if the projected M can be converted to the desired M.
                if proj_type.can_convert(&wanted_type) {
                    let mut result_type = m_type.clone();
                    result_type.1 .0.remove(i);
                    result_type.1 = SumType::plus(result_type.1, n_type.1.clone());

                    Some(result_type)
                } else {
                    None
                }
            }

            if let Some(ty) = try_types(i, &m_type, &n_type) {
                return Ok(ty);
            }

            // Try again with N stack-expanded by M's output on i.
            if let Some(m_output_on_i) = m_type.1 .0.get(i) {
                n_type.stack_expand(m_output_on_i);
                if let Some(ty) = try_types(i, &m_type, &n_type) {
                    return Ok(ty);
                }
            }

            return Err(TypeError::BadCase(
                WithStorage(&m_type, storage).to_string(),
                WithStorage(i, storage).to_string(),
                WithStorage(&n_type, storage).to_string(),
            ));
        }
        Term::Loop(m, i) => {
            // Type for a loop is the type of M with the output on i removed.
            // If there was no output on i that's fine as the situation can be
            // resolved by inclusion.
            let mut result_type = typecheck(m, context, storage)?;
            result_type.1 .0.remove(i);
            Ok(result_type)
        }
    };
    if let Ok(ty) = result.as_ref() {
        trace!(
            "Typecheck '{}' --> OK '{}'",
            WithStorage(term, storage),
            WithStorage(ty, storage)
        );
    } else {
        trace!("Typecheck '{}' --> ERROR", WithStorage(term, storage));
    }
    result
}

// True if t1 can be converted to t2 using the expansion rule:
// t1 can be expanded to t2 if each stack's type vector in t2 ends
// in the same stack's type vector in t1, and the remaining N elements
// towards the start are the same as the first N elements in t1.
fn can_expand(t1: (&MemoryType, &MemoryType), t2: (&MemoryType, &MemoryType)) -> bool {
    let (t1_input, t1_output) = t1;
    let (t2_input, t2_output) = t2;

    // Find the set of all stacks mentioned on any side of either type.
    let all_stacks = std::iter::empty()
        .chain(t1_input.0.keys())
        .chain(t1_output.0.keys())
        .chain(t2_input.0.keys())
        .chain(t2_output.0.keys())
        .collect::<FxHashSet<_>>();

    for stack_id in all_stacks {
        // Get all type vectors as possibly empty slices.
        // A memory type not having a type vector for a stack is the same as having an empty type
        // vector.
        fn get_typevec<'a>(
            stack_id: &StackIdentifier,
            MemoryType(m): &'a MemoryType,
        ) -> &'a [Type] {
            m.get(&stack_id)
                .map(|StackType(v)| v.as_slice())
                .unwrap_or(&[])
        }
        let t1_input_typevec = get_typevec(stack_id, t1_input);
        let t1_output_typevec = get_typevec(stack_id, t1_output);
        let t2_input_typevec = get_typevec(stack_id, t2_input);
        let t2_output_typevec = get_typevec(stack_id, t2_output);

        if t1_output_typevec.len() > t2_output_typevec.len()
            || t1_input_typevec.len() > t2_input_typevec.len()
            // Check that the start of t2's in/out vectors match up to where t1's in/out vectors begin.
            || !t2_input_typevec[0..t2_input_typevec.len() - t1_input_typevec.len()]
                .iter()
                .zip_eq(t2_output_typevec[0..t2_output_typevec.len() - t1_output_typevec.len()].iter())
                .all(|(a, b)| a.can_convert(b))
            // Check the end of t2's output typevec is equal to t1's output typevec.
            || !t2_output_typevec[t2_output_typevec.len() - t1_output_typevec.len()..]
                .iter()
                .zip_eq(t1_output_typevec.iter())
                .all(|(a, b)| a.can_convert(b))
            // Check the end of t2's input typevec is equal to t1's input typevec.
            || !t2_input_typevec[t2_input_typevec.len() - t1_input_typevec.len()..]
                .iter()
                .zip_eq(t1_input_typevec.iter())
                .all(|(a, b)| a.can_convert(b))
        {
            return false;
        }
    }
    true
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TypeError {
    #[error("Missing type in binding of '{_0}'.")]
    BindingMissingType(String),
    #[error("Variable '{_0}' appears unbound.")]
    UnboundVariable(String),
    #[error("Cannot apply '{_0}' to '{_1}'.")]
    BadApplication(String, String),
    #[error("{_1}->'{_2}' is not a valid continuation after '{_0}'.")]
    BadCase(String, String, String),
}
