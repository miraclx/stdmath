use std::hash::Hash;

use super::{
    exclude::{ExcludedIterator, ExcludedIteratorExt},
    One,
};

#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug, Ord, PartialOrd)]
pub enum Type<T> {
    Normal(T),
    Flipped(T),
}

impl<T> Type<T> {
    fn flip(self) -> Self {
        match self {
            Type::Normal(val) => Type::Flipped(val),
            Type::Flipped(val) => Type::Normal(val),
        }
    }
}

#[derive(Clone)]
pub enum TypedIter<I> {
    Normal(I),
    Flipped(I),
}

impl<I: Iterator<Item = T>, T> Iterator for TypedIter<I> {
    type Item = Type<T>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(match self {
            TypedIter::Normal(iter) => Type::Normal(iter.next()?),
            TypedIter::Flipped(iter) => Type::Flipped(iter.next()?),
        })
    }
}

#[derive(Clone)]
pub struct RangedStruct<I, F> {
    pub iter: I,
    func: F,
}

impl<I, T, F, R> RangedStruct<TypedIter<I>, F>
where
    I: Iterator<Item = T>,
    F: Fn(T) -> R,
{
    pub fn new(iter: I, func: F) -> Self {
        Self {
            iter: TypedIter::Normal(iter),
            func,
        }
    }
}

impl<I, T, F, R> RangedStruct<I, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(T) -> R,
{
    pub fn with(iter: I, func: F) -> Self {
        RangedStruct { iter, func }
    }
    pub fn compute(self) -> R
    where
        R: One + std::ops::Div<Output = R> + std::iter::Product,
    {
        let func = &self.func;
        self.iter
            .map(|val| match val {
                Type::Normal(val) => func(val),
                Type::Flipped(val) => R::one() / func(val),
            })
            .product()
    }
}

impl<B, C, T, F> std::ops::Div<RangedStruct<C, F>> for RangedStruct<B, F>
where
    B: Iterator<Item = Type<T>>,
    C: Iterator<Item = Type<T>>,
    T: Eq + Hash,
{
    type Output = RangedStruct<ExcludedIterator<B, C, Type<T>>, F>;
    fn div(self, rhs: RangedStruct<C, F>) -> Self::Output {
        RangedStruct {
            iter: self
                .iter
                .exclude(rhs.iter)
                .with_transformer(|val| val)
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

impl<B, C, T, F> std::ops::Mul<RangedStruct<C, F>> for RangedStruct<B, F>
where
    B: Iterator<Item = Type<T>>,
    C: Iterator<Item = Type<T>>,
{
    type Output = RangedStruct<std::iter::Chain<B, C>, F>;
    fn mul(self, rhs: RangedStruct<C, F>) -> Self::Output {
        RangedStruct {
            iter: self.iter.chain(rhs.iter),
            func: self.func,
        }
    }
}
