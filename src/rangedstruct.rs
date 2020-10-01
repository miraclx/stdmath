use std::hash::Hash;

use stdmath::{
    exclude::{ExcludedIterator, ExcludedIteratorExt},
    One,
};

#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug)]
pub enum Type<T> {
    Normal(T),
    Flipped(T),
}

impl<T> Type<T> {
    fn unwrap(self) -> T {
        match self {
            Type::Normal(val) => val,
            Type::Flipped(val) => val,
        }
    }
}

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

pub struct RangedStruct<I, F> {
    iter: I,
    func: F,
}

impl<I, F> RangedStruct<TypedIter<I>, F>
where
    I: Iterator,
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
    pub fn compute(&mut self) -> R
    where
        R: One + std::ops::Div<Output = R> + std::iter::Product,
    {
        let func = &self.func;
        self.iter
            .by_ref()
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
                .with_transformer(|val| Type::Normal(val.unwrap()))
                .include_overflow_with(|val| Type::Flipped(val.unwrap())),
            func: self.func,
        }
    }
}
