use super::{
    super::{
        exclude::{ExcludedIterator, ExcludedIteratorExt},
        Zero,
    },
    core::*,
};
use std::hash::Hash;

#[derive(Clone)]
pub struct Sigma<I: Iterator, F> {
    iter: I,
    func: F,
}

pub type SigmaIntoIter<I> = DeBoxify<I>;

impl<I, T, F, R> Resolvable for Sigma<I, F>
where
    I: Iterator<Item = Type<Box<T>>>,
    F: Fn(<T as Resolvable>::Result) -> R,
    T: Resolvable,
    R: Zero + std::ops::Sub<Output = R>,
{
    type Result = R;
    fn resolve(self) -> R {
        self.compute()
    }
}

/// allows creating a Product value from an iterator of primitives
impl<'a, I, T: 'a, F, R> Sigma<TypedWithIter<TypedIter<I>>, F>
where
    I: Iterator<Item = T>,
    F: Fn(<T as Resolvable>::Result) -> R,
    T: Resolvable,
{
    pub fn from_normal(iter: I, func: F) -> Self {
        Sigma::with(TypedIter::Normal(iter), func)
    }
    pub fn from_inverse(iter: I, func: F) -> Self {
        Sigma::with(TypedIter::Inverse(iter), func)
    }
}

impl<I, T, F, R> Sigma<TypedWithIter<I>, F>
where
    I: Iterator<Item = Type<T>>,
    F: Fn(<T as Resolvable>::Result) -> R,
    T: Resolvable,
{
    pub fn with<P>(iter: P, func: F) -> Self
    where
        P: IntoIterator<Item = I::Item, IntoIter = I>,
    {
        Sigma {
            iter: TypedWithIter::new(iter.into_iter()),
            func,
        }
    }
}

impl<I, T, F, R> Sigma<I, F>
where
    I: Iterator<Item = Type<Box<T>>>,
    F: Fn(<T as Resolvable>::Result) -> R,
    T: Resolvable,
{
    pub fn compute(self) -> R
    where
        R: Zero + std::ops::Sub<Output = R>,
    {
        let func = &self.func;
        let (normal, inverse) = self.iter.fold((None, None), |(normal, inverse), val| {
            let is_inverted = val.is_inverted();
            let (this, other) = if !is_inverted {
                (normal, inverse)
            } else {
                (inverse, normal)
            };
            let this = Some(match this {
                Some(prev) => prev + func(val.unwrap().resolve()),
                None => func(val.unwrap().resolve()),
            });
            if !is_inverted {
                (this, other)
            } else {
                (other, this)
            }
        });
        let normal = normal.unwrap_or_else(|| R::zero());
        let inverse = inverse.unwrap_or_else(|| R::zero());

        normal - inverse
    }
}

// converts a Sigma struct into an iterator of Type<T>
impl<I: Iterator<Item = Type<Box<T>>>, T, F> IntoIterator for Sigma<I, F> {
    type Item = Type<T>;
    type IntoIter = SigmaIntoIter<I>;
    fn into_iter(self) -> Self::IntoIter {
        SigmaIntoIter::new(self.iter)
    }
}

impl<B, C, T, F> std::ops::Sub<Sigma<C, F>> for Sigma<B, F>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator<Item = Type<Box<T>>>,
    T: Eq + Hash,
    Box<T>: Clone,
{
    type Output = Sigma<ExcludedIterator<B, C, Type<Box<T>>>, F>;
    fn sub(self, rhs: Sigma<C, F>) -> Self::Output {
        Sigma {
            iter: self
                .iter
                .exclude(rhs.iter)
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}

impl<B, C, T, F> std::ops::Add<Sigma<C, F>> for Sigma<B, F>
where
    B: Iterator<Item = Type<Box<T>>>,
    C: Iterator<Item = Type<Box<T>>>,
    T: Eq + Hash,
    Box<T>: Clone,
{
    type Output = Sigma<ExcludedIterator<B, FlippedIteratorOfTypes<C>, Type<Box<T>>>, F>;
    fn add(self, rhs: Sigma<C, F>) -> Self::Output {
        Sigma {
            iter: self
                .iter
                .exclude(rhs.iter.flip())
                .include_overflow_with(|val| val.flip()),
            func: self.func,
        }
    }
}
