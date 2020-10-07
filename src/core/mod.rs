mod product;
mod sigma;

pub use self::{
    core::{Resolvable, Type, TypedIter},
    product::Product,
    sigma::Sigma,
};

mod core {
    #[derive(Eq, PartialEq, Copy, Clone, Hash, Debug, Ord, PartialOrd)]
    pub enum Type<T> {
        Normal(T),
        Inverse(T),
    }

    impl<T> Type<T> {
        pub fn flip(self) -> Self {
            match self {
                Type::Normal(val) => Type::Inverse(val),
                Type::Inverse(val) => Type::Normal(val),
            }
        }
        pub fn is_inverted(&self) -> bool {
            match self {
                Type::Normal(_) => false,
                Type::Inverse(_) => true,
            }
        }
        pub fn unwrap(self) -> T {
            match self {
                Type::Normal(val) => val,
                Type::Inverse(val) => val,
            }
        }
        pub fn map<P: Fn(T) -> R, R>(self, func: P) -> Type<R> {
            match self {
                Type::Normal(val) => Type::Normal(func(val)),
                Type::Inverse(val) => Type::Inverse(func(val)),
            }
        }
    }

    #[derive(Clone)]
    pub enum TypedIter<I> {
        Normal(I),
        Inverse(I),
    }

    // turns an iterator of T's to an iterator of Type<T>'s
    impl<I: Iterator<Item = T>, T> Iterator for TypedIter<I> {
        type Item = Type<T>;
        fn next(&mut self) -> Option<Self::Item> {
            Some(match self {
                TypedIter::Normal(iter) => Type::Normal(iter.next()?),
                TypedIter::Inverse(iter) => Type::Inverse(iter.next()?),
            })
        }
    }

    #[derive(Clone)]
    pub struct TypedWithIter<I> {
        inner: I,
    }

    impl<I> TypedWithIter<I> {
        pub fn new(iter: I) -> Self {
            TypedWithIter { inner: iter }
        }
    }

    // turns an iter of Type<T>'s to an iterator of Type<Box<T>>'s
    impl<I: Iterator<Item = Type<T>>, T> Iterator for TypedWithIter<I> {
        type Item = Type<Box<T>>;
        fn next(&mut self) -> Option<Self::Item> {
            Some(self.inner.next()?.map(|val| Box::new(val)))
        }
    }

    #[derive(Clone)]
    pub struct FlippedIteratorOfTypes<I> {
        inner: I,
    }

    // turns an iter of Type<T> to an iter of the inverse of each item
    // i.e [Type::Normal(x), Type::Flipped(y)] becomes [Type::Flipped(x), Type::Normal(y)]
    impl<I: Iterator<Item = Type<T>>, T> Iterator for FlippedIteratorOfTypes<I> {
        type Item = Type<T>;
        fn next(&mut self) -> Option<Self::Item> {
            Some(self.inner.next()?.flip())
        }
    }

    pub trait Flippable<I> {
        fn flip(self) -> FlippedIteratorOfTypes<I>;
    }

    // adds the .flip() method to all iterators whose items are Type<T>
    impl<I, T> Flippable<I> for I
    where
        I: Iterator<Item = Type<T>>,
    {
        fn flip(self) -> FlippedIteratorOfTypes<I> {
            FlippedIteratorOfTypes { inner: self }
        }
    }

    pub struct DeBoxify<I> {
        inner: I,
    }

    impl<I> DeBoxify<I> {
        pub fn new(iter: I) -> Self {
            DeBoxify { inner: iter }
        }
    }

    // converts an iterator of Type<Box<T>> to one of Type<T>
    impl<I: Iterator<Item = Type<Box<T>>>, T> Iterator for DeBoxify<I> {
        type Item = Type<T>;
        fn next(&mut self) -> Option<Self::Item> {
            Some(self.inner.next()?.map(|val| *val))
        }
    }

    pub trait Resolvable {
        type Result;
        fn resolve(self) -> Self::Result;
    }

    macro_rules! impl_resolve_primitives {
        ($($type:ty),+) => {
            $(
                impl Resolvable for $type {
                    type Result = $type;
                    fn resolve(self) -> $type {
                        self
                    }
                }
            )+
        };
    }

    impl_resolve_primitives!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128);

    #[cfg(test)]
    mod tests {
        use super::*;
        #[test]
        fn type_flip() {
            let ty = Type::Normal(());
            assert_eq!(ty, Type::Normal(()));
            assert_ne!(ty, Type::Inverse(()));
            assert_eq!(ty.flip(), Type::Inverse(()));

            let ty = Type::Inverse(());
            assert_eq!(ty, Type::Inverse(()));
            assert_ne!(ty, Type::Normal(()));
            assert_eq!(ty.flip(), Type::Normal(()));
        }
        #[test]
        fn iter_type_flip() {
            // flip an iterator of types
            assert_eq!(
                vec![
                    Type::Normal(5),
                    Type::Inverse(10),
                    Type::Inverse(15),
                    Type::Normal(20)
                ]
                .into_iter()
                .flip()
                .collect::<Vec<_>>(),
                vec![
                    Type::Inverse(5),
                    Type::Normal(10),
                    Type::Normal(15),
                    Type::Inverse(20)
                ]
            );
        }
    }
}
