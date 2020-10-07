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

pub trait Compute {
    type Result;
    fn compute(self) -> Self::Result;
}

macro_rules! impl_resolve_primitives {
    ($($type:ty),+) => {
        $(
            impl Compute for $type {
                type Result = $type;
                fn compute(self) -> $type {
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
    fn type_val_map() {
        let ty = Type::Normal(10);
        assert_eq!(ty, Type::Normal(10));
        assert_eq!(ty.map(|val| val * 2), Type::Normal(20));
    }
    #[test]
    fn type_val_unwrap() {
        let ty = Type::Normal(true);
        assert_eq!(ty.unwrap(), true);
        assert_ne!(ty.unwrap(), false);
    }
    #[test]
    fn type_val_check_state() {
        let ty = Type::Normal(true);
        assert_eq!(ty.is_inverted(), false);
        assert_ne!(ty.is_inverted(), true);

        let ty = Type::Inverse(true);
        assert_eq!(ty.is_inverted(), true);
        assert_ne!(ty.is_inverted(), false);

        let ty = Type::Inverse(false).flip().map(|state| !state);
        assert_eq!(ty.is_inverted(), false);
        assert_eq!(ty, Type::Normal(true));
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
    #[test]
    fn convert_iter_t_to_iter_type_t() {
        assert_eq!(
            TypedIter::Normal(1..=6).collect::<Vec<_>>(),
            vec![
                Type::Normal(1),
                Type::Normal(2),
                Type::Normal(3),
                Type::Normal(4),
                Type::Normal(5),
                Type::Normal(6)
            ]
        );

        assert_eq!(
            (3..=7)
                .map(|val| Type::Normal(val))
                .flip()
                .collect::<Vec<_>>(),
            vec![
                Type::Inverse(3),
                Type::Inverse(4),
                Type::Inverse(5),
                Type::Inverse(6),
                Type::Inverse(7)
            ]
        );
    }
    #[test]
    fn convert_iter_type_t_to_iter_type_box_t() {
        assert_eq!(
            TypedWithIter::new((3..=5).map(|val| Type::Normal(val))).collect::<Vec<_>>(),
            vec![
                Type::Normal(Box::new(3)),
                Type::Normal(Box::new(4)),
                Type::Normal(Box::new(5))
            ]
        );

        assert_eq!(
            TypedWithIter::new(
                vec![
                    Type::Normal(1),
                    Type::Normal(2),
                    Type::Normal(3),
                    Type::Normal(4)
                ]
                .into_iter()
            )
            .collect::<Vec<_>>(),
            vec![
                Type::Normal(Box::new(1)),
                Type::Normal(Box::new(2)),
                Type::Normal(Box::new(3)),
                Type::Normal(Box::new(4)),
            ]
        )
    }
    #[test]
    fn convert_iter_type_box_t_to_iter_type_t() {
        assert_eq!(
            DeBoxify::new(TypedWithIter::new((3..=6).map(|val| Type::Normal(val))))
                .collect::<Vec<_>>(),
            vec![
                Type::Normal(3),
                Type::Normal(4),
                Type::Normal(5),
                Type::Normal(6)
            ]
        );

        assert_eq!(
            DeBoxify::new(
                vec![
                    Type::Normal(Box::new(3)),
                    Type::Normal(Box::new(4)),
                    Type::Normal(Box::new(5)),
                    Type::Normal(Box::new(6)),
                ]
                .into_iter()
            )
            .collect::<Vec<_>>(),
            vec![
                Type::Normal(3),
                Type::Normal(4),
                Type::Normal(5),
                Type::Normal(6)
            ]
        );
    }
}
