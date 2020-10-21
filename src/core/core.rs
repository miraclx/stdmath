#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug, Ord, PartialOrd)]
/// Provide a means to represent the state of a value. Normal or Reciprocal.
pub enum Type<T> {
    /// context        | value | identity | indirect identity
    /// -------------- | ----- | -------- | -----------------
    /// multiplicative |  `3`  | `3 * 1`  | `3 / 1`
    /// additive       |  `3`  | `3 + 0`  | `3 - 0`
    Normal(T),
    /// context        | value | identity | indirect identity
    /// -------------- | ----- | -------- | -----------------
    /// multiplicative |  `3`  | `1 / 3`  | `1 * 3^-1`
    /// additive       |  `3`  | `0 - 3`  | `0 + -3`
    Inverse(T),
}

impl<T> Type<T> {
    /// Inverts the state of the Type
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Typ{mul, sum, Context, Type}e;
    /// #
    /// let val = Type::Normal(10);
    /// let inv = val.flip();
    /// assert_eq!(inv, Type::Inverse(10));
    ///
    /// let val = Type::Inverse(30);
    /// let inv = val.flip();
    /// assert_eq!(inv, Type::Normal(30));
    /// ```
    pub fn flip(self) -> Self {
        match self {
            Type::Normal(val) => Type::Inverse(val),
            Type::Inverse(val) => Type::Normal(val),
        }
    }
    /// Matches the type variant, returning true if self is [`Type::Inverse`](#variant.Inverse)
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Type;
    /// #
    /// let val = Type::Normal(());
    /// assert_eq!(val.is_inverted(), false);
    ///
    /// let val = Type::Inverse(());
    /// assert_eq!(val.is_inverted(), true);
    /// ```
    pub fn is_inverted(&self) -> bool {
        if let Type::Inverse(_) = self {
            return true;
        };
        false
    }
    /// Extracts the value contained in a variant of `Type`
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Type;
    /// #
    /// let val = Type::Normal(21);
    /// assert_eq!(val.unwrap(), 21);
    ///
    /// let val = Type::Inverse("hello");
    /// assert_eq!(val.unwrap(), "hello");
    /// ```
    pub fn unwrap(self) -> T {
        match self {
            Type::Normal(val) => val,
            Type::Inverse(val) => val,
        }
    }
    /// Transform the value within the type variant, returning the result contained within same type variant.
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Type;
    /// #
    /// let val = Type::Normal(533);
    /// assert_eq!(val.map(|num| num - 33), Type::Normal(500));
    ///
    /// let val = Type::Inverse(10);
    /// assert_eq!(val.map(|num| num * 20), Type::Inverse(200));
    /// ```
    pub fn map<P: Fn(T) -> R, R>(self, func: P) -> Type<R> {
        match self {
            Type::Normal(val) => Type::Normal(func(val)),
            Type::Inverse(val) => Type::Inverse(func(val)),
        }
    }
    /// Converts from a `&Type<T>` to a `Type<&T>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Type;
    /// #
    /// let val = Type::Normal(100);
    /// assert_eq!(val.as_ref().map(|val| val * 2), Type::Normal(200));
    ///
    /// let val = Type::Inverse("Hello");
    /// assert_eq!(val.as_ref().map(|txt| txt.len()), Type::Inverse(5));
    /// ```
    pub fn as_ref(&self) -> Type<&T> {
        match self {
            Type::Normal(val) => Type::Normal(val),
            Type::Inverse(val) => Type::Inverse(val),
        }
    }
    /// Converts from a `&mut Type<T>` to a `Type<&mut T>`
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Type;
    /// #
    /// let mut text = Type::Normal("Hello".to_string());
    /// text.as_mut().map(|s| s.push_str(", World!"));
    /// assert_eq!(text.as_ref().map(|s| s.as_str()), Type::Normal("Hello, World!"));
    ///
    /// let mut val = Type::Inverse(33);
    /// val.as_mut().map(|v| *v += 20);
    /// assert_eq!(val, Type::Inverse(53));
    /// ```
    pub fn as_mut(&mut self) -> Type<&mut T> {
        match self {
            Type::Normal(val) => Type::Normal(val),
            Type::Inverse(val) => Type::Inverse(val),
        }
    }
}

/// Provide a means to convert an iterator of `T` to one of `Type<T>`
///
/// # Examples
/// ```
/// # use stdmath::core::Type;
/// #
/// let vals = Type::Normal(1..=5).collect::<Vec<_>>();
/// assert_eq!(vals, vec![
///     Type::Normal(1),
///     Type::Normal(2),
///     Type::Normal(3),
///     Type::Normal(4),
///     Type::Normal(5)
/// ]);
///
/// let vals = Type::Inverse(6..=10).collect::<Vec<_>>();
/// assert_eq!(vals, vec![
///     Type::Inverse(6),
///     Type::Inverse(7),
///     Type::Inverse(8),
///     Type::Inverse(9),
///     Type::Inverse(10)
/// ]);
/// ```
impl<I: Iterator<Item = T>, T> Iterator for Type<I> {
    type Item = Type<T>;
    fn next(&mut self) -> Option<Self::Item> {
        match self.as_mut().map(|item| item.next()) {
            Type::Normal(result) => Some(Type::Normal(result?)),
            Type::Inverse(result) => Some(Type::Inverse(result?)),
        }
    }
}

#[derive(Clone)]
/// Provide a means to convert an iterator of `T` to one of `Type<T>`
///
/// # Examples
/// ```
/// # use stdmath::core::{Type, TypedIter};
/// #
/// let vals = TypedIter::Normal(1..=5).collect::<Vec<_>>();
/// assert_eq!(vals, vec![
///     Type::Normal(1),
///     Type::Normal(2),
///     Type::Normal(3),
///     Type::Normal(4),
///     Type::Normal(5)
/// ]);
///
/// let vals = TypedIter::Inverse(6..=10).collect::<Vec<_>>();
/// assert_eq!(vals, vec![
///     Type::Inverse(6),
///     Type::Inverse(7),
///     Type::Inverse(8),
///     Type::Inverse(9),
///     Type::Inverse(10)
/// ]);
/// ```
#[deprecated = "use Type<T: Iterator> instead"]
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
/// Provide a means to convert an iterator of `Type`s to their inverse variants
/// e.g `[Type::Normal(x), Type::Flipped(y)]` becomes `[Type::Flipped(x), Type::Normal(y)]`
pub struct FlippedIteratorOfTypes<I> {
    inner: I,
}

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
/// Provide a means to convert an iterator of `Type<T>` to one of `Type<Box<T>>`
pub struct TypedWithIter<I> {
    inner: I,
}

impl<I> TypedWithIter<I> {
    pub fn new(iter: I) -> Self {
        TypedWithIter { inner: iter }
    }
}

impl<I: Iterator<Item = Type<T>>, T> Iterator for TypedWithIter<I> {
    type Item = Type<Box<T>>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.map(|val| Box::new(val)))
    }
}

/// Provide a means to convert an iterator of `Type<Box<T>>` to one of `Type<T>`
pub struct DeBoxify<I: Iterator> {
    inner: I,
}

impl<I: Iterator> DeBoxify<I> {
    pub fn new(iter: I) -> Self {
        DeBoxify { inner: iter }
    }
}

impl<I: Iterator<Item = Type<Box<T>>>, T> Iterator for DeBoxify<I> {
    type Item = Type<T>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.map(|val| *val))
    }
}

/// An interface for defining types that can be resolved
///
/// ```
/// use stdmath::core::Resolve;
///
/// struct Squared(u8);
///
/// impl Resolve for Squared {
///     type Result = u16;
///     fn resolve(self: Box<Self>) -> Self::Result {
///         (self.0 as u16).pow(2)
///     }
/// }
///
/// fn add_computables<T, A, B>(a: A, b: B) -> T
/// where
///     A: Resolve<Result = T>,
///     B: Resolve<Result = T>,
///     T: std::ops::Add<Output = T>,
/// {
///     Box::new(a).resolve() + Box::new(b).resolve()
/// }
///
/// assert_eq!(add_computables(Squared(36), 54_u16), 1350);
/// ```
pub trait Resolve {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;
}

macro_rules! impl_resolve_primitives {
    ($($type:ty),+) => {
        $(
            impl Resolve for $type {
                type Result = $type;
                fn resolve(self: Box<Self>) -> $type {
                    *self
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
