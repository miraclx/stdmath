use super::{exclude::ExcludedIteratorExt, One, Zero};
use std::{
    any::Any,
    cmp::{Eq, Ordering, PartialEq},
    fmt::{self, Debug, Write},
    hash::{Hash, Hasher},
};

/// Provides a means to represent the state of a value.
#[derive(Eq, PartialEq, Copy, Clone, Hash, Debug, Ord, PartialOrd)]
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
    /// Inverts the state of the Type.
    ///
    /// # Examples
    ///
    /// ```
    /// # use stdmath::core::Type;
    /// #
    /// let val = Type::Normal(10);
    /// let inv = val.flip();
    /// assert_eq!(inv, Type::Inverse(10));
    ///
    /// let val = Type::Inverse(30);
    /// let inv = val.flip();
    /// assert_eq!(inv, Type::Normal(30));
    ///
    /// // flip a type wrapping an iterator
    /// let vals = Type::Inverse(6..=8).flip();
    /// assert_eq!(vals, Type::Normal(6..=8));
    /// assert_eq!(vals.collect::<Vec<_>>(), vec![
    ///     Type::Normal(6),
    ///     Type::Normal(7),
    ///     Type::Normal(8)
    /// ])
    /// ```
    #[inline]
    pub fn flip(self) -> Self {
        match self {
            Type::Normal(val) => Type::Inverse(val),
            Type::Inverse(val) => Type::Normal(val),
        }
    }
    /// Matches the type variant, returning true if self is [`Type::Inverse`].
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
    #[inline]
    pub fn is_inverted(&self) -> bool {
        if let Type::Inverse(_) = self {
            return true;
        };
        false
    }
    /// Extracts the value contained in a variant of `Type`.
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
    #[inline]
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
    #[inline]
    pub fn map<P: Fn(T) -> R, R>(self, func: P) -> Type<R> {
        match self {
            Type::Normal(val) => Type::Normal(func(val)),
            Type::Inverse(val) => Type::Inverse(func(val)),
        }
    }
    /// Converts from a `&Type<T>` to a `Type<&T>`.
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
    #[inline]
    pub fn as_ref(&self) -> Type<&T> {
        match self {
            Type::Normal(val) => Type::Normal(val),
            Type::Inverse(val) => Type::Inverse(val),
        }
    }
    /// Converts from a `&mut Type<T>` to a `Type<&mut T>`.
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
    #[inline]
    pub fn as_mut(&mut self) -> Type<&mut T> {
        match self {
            Type::Normal(val) => Type::Normal(val),
            Type::Inverse(val) => Type::Inverse(val),
        }
    }
}

/// Provide a means to convert an iterator of `T` to one of `Type<T>`.
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

/// An iterator that flips the type variant of it's items.
///
/// # Examples
/// ```
/// # use stdmath::core::{Type, Flippable, FlippedIteratorOfTypes};
/// #
/// let vals: FlippedIteratorOfTypes<_> = vec![
///     Type::Normal(1),
///     Type::Inverse(2),
///     Type::Normal(3)
/// ].flip();
/// assert_eq!(vals.collect::<Vec<_>>(), vec![
///     Type::Inverse(1),
///     Type::Normal(2),
///     Type::Inverse(3)
/// ]);
/// ```
#[derive(Clone)]
pub struct FlippedIteratorOfTypes<I> {
    inner: I,
}

impl<I: Iterator<Item = Type<T>>, T> Iterator for FlippedIteratorOfTypes<I> {
    type Item = Type<T>;
    fn next(&mut self) -> Option<Self::Item> {
        Some(self.inner.next()?.flip())
    }
}

/// An interface for flipping an iterator of types.
pub trait Flippable<I> {
    fn flip(self) -> FlippedIteratorOfTypes<I>;
}

/// Adds the `.flip()` helper method for all objects that can become an iterator of `Type<T>`.
///
/// # Examples
/// ```
/// # use stdmath::core::Type;
/// #
/// // Invert the odd numbers within this iteration
/// assert_eq!(
///     Type::Normal(2..=7)
///         .fuse() // lock the iterator, workaround for `.map()` disambiguation
///         .map(|item: Type<u8>| {
///             if item.as_ref().map(|val: &u8| val % 2 != 0).unwrap() {
///                 return item.flip();
///             }
///             item
///         })
///         .collect::<Vec<_>>(),
///     vec![
///         Type::Normal(2),
///         Type::Inverse(3),
///         Type::Normal(4),
///         Type::Inverse(5),
///         Type::Normal(6),
///         Type::Inverse(7),
///     ]
/// );
/// ```
impl<I, T> Flippable<I::IntoIter> for I
where
    I: IntoIterator<Item = Type<T>>,
{
    #[inline]
    fn flip(self) -> FlippedIteratorOfTypes<I::IntoIter> {
        FlippedIteratorOfTypes {
            inner: self.into_iter(),
        }
    }
}

/// Trait for values that can be simplified.
///
/// ## How is this different from `Debug` or `Display`
///
/// `Simplify` indicates the property for a value to be represented within a context.
/// Not all values have the same representation across all these traits.
/// It's perfectly fine to defer the `Simplify` implementation to either traits.
///
/// ## How can I implement `Simplify`?
///
/// `Simplify` only requires the implementation of the `simplify` method, with the others
/// generated from default implementations.
///
/// ```
/// use std::fmt;
/// use stdmath::core::Simplify;
///
/// struct Complex<T>(T, T);
///
/// impl<T: fmt::Display> Simplify for Complex<T> {
///     fn simplify(&self, file: &mut dyn fmt::Write) -> fmt::Result {
///         write!(file, "({}+{}j)", self.0, self.1)
///     }
/// }
///
/// let val = Complex(2, 5);
/// assert_eq!(val.repr().expect("failed to represent context"), "(2+5j)");
/// ```
pub trait Simplify {
    /// This method serializes `self` into any `file` that implements [`Write`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stdmath::core::Simplify;
    ///
    /// let mut file = String::new();
    /// 50_u8.simplify(&mut file).expect("failed to simplify");
    /// assert_eq!(file, "50".to_string());
    /// ```
    fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result;
    /// This helper method serializes `self` into a [`String`].
    ///
    /// # Examples
    ///
    /// ```
    /// use stdmath::core::Simplify;
    ///
    /// let mut file = String::new();
    /// 50_u8.simplify(&mut file).expect("failed to simplify");
    /// assert_eq!(file, "50".to_string());
    /// ```
    #[inline]
    fn repr(&self) -> Result<String, std::fmt::Error> {
        let mut file = String::new();
        Simplify::simplify(self, &mut file)?;
        Ok(file)
    }
}

/// Trait for objects that can be resolved to a value.
///
/// ## How can I implement `Resolve`?
///
/// `Resolve` primarily requires the implementation of the `resolve` method. But also depends on all methods being implemented.
/// The default behaviour of a provided method is to panic from unimplementation (See [`unimplemented!()`]).
///
/// You can use the helpful [`stage_default_methods!()`] macro to apply default implementations of these methods.
///
/// `Resolve` requries that your type implements [`Simplify`].
///
/// ```
/// use std::fmt;
/// use stdmath::{stage_default_methods, core::{Simplify, Resolve}};
///
/// #[derive(Debug, Hash, Clone, PartialEq, PartialOrd)]
/// struct Add(u8, u8);
///
/// impl Simplify for Add {
///     fn simplify(&self, file: &mut dyn fmt::Write) -> fmt::Result {
///         write!(file, "({} + {})", self.0, self.1)
///     }
/// }
///
/// impl Resolve for Add {
///     type Result = u8;
///     stage_default_methods!(is_friendly_with to_context ALL);
///     fn resolve(self: Box<Self>) -> Self::Result {
///         self.0 + self.1
///     }
/// }
///
/// let val = Add(10, 20);
/// assert_eq!(val.repr().expect("failed to represent context"), "(10 + 20)");
/// assert_eq!(Box::new(val).resolve(), 30);
/// ```
pub trait Resolve: Simplify {
    /// The result of the object resolution.
    type Result;
    /// This method resolves `self` into it's equivalent [`Result`][Self::Result] type.
    fn resolve(self: Box<Self>) -> Self::Result;

    // methods needed for dynamicism

    /// This method transposes `self` into a dynamic [`Any`][std::any::Any] representation.
    ///
    /// ```compile_fail
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn as_any(&self) -> &dyn Any {
    ///         // cast a reference to self as a dynamic reference
    ///         self
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// This is required for dynamicism between varied types that impl `Resolve`.
    fn as_any(&self) -> &dyn Any;
    /// This method determines whether the type behind the dynamic reference `other`
    /// is a type that is friendly with `self` during simplification & resolution.
    ///
    /// # What this means
    ///
    /// During simplification, friendly values can be included within the same bracket scope.
    ///
    /// Given `(1 + 2 + (3 + 4))`
    ///
    /// - `2` and `1` are friendly
    /// - `3` and `2` are unfriendly
    /// - `4` and `3` are friendly
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn is_friendly_with(&self, other: &dyn Resolve<Result = Self::Result>) -> bool {
    ///         // check if other is a valid object whose type matches MyValue
    ///         other.as_any().is::<Self>()
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// This is required for dynamicism between varied types that impl `Resolve`.
    fn is_friendly_with(&self, other: &dyn Resolve<Result = Self::Result>) -> bool;
    /// This method partially compares `self` with the type behind the dynamic reference `other`
    ///
    /// # Partial Comparison
    ///
    /// - returns `None` if `other` is not a type that matches `Self`.
    /// - returns `None` if `other` is not partially comparable to `Self`.
    /// - returns `Some(Ordering)` otherwise.
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// use std::cmp::PartialOrd;
    ///
    /// #[derive(PartialEq, PartialOrd)]
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering> {
    ///         // attempt casting other to the type MyValue
    ///         // after conversion, partially compare both types
    ///         other
    ///             .as_any()
    ///             .downcast_ref::<Self>()
    ///             .map_or(None, |other| PartialOrd::partial_cmp(self, other))
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// This is required for dynamicism between varied types that impl `Resolve`.
    fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering>;
    /// This method enables cloning trait objects that implements `Resolve`
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// #[derive(Clone)]
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
    ///         // return a Resolve trait object from a clone of Self
    ///         Box::new(self.clone()) as Box<dyn Resolve<Result = Self::Result>>
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// While this is a provided method, it's default implementation is to panic from unimplementation (See [`unimplemented!()`]).
    /// So, if cloning functionality is ever needed, you'd have to overload this method.
    #[inline]
    fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
        unimplemented!()
    }
    /// This method enables debugging trait objects that implements `Resolve`
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// use std::fmt;
    ///
    /// #[derive(Debug)]
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn _debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    ///         // proxy for debugging Self
    ///         fmt::Debug::fmt(self, f)
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// While this is a provided method, it's default implementation is to panic from unimplementation (See [`unimplemented!()`]).
    /// So, if debugging is ever needed, you'd have to overload this method.
    #[inline]
    fn _debug(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
    /// This method enables hashing trait objects that implements `Resolve`
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// use std::hash::{Hash, Hasher};
    ///
    /// #[derive(Hash)]
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn _hash(&self, state: &mut dyn Hasher) {
    ///         // proxy for hashing Self
    ///         Hash::hash(self, &mut state)
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// This is required for dynamicism between varied types that impl `Resolve`.
    fn _hash(&self, _state: &mut dyn Hasher);
    /// This method allows wrapping a resolvable value into a context
    ///
    /// # Behaviour
    /// If the underlying value is already a context, it returns that,
    /// otherwise, wrap it within a Nil context
    ///
    /// # Example
    ///
    /// ```compile_fail
    /// struct MyValue;
    /// impl Resolve for MyValue {
    ///     ...
    ///     fn to_context(self) -> Context<Self::Result> {
    ///         // wrap self within a context
    ///         stdmath::core::value(self)
    ///     }
    ///     ...
    /// }
    /// ```
    ///
    /// This is required for dynamicism between varied types that impl `Resolve`.
    fn to_context(self) -> Context<Self::Result>;
}

impl<X> PartialEq for dyn Resolve<Result = X> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        if let Some(Ordering::Equal) = self._cmp(other) {
            return true;
        }
        false
    }
}

impl<X> Eq for dyn Resolve<Result = X> {}

impl<X> PartialOrd for dyn Resolve<Result = X> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self._cmp(other)
    }
}

impl<X> Debug for dyn Resolve<Result = X> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._debug(f)
    }
}

impl<X> Clone for Box<dyn Resolve<Result = X>> {
    #[inline]
    fn clone(&self) -> Self {
        (**self)._clone()
    }
}

impl<X> Hash for Box<dyn Resolve<Result = X>> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        (**self)._hash(state);
    }
}

#[macro_export]
macro_rules! stage_default_methods {
    () => {};
    (ALL) => {
        $crate::stage_default_methods!(as_any _cmp _debug _clone _hash);
    };
    (as_any $($rest:tt)*) => {
        #[inline]
        fn as_any(&self) -> &dyn ::std::any::Any {
            self
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (_cmp $($rest:tt)*) => {
        #[inline]
        fn _cmp(&self, other: &dyn $crate::core::Resolve<Result = Self::Result>) -> ::std::prelude::v1::Option<::std::cmp::Ordering> {
            other
                .as_any()
                .downcast_ref::<Self>()
                .map_or(None, |other| ::std::cmp::PartialOrd::partial_cmp(self, other))
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (is_friendly_with $($rest:tt)*) => {
        #[inline]
        fn is_friendly_with(&self, other: &dyn $crate::core::Resolve<Result = Self::Result>) -> bool {
            other.as_any().is::<Self>()
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (is_friendly_with_all $($rest:tt)*) => {
        #[inline]
        fn is_friendly_with(&self, _other: &dyn $crate::core::Resolve<Result = Self::Result>) -> bool {
            true
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (_debug $($rest:tt)*) => {
        #[inline]
        fn _debug(&self, f: &mut ::std::fmt::Formatter<'_>) -> ::std::fmt::Result {
            ::std::fmt::Debug::fmt(self, f)
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (_clone $($rest:tt)*) => {
        #[inline]
        fn _clone(&self) -> ::std::prelude::v1::Box<dyn $crate::core::Resolve<Result = Self::Result>> {
            ::std::prelude::v1::Box::new(::std::prelude::v1::Clone::clone(self)) as ::std::prelude::v1::Box<dyn $crate::core::Resolve<Result = Self::Result>>
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (_hash $($rest:tt)*) => {
        #[inline]
        fn _hash(&self, mut state: &mut dyn ::std::hash::Hasher) {
            ::std::hash::Hash::hash(self, &mut state)
        }
        $crate::stage_default_methods!($($rest)*);
    };
    (to_context $($rest:tt)*) => {
        #[inline]
        fn to_context(self) -> $crate::core::Context<Self::Result> {
            $crate::core::Context::Nil(::std::prelude::v1::Box::new(self))
        }
        $crate::stage_default_methods!($($rest)*);
    };
}

macro_rules! bulk_impl_traits {
    (@ [$($methods:tt)+] $type:ty {$($items:item)*}) => {
        impl Resolve for $type {
            type Result = $type;
            stage_default_methods!($($methods)+);
            stage_default_methods!(is_friendly_with_all to_context);
            $($items)*
            #[inline]
            fn resolve(self: Box<Self>) -> Self::Result {
                *self
            }
        }
        impl Simplify for $type {
            #[inline]
            fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
                write!(file, "{}", self)
            }
        }
    };
    (float($($type:ty),+)) => {
        $(
            bulk_impl_traits!(@ [as_any _cmp _debug _clone] $type {
                #[inline]
                fn _hash(&self, mut state: &mut dyn Hasher) {
                    self.to_bits().hash(&mut state)
                }
            });
        )+
    };
    (vars($($type:ty),+)) => {
        $(
            impl Resolve for $type {
                // fixme: this could be an unnecessary hack
                // fixme: i.e pegging the result to a usize
                // fixme: maybe creating a custom struct wrapping
                // fixme: strings would be a better alternative
                type Result = usize;
                stage_default_methods!(is_friendly_with_all to_context ALL);
                #[inline]
                fn resolve(self: Box<Self>) -> Self::Result {
                    unimplemented!("cannot resolve strings")
                }
            }
            impl Simplify for $type {
                #[inline]
                fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
                    write!(file, "{}", self)
                }
            }
        )+
    };
    ($($type:ty),+) => {
        $(bulk_impl_traits!(@ [ALL] $type {});)+
    }
}

bulk_impl_traits!(i8, i16, i32, i64, isize);
bulk_impl_traits!(u8, u16, u32, u64, usize);
bulk_impl_traits!(float(f32, f64));
bulk_impl_traits!(i128, u128);
bulk_impl_traits!(vars(char, String));

impl<X> Simplify for Box<dyn Resolve<Result = X>> {
    fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
        (&**self).simplify(file)
    }
}

impl<X: 'static> Resolve for Box<dyn Resolve<Result = X>> {
    type Result = X;
    stage_default_methods!(is_friendly_with to_context ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        (*self).resolve()
    }
}

#[derive(Hash, PartialEq, PartialOrd)]
pub enum ContextVal<M, S> {
    Multiple(M),
    Single(S),
}

impl<M, S> ContextVal<M, S> {
    #[inline]
    pub fn multiple(self) -> Option<M> {
        match self {
            ContextVal::Multiple(m) => Some(m),
            _ => None,
        }
    }
    #[inline]
    pub fn single(self) -> Option<S> {
        match self {
            ContextVal::Single(s) => Some(s),
            _ => None,
        }
    }
}

pub enum Context<R> {
    Add(Vec<Type<Box<dyn Resolve<Result = R>>>>),
    Mul(Vec<Type<Box<dyn Resolve<Result = R>>>>),
    Nil(Box<dyn Resolve<Result = R>>),
}

impl<R: 'static> Context<R> {
    #[inline]
    pub fn resolve(self) -> R
    where
        R: One + Zero + std::ops::Mul + std::ops::Add + std::ops::Div + std::ops::Sub,
    {
        Box::new(self).resolve()
    }
    #[inline]
    pub fn dump(
        self,
    ) -> ContextVal<Vec<Type<Box<dyn Resolve<Result = R>>>>, Box<dyn Resolve<Result = R>>> {
        match self {
            Context::Add(vec) | Context::Mul(vec) => ContextVal::Multiple(vec),
            Context::Nil(val) => ContextVal::Single(val),
        }
    }
    #[inline]
    pub fn get_ref(
        &self,
    ) -> ContextVal<&Vec<Type<Box<dyn Resolve<Result = R>>>>, &Box<dyn Resolve<Result = R>>> {
        match self {
            Context::Add(vec) => ContextVal::Multiple(vec),
            Context::Mul(vec) => ContextVal::Multiple(vec),
            Context::Nil(val) => ContextVal::Single(val),
        }
    }
    #[inline]
    pub fn is_additive(&self) -> bool {
        if let Context::Add(_) = self {
            return true;
        }
        false
    }
    #[inline]
    pub fn to_valid_or(self, f: fn(Box<dyn Resolve<Result = R>>) -> Self) -> Self {
        if let Context::Nil(val) = self {
            return f(val);
        }
        self
    }
    #[inline]
    fn typed_map_handle<X: 'static>(
        vec: Vec<Type<Box<dyn Resolve<Result = R>>>>,
        f: fn(R) -> X,
    ) -> Vec<Type<Box<dyn Resolve<Result = X>>>> {
        vec.into_iter()
            .map(|item| {
                item.map(|val| Box::new(TransformedValue(val, f)) as Box<dyn Resolve<Result = X>>)
            })
            .collect()
    }
    #[inline]
    pub fn type_map<X: 'static>(self, f: fn(R) -> X) -> Context<X> {
        match self {
            Context::Add(vec) => Context::Add(Self::typed_map_handle(vec, f)),
            Context::Mul(vec) => Context::Mul(Self::typed_map_handle(vec, f)),
            Context::Nil(val) => Context::Nil(Box::new(TransformedValue(val, f))),
        }
    }
}

impl<R: 'static> PartialEq for Context<R> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        let id_me = std::mem::discriminant(self);
        let id_you = std::mem::discriminant(other);
        if id_me == id_you {
            self.get_ref() == other.get_ref()
        } else {
            false
        }
    }
}

impl<R: 'static> PartialOrd for Context<R> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let id_me = unsafe { *(&std::mem::discriminant(self) as *const _ as *const usize) };
        let id_you = unsafe { *(&std::mem::discriminant(other) as *const _ as *const usize) };
        if id_me == id_you {
            self.get_ref().partial_cmp(&other.get_ref())
        } else {
            id_me.partial_cmp(&id_you)
        }
    }
}

impl<R: 'static> Hash for Context<R> {
    #[inline]
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_ref().hash(state)
    }
}

impl<R> Debug for Context<R> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (name, val): (_, &dyn Debug) = match self {
            Context::Add(vec) => ("Add", vec),
            Context::Mul(vec) => ("Mul", vec),
            Context::Nil(val) => ("Nil", val),
        };
        f.debug_tuple(name).field(val).finish()
    }
}

impl<R> Clone for Context<R> {
    #[inline]
    fn clone(&self) -> Self {
        match self {
            Context::Add(vec) => Context::Add(vec.clone()),
            Context::Mul(vec) => Context::Mul(vec.clone()),
            Context::Nil(val) => Context::Nil(val.clone()),
        }
    }
}

impl<R: 'static> Resolve for Context<R>
where
    R: One + Zero + std::ops::Mul + std::ops::Add + std::ops::Div + std::ops::Sub,
{
    type Result = R;
    stage_default_methods!(is_friendly_with_all ALL);
    #[inline]
    fn to_context(self) -> Context<Self::Result> {
        self
    }
    fn resolve(self: Box<Self>) -> Self::Result {
        #[allow(clippy::type_complexity)]
        let (vec, default, [normal_op, inverse_op]): (_, fn() -> R, [fn(R, R) -> R; 2]) =
            match *self {
                Context::Add(vec) => (vec, || R::zero(), [std::ops::Add::add, std::ops::Sub::sub]),
                Context::Mul(vec) => (vec, || R::one(), [std::ops::Mul::mul, std::ops::Div::div]),
                Context::Nil(val) => return val.resolve(),
            };
        let (mut normal, mut inverse) = (None, None);
        for item in vec {
            let is_inverted = item.is_inverted();
            let this = if !is_inverted {
                &mut normal
            } else {
                &mut inverse
            };
            let val = item.unwrap().resolve();
            *this = Some(match this.take() {
                Some(prev) => normal_op(prev, val),
                None => val,
            })
        }
        let normal = normal.unwrap_or_else(default);
        let inverse = inverse.unwrap_or_else(default);

        inverse_op(normal, inverse)
    }
}

impl<R: 'static> Simplify for Context<R> {
    fn simplify(&self, mut file: &mut dyn Write) -> std::fmt::Result {
        let (is_additive, vec) = (
            self.is_additive(),
            match self.get_ref() {
                ContextVal::Multiple(vec) => vec,
                ContextVal::Single(val) => return val.simplify(&mut file),
            },
        );
        let (mut normal, mut inverse) = (None, None);
        for item in vec {
            let is_inverted = item.is_inverted();
            #[allow(clippy::type_complexity)]
            let this: &mut Option<((&(dyn Resolve<Result = R>), i32), (String, bool))> =
                if !is_inverted {
                    &mut normal
                } else {
                    &mut inverse
                };
            let mut file = String::new();
            let item = &**item.as_ref().unwrap();
            item.simplify(&mut file)?;
            if let Some(((prev, bracket_stack), (this_file, over_one))) = this {
                *over_one = true;
                // Check that the previous item is friendly with this item
                // And check that this item is friendly with the previous item
                let is_friendly = prev.is_friendly_with(item) && item.is_friendly_with(*prev);
                if !is_friendly && *bracket_stack > 0 {
                    String::push_str(this_file, ")");
                    *bracket_stack -= 1;
                }
                String::push_str(this_file, if is_additive { " + " } else { " * " });
                if !is_friendly {
                    String::push_str(this_file, "(");
                    *bracket_stack += 1;
                }
                String::push_str(this_file, &file);
                *prev = item;
            } else {
                *this = Some(((item, 0), (file, false)));
            };
        }
        let handle_brackets = |side| {
            Option::map(side, |((_, bracket_stack), (mut file, over_one))| {
                (0..bracket_stack).for_each(|_| String::push_str(&mut file, ")"));
                (file, over_one)
            })
        };
        let (normal, inverse) = (handle_brackets(normal), handle_brackets(inverse));
        match (normal, inverse) {
            (Some((normal, n_over_one)), Some((inverse, f_over_one))) => write!(
                file,
                "({}{}{})",
                if n_over_one {
                    format!("({})", normal)
                } else {
                    normal
                },
                if is_additive { " - " } else { " / " },
                if f_over_one {
                    format!("({})", inverse)
                } else {
                    inverse
                },
            ),
            (Some((normal, n_over_one)), None) => {
                if n_over_one {
                    write!(file, "({})", normal)
                } else {
                    write!(file, "{}", normal)
                }
            }
            (None, Some((inverse, f_over_one))) => write!(
                file,
                "{}{}",
                if is_additive { "-" } else { "1/" },
                if f_over_one {
                    format!("({})", inverse)
                } else {
                    inverse
                }
            ),
            (None, None) => Ok(()),
        }
    }
}

#[macro_export]
macro_rules! ctx {
    () => {};
    ($val: ident) => {
        $crate::ctx!($val,);
    };
    ($val: ident = $var: expr) => {
        $crate::ctx!($val = $var,);
    };
    (($($val: ident),+) = $var: expr) => {
        $crate::ctx!(($($val),+) = $var,);
    };
    ($val: ident = $var: expr, $($rest:tt)*) => {
        let $val: $crate::core::Context<_> = $crate::ctx!({$var});
        $crate::ctx!($($rest)*);
    };
    (($($val: ident),+) = $var: expr, $($rest:tt)*) => {
        $(let $val: $crate::core::Context<_> = $crate::ctx!({$var});)+
        $crate::ctx!($($rest)*);
    };
    ($val: ident, $($rest:tt)*) => {
        let $val: $crate::core::Context<_>;
        $crate::ctx!($($rest)*);
    };
    ({( $($val: expr),+ )}) => { ( $( $crate::ctx!({ $val }) ),+ ) };
    ({$val: expr}) => { $crate::core::Resolve::to_context($val) };
    ({$($vars:tt)*} $expr:expr) => {
        {
            $crate::ctx!($($vars)*);
            $expr
        }
    };
}

#[macro_export]
macro_rules! mul {
    [$($var:expr),+] => {
        $crate::Context::Mul( ::std::vec![ $($var),+ ] )
    };
}

#[macro_export]
macro_rules! add {
    [$($var:expr),+] => {
        $crate::Context::Add( ::std::vec![ $($var),+ ] )
    };
}

#[macro_export]
macro_rules! n {
    ($val:expr) => {
        $crate::Type::Normal(::std::prelude::v1::Box::new($val)
            as ::std::prelude::v1::Box<dyn $crate::Resolve<Result = _>>)
    };
}

#[macro_export]
macro_rules! i {
    ($val:expr) => {
        $crate::Type::Inverse(
            Box::new($val) as ::std::prelude::v1::Box<dyn $crate::Resolve<Result = _>>
        )
    };
}

macro_rules! impl_ops {
    ($($trait:path[fn $method:ident($lhs_ident:ident, $rhs_ident:ident) -> $final_variant:path] => {$($rules:tt)+}),+) => {
        $(
            impl<R: 'static> $trait for Context<R>
            where
                R: One
                    + Zero
                    + std::ops::Mul
                    + std::ops::Add
                    + std::ops::Div
                    + std::ops::Sub,
            {
                type Output = Context<R>;
                #[inline]
                fn $method(self, rhs: Self) -> Self::Output {
                    let ($lhs_ident, $rhs_ident) = (
                        self.to_valid_or(|val| $final_variant(vec![Type::Normal(val)])),
                        rhs.to_valid_or(|val| $final_variant(vec![Type::Normal(val)]))
                    );
                    $final_variant(impl_ops!(rules $($rules)+).collect())
                }
            }
        )+
    };
    (rules
        base => $base_cond:expr , $base_true:expr , $base_false:expr ;
        ctrl => $ctrl_cond:expr , $ctrl_true:expr , $ctrl_false:expr ;
        incl => $incl_expr:expr;
    ) => {
        if $base_cond {
            Box::new($base_true) as Box<dyn Iterator<Item = Type<Box<_>>>>
        } else {
            Box::new($base_false)
        }
        .exclude(
            if $ctrl_cond {
                Box::new($ctrl_true) as Box<dyn Iterator<Item = Type<Box<_>>>>
            } else {
                Box::new($ctrl_false)
            }
        )
        .include_overflow_with($incl_expr)
    };
    (rules default_normal($sign:tt, $lhs:ident, $rhs:ident)) => {
        impl_ops!(
            rules
              base => impl_ops!(ctx $sign $lhs)
                , impl_ops!(dump_items $lhs)
                , impl_ops!(dump_raw $lhs);
              ctrl => impl_ops!(ctx $sign $rhs)
                , impl_ops!(dump_items $rhs).flip()
                , impl_ops!(dump_raw $rhs).flip();
              incl => impl_ops!(incl_default);
        )
    };
    (rules default_inverse($sign:tt, $lhs:ident, $rhs:ident)) => {
        impl_ops!(
            rules
              base => impl_ops!(ctx $sign $lhs)
                , impl_ops!(dump_items $lhs)
                , impl_ops!(dump_raw $lhs);
              ctrl => impl_ops!(ctx $sign $rhs)
                , impl_ops!(dump_items $rhs)
                , impl_ops!(dump_raw $rhs);
              incl => impl_ops!(incl_default);
        )
    };
    (ctx + $side:ident) => {$side.is_additive()};
    (ctx * $side:ident) => {!$side.is_additive()};
    (dump_items $side:ident) => {$side.dump().multiple().expect("expected a defined context, please transpose this Nil context").into_iter()};
    (dump_raw $side:ident) => {
        std::iter::once(Type::Normal(Box::new($side) as Box<dyn Resolve<Result = R>>))
    };
    (incl_default) => {|item| item.flip()}
}

impl_ops! {
    // ((2 + 3 - 4) + (-2 + 3 - 6))
    //   lhs := (2 + 3 - 4)
    //   rhs := (-2 + 3 - 6)
    // ? invert rhs
    //   'rhs := -(-2 + 3 - 6)
    //   'rhs := (2 - 3 + 6)
    // ? exclude matching items in 'rhs from lhs
    //   'lhs := (lhs ^ 'rhs)
    //    = ((2 + 3 - 4) ^ (2 - 3 + 6))
    //   'lhs := (3 - 4) [overflow = (-3 + 6)]
    // ? invert the overflow
    //   'overflow := -(-3 + 6)
    //   'overflow := (3 - 6)
    // ? merge 'overflow and 'lhs
    //   result := ('lhs + 'overflow)
    //    = (3 - 4) + (3 - 6)
    // ? group typed variants
    //   'result := (3 + 3) - (4 + 6)
    //    = (6) - (10)
    //    = -4

    // ((1 - 2 + 3) + (-1 + 2 - 3))
    //   lhs := (1 - 2 + 3)
    //   rhs := (-1 + 2 - 3)
    // ? invert rhs
    //   'rhs := -(-1 + 2 - 3)
    //   'rhs := (1 - 2 + 3)
    // ? exclude matching items in 'rhs from lhs
    //   'lhs := (lhs ^ 'rhs)
    //    = ((1 - 2 + 3) ^ (1 - 2 + 3))
    //   'lhs := () [overflow = ()]
    // ? invert the overflow
    //   'overflow := -()
    //   'overflow := ()
    // ? merge 'overflow and 'lhs
    //   result := ('lhs + 'overflow)
    //    = () + ()
    // ? group typed variants
    //   'result := () - ()
    //    = () - ()
    //    = 0
    std::ops::Add[fn add(lhs, rhs) -> Context::Add] => { default_normal(+, lhs, rhs) },
    // TODO! DOCS
    std::ops::Sub[fn sub(lhs, rhs) -> Context::Add] => { default_inverse(+, lhs, rhs) },
    // TODO! DOCS
    std::ops::Mul[fn mul(lhs, rhs) -> Context::Mul] => { default_normal(*, lhs, rhs) },
    // TODO! DOCS
    std::ops::Div[fn div(lhs, rhs) -> Context::Mul] => { default_inverse(*, lhs, rhs) }
}

macro_rules! impl_ops_with_primitives {
    (($($generics:tt)*) $trait:ident $(:: $trait_path:ident)* ::[$method:ident($lhs:ty, $rhs:ty)]) => {
        impl<$($generics)*> $trait$(::$trait_path)*<Context<$rhs>> for $lhs {
            type Output = Context<$rhs>;
            #[inline]
            fn $method(self, rhs: Context<$rhs>) -> Self::Output {
                $trait$(::$trait_path)*::$method(self.to_context(), rhs)
            }
        }
        impl<$($generics)*> $trait$(::$trait_path)*<$lhs> for Context<$rhs> {
            type Output = Context<$rhs>;
            #[inline]
            fn $method(self, rhs: $lhs) -> Self::Output {
                $trait$(::$trait_path)*::$method(self, rhs.to_context())
            }
        }
    };
    (($($generics:tt)*) $lhs:ty: $rhs:ty) => {
        impl_ops_with_primitives!(($($generics)*) std::ops::Add::[add($lhs, $rhs)]);
        impl_ops_with_primitives!(($($generics)*) std::ops::Sub::[sub($lhs, $rhs)]);
        impl_ops_with_primitives!(($($generics)*) std::ops::Mul::[mul($lhs, $rhs)]);
        impl_ops_with_primitives!(($($generics)*) std::ops::Div::[div($lhs, $rhs)]);
    };
    ($($lhs:ty),+) => {
        $(impl_ops_with_primitives!(() $lhs: <$lhs as Resolve>::Result);)+
    };
}

impl_ops_with_primitives!(i8, i16, i32, i64, isize);
impl_ops_with_primitives!(u8, u16, u32, u64, usize);
impl_ops_with_primitives!(f32, f64);
impl_ops_with_primitives!(i128, u128);
impl_ops_with_primitives!(
    (
        T: Resolve + Clone + Hash + Debug + PartialOrd + 'static,
        R: One
            + Zero
            + std::ops::Mul
            + std::ops::Add
            + std::ops::Div
            + std::ops::Sub + 'static,
        F: Fn(T::Result) -> R + Clone + 'static,
    )
    TransformedValue<T, F>: R
);

pub fn sum<I, T, X>(iter: I) -> Context<X>
where
    I: IntoIterator<Item = Type<T>>,
    T: Resolve<Result = X> + 'static,
{
    Context::Add(
        iter.into_iter()
            .map(|item| item.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>))
            .collect(),
    )
}

pub fn mul<I, T, X>(iter: I) -> Context<X>
where
    I: IntoIterator<Item = Type<T>>,
    T: Resolve<Result = X> + 'static,
{
    Context::Mul(
        iter.into_iter()
            .map(|item| item.map(|val| Box::new(val) as Box<dyn Resolve<Result = _>>))
            .collect(),
    )
}

#[derive(Clone)]
pub struct TransformedValue<T, F>(T, F);

impl<T: Resolve, R, F: Fn(T::Result) -> R> TransformedValue<T, F> {
    #[inline]
    pub fn resolve(self) -> R
    where
        T: Clone + Hash + Debug + PartialOrd,
        F: Clone,
        //
        T: 'static,
        R: 'static,
        F: 'static,
    {
        Resolve::resolve(Box::new(self))
    }
}

impl<T: Hash, F: 'static> Hash for TransformedValue<T, F> {
    #[inline]
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.1.type_id().hash(state);
        self.0.hash(state);
    }
}

impl<T: Debug, F> Debug for TransformedValue<T, F> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("TransformedValue").field(&self.0).finish()
    }
}

impl<T: PartialEq + 'static, F1: 'static, F2: 'static> PartialEq<TransformedValue<T, F2>>
    for TransformedValue<T, F1>
{
    #[inline]
    fn eq(&self, other: &TransformedValue<T, F2>) -> bool {
        self.0 == other.0 && (&other.1 as &dyn Any).is::<F1>()
    }
}
impl<T: PartialOrd + 'static, F1: 'static, F2: 'static> PartialOrd<TransformedValue<T, F2>>
    for TransformedValue<T, F1>
{
    #[inline]
    fn partial_cmp(&self, other: &TransformedValue<T, F2>) -> Option<Ordering> {
        if (&other.1 as &dyn Any).is::<F1>() {
            return self.0.partial_cmp(&other.0);
        }
        None
    }
}

impl<T: Resolve, R, F: Fn(T::Result) -> R> Resolve for TransformedValue<T, F>
where
    T: Clone + Hash + Debug + PartialOrd,
    F: Clone,
    //
    T: 'static,
    R: 'static,
    F: 'static,
{
    type Result = R;
    stage_default_methods!(is_friendly_with to_context ALL);
    #[inline]
    fn resolve(self: Box<Self>) -> Self::Result {
        (self.1)(Box::new(self.0).resolve())
    }
}

impl<T: Simplify, R> Simplify for TransformedValue<T, R> {
    #[inline]
    fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
        self.0.simplify(file)
    }
}

type Sigma<R> = Context<R>;

pub fn sigma<I: IntoIterator<Item = T>, T, R, F: Fn(T::Result) -> R + Copy>(
    iter: I,
    func: F,
) -> Sigma<R>
where
    T: Resolve + Clone + Hash + Debug + PartialOrd,
    //
    T: 'static,
    R: 'static,
    F: 'static,
{
    Context::Add(
        iter.into_iter()
            .map(|val| {
                Type::Normal(Box::new(TransformedValue(val, func)) as Box<dyn Resolve<Result = R>>)
            })
            .collect(),
    )
}

type Product<R> = Context<R>;

pub fn product<I: IntoIterator<Item = T>, T, R, F: Fn(T::Result) -> R + Copy>(
    iter: I,
    func: F,
) -> Product<R>
where
    T: Resolve + Clone + Hash + Debug + PartialOrd,
    //
    T: 'static,
    R: 'static,
    F: 'static,
{
    Context::Mul(
        iter.into_iter()
            .map(|val| {
                Type::Normal(Box::new(TransformedValue(val, func)) as Box<dyn Resolve<Result = R>>)
            })
            .collect(),
    )
}

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
            Type::Normal(1..=6).collect::<Vec<_>>(),
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
            Type::Normal(3..=7).flip().collect::<Vec<_>>(),
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
    fn basic_sum_repr() {
        let val = sum(Type::Normal(3..=6));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(3 + 4 + 5 + 6)"
        );
    }
    #[test]
    fn basic_mul_repr() {
        let val = mul(Type::Normal(4..=7));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(4 * 5 * 6 * 7)"
        );
    }
    #[test]
    fn basic_sum_compute() {
        let val = sum(Type::Normal(3..=6));
        assert_eq!(val.resolve(), 18);
    }
    #[test]
    fn basic_mul_compute() {
        let val = mul(Type::Normal(4..=7));
        assert_eq!(val.resolve(), 840);
    }
    #[test]
    fn trait_clone() {
        let val1 = sum(Type::Normal(9..=12));
        let val2 = val1.clone();
        assert_eq!(
            val1.repr().expect("failed to represent math context"),
            "(9 + 10 + 11 + 12)"
        );
        assert_eq!(val1.resolve(), 42);
        assert_eq!(
            val2.repr().expect("failed to represent math context"),
            "(9 + 10 + 11 + 12)"
        );
        assert_eq!(val2.resolve(), 42);
    }
    #[test]
    fn basic_repr_compute() {
        let val = mul(Type::Normal(1..=10));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10)"
        );
        assert_eq!(val.resolve(), 3628800);
    }
    #[test]
    fn context_op_method_1() {
        let val1 = sum(vec![Type::Normal(1), Type::Inverse(2), Type::Normal(3)]);
        let val2 = sum(vec![Type::Inverse(1), Type::Normal(2), Type::Inverse(3)]);

        // Add
        // (1 - 2 + 3) + (-1 + 2 - 3)
        // (1 - 2 + 3 - 1 + 2 - 3) // ? op/ctx match: merge both sides
        // (1 - 1 + 2 - 2 + 3 - 3)
        // ()
        let add = val1.clone() + val2.clone();
        assert_eq!(add.repr().expect("failed to represent math context"), "");
        assert_eq!(add.resolve(), 0);

        // Sub
        // (1 - 2 + 3) - (-1 + 2 - 3)
        // (1 - 2 + 3 + 1 - 2 + 3) // ? op/ctx match: merge both sides
        // (1 + 3 + 1 + 3) - (2 + 2) // ? group variants
        // (8) - (4)
        // (4)
        let sub = val1.clone() - val2.clone();
        assert_eq!(
            sub.repr().expect("failed to represent math context"),
            "((1 + 3 + 1 + 3) - (2 + 2))"
        );
        assert_eq!(sub.resolve(), 4);

        let val1 = mul(vec![
            Type::Normal(1.0),
            Type::Inverse(2.0),
            Type::Normal(3.0),
        ]);
        let val2 = mul(vec![
            Type::Inverse(1.0),
            Type::Normal(2.0),
            Type::Inverse(3.0),
        ]);

        // Mul
        // (1 / 2 * 3) * (1/1 * 2 / 3)
        // (1 / 2 * 3 / 1 * 2 / 3) // ? op/ctx match: merge both sides
        // (1 / 1 * 2 / 2 * 3 / 3)
        // ()
        let mul = val1.clone() * val2.clone();
        assert_eq!(mul.repr().expect("failed to represent math context"), "");
        assert_eq!(mul.resolve(), 1.0);

        // Div
        // (1 / 2 * 3) / (1/1 * 2 / 3)
        // (1 / 2 * 3 * 1 / 2 * 3) // ? op/ctx match: merge both sides
        // (1 * 3 * 1 * 3) / (2 * 2) // ? group variants
        // (9) / (4)
        // (2.25)
        let div = val1.clone() / val2.clone();
        assert_eq!(
            div.repr().expect("failed to represent math context"),
            "((1 * 3 * 1 * 3) / (2 * 2))"
        );
        assert_eq!(div.resolve(), 2.25);
    }
    #[test]
    fn context_op_method_2a() {
        let val1 = sum(Type::Normal(2..=3));
        let val2 = mul(Type::Normal(4..=5));

        // Add
        // (2 + 3) + (4 * 5)
        // (2 + 3 + (4 * 5)) // ? rhs' ctx doesn't match the op: merge only lhs
        // (2 + 3 + 20)
        // (25)
        let add = val1.clone() + val2.clone();
        assert_eq!(
            add.repr().expect("failed to represent math context"),
            "(2 + 3 + (4 * 5))"
        );
        assert_eq!(add.resolve(), 25);

        // Sub
        // (2 + 3) - (4 * 5)
        // (2 + 3 - (4 * 5)) // ? rhs' ctx doesn't match the op: merge only lhs
        // ((2 + 3) - (4 * 5)) // ? group variants
        // ((5) - (20))
        // (-15)
        let sub = val1.clone() - val2.clone();
        assert_eq!(
            sub.repr().expect("failed to represent math context"),
            "((2 + 3) - (4 * 5))"
        );
        assert_eq!(sub.resolve(), -15);

        let val1 = mul(Type::Normal(vec![2.0, 3.0].into_iter()));
        let val2 = sum(Type::Normal(vec![4.0, 5.0].into_iter()));

        // Mul
        // (2 * 3) * (4 + 5)
        // (2 * 3 * (4 + 5)) // ? rhs' ctx doesn't match the op: merge only lhs
        // (2 * 3 * 9)
        // (54)
        let mul = val1.clone() * val2.clone();
        assert_eq!(
            mul.repr().expect("failed to represent math context"),
            "(2 * 3 * (4 + 5))"
        );
        assert_eq!(mul.resolve(), 54.0);

        // Div
        // (2 * 3) / (4 + 5)
        // (2 * 3 / (4 + 5)) // ? op/ctx match: merge both sides
        // ((2 * 3) / (4 + 5)) // ? group variants
        // ((6) / (9))
        // (0.66)
        let div = val1.clone() / val2.clone();
        assert_eq!(
            div.repr().expect("failed to represent math context"),
            "((2 * 3) / (4 + 5))"
        );
        assert_eq!(div.resolve(), 0.6666666666666666);
    }
    #[test]
    fn context_op_method_2b() {
        let val1 = mul(Type::Normal(2..=3));
        let val2 = sum(Type::Normal(4..=5));

        // Add
        // (2 * 3) + (4 + 5)
        // ((2 * 3) + 4 + 5) // ? rhs' ctx doesn't match the op: merge only lhs
        // (6 + 4 + 5)
        // (15)
        let add = val1.clone() + val2.clone();
        assert_eq!(
            add.repr().expect("failed to represent math context"),
            "((2 * 3) + 4 + 5)"
        );
        assert_eq!(add.resolve(), 15);

        // Sub
        // (2 * 3) - (4 + 5)
        // ((2 * 3) - 4 - 5) // ? rhs' ctx doesn't match the op: merge only lhs
        // ((2 * 3) - (4 + 5)) // ? group variants
        // ((6) - (9))
        // (-3)
        let sub = val1.clone() - val2.clone();
        assert_eq!(
            sub.repr().expect("failed to represent math context"),
            "((2 * 3) - (4 + 5))"
        );
        assert_eq!(sub.resolve(), -3);

        let val1 = sum(Type::Normal(vec![2.0, 3.0].into_iter()));
        let val2 = mul(Type::Normal(vec![4.0, 5.0].into_iter()));

        // Mul
        // (2 + 3) * (4 * 5)
        // ((2 + 3) * 4 * 5) // ? rhs' ctx doesn't match the op: merge only lhs
        // (5 * 4 * 5)
        // (100)
        let mul = val1.clone() * val2.clone();
        assert_eq!(
            mul.repr().expect("failed to represent math context"),
            "((2 + 3) * 4 * 5)"
        );
        assert_eq!(mul.resolve(), 100.0);

        // Div
        // (2 + 3) / (4 * 5)
        // ((2 + 3) / 4 / 5) // ? op/ctx match: merge both sides
        // ((2 + 3) / (4 * 5)) // ? group variants
        // (5 / (4 * 5))
        // ((5) / (20))
        // (0.25)
        let div = val1.clone() / val2.clone();
        assert_eq!(
            div.repr().expect("failed to represent math context"),
            "((2 + 3) / (4 * 5))"
        );
        assert_eq!(div.resolve(), 0.25);
    }
    #[test]
    fn context_op_method_3() {
        let val1 = mul(Type::Normal(2..=3));
        let val2 = mul(Type::Normal(4..=5));

        // Add
        // (2 * 3) + (4 * 5)
        // ((2 * 3) + (4 * 5)) // ? neither side's ctx matches op: insert as-is
        // (6 + 20)
        // (26)
        let add = val1.clone() + val2.clone();
        assert_eq!(
            add.repr().expect("failed to represent math context"),
            "((2 * 3) + (4 * 5))"
        );
        assert_eq!(add.resolve(), 26);

        // Sub
        // (2 * 3) - (4 * 5)
        // ((2 * 3) - (4 * 5)) // ? neither side's ctx matches op: insert as-is
        // ((2 * 3) - (4 * 5)) // ? group variants
        // ((6) - (20))
        // (-14)
        let sub = val1.clone() - val2.clone();
        assert_eq!(
            sub.repr().expect("failed to represent math context"),
            "((2 * 3) - (4 * 5))"
        );
        assert_eq!(sub.resolve(), -14);

        let val1 = sum(vec![
            Type::Normal(1.0),
            Type::Inverse(2.0),
            Type::Normal(3.0),
        ]);
        let val2 = sum(vec![
            Type::Inverse(1.0),
            Type::Normal(2.0),
            Type::Inverse(3.0),
        ]);

        // Mul
        // (1 - 2 + 3) * (-1 + 2 - 3)
        // ((1 - 2 + 3) * (-1 + 2 - 3)) // ? neither side's ctx matches op: insert as-is
        // (((1 + 3) - 2) * (2 - (1 + 3))) // ? group variants
        // (((4) - 2) * (2 - (4)))
        // ((2) * (-2))
        // (-4)
        let mul = val1.clone() * val2.clone();
        assert_eq!(
            mul.repr().expect("failed to represent math context"),
            "(((1 + 3) - 2) * (2 - (1 + 3)))"
        );
        assert_eq!(mul.resolve(), -4.0);

        // Div
        // (1 - 2 + 3) / (-1 + 2 - 3)
        // ((1 - 2 + 3) / (-1 + 2 - 3)) // op/ctx mismatch: no-op
        // (((1 + 3) - 2) / (2 - (1 + 3))) ? group variants
        // (((4) - 2) / (2 - (4)))
        // ((2) / (-2))
        // (-1)
        let mul = val1.clone() / val2.clone();
        assert_eq!(
            mul.repr().expect("failed to represent math context"),
            "(((1 + 3) - 2) / (2 - (1 + 3)))"
        );
        assert_eq!(mul.resolve(), -1.0);
    }
    #[test]
    fn transformed_value() {
        let val = TransformedValue(50, |val| val + 50);
        assert_eq!(format!("{:?}", val), "TransformedValue(50)");
        assert_eq!(val.repr().expect("failed to represent math context"), "50");
        assert_eq!(val.resolve(), 100);
    }
    #[test]
    fn transformed_eq() {
        let val1 = TransformedValue(50, |val: u8| val + 50);
        let val2 = TransformedValue(50, |val: u8| val + 50);
        assert_ne!(val1, val2);

        let func = |val: u8| val + 10;
        let val1 = TransformedValue(50, func);
        let val2 = TransformedValue(50, func);
        assert_eq!(val1, val2);
    }
    #[test]
    fn transformed_unshared_cmp() {
        let val1 = TransformedValue(50, |val| val + 50); // 100
        let val2 = TransformedValue(80, |val| val + 11); // 91
        assert!(!(val1 < val2)); // can't compare
        assert!(val1 != val2); // can't compare
        assert!(!(val1 > val2)); // can't compare
        assert_eq!(val1.partial_cmp(&val2), None); // can't compare
        assert!(val1.resolve() > val2.resolve());

        let val1 = TransformedValue(60, |val| val + 12); // 72
        let val2 = TransformedValue(32, |val| val + 43); // 75
        assert!(!(val1 < val2)); // can't compare
        assert!(val1 != val2); // can't compare
        assert!(!(val1 > val2)); // can't compare
        assert_eq!(val1.partial_cmp(&val2), None); // can't compare
        assert!(val1.resolve() < val2.resolve());
    }
    #[test]
    fn transformed_shared_cmp() {
        let func = |x| x + 10;
        let val1 = TransformedValue(50, func); // 60
        let val2 = TransformedValue(80, func); // 90
        assert!(val1 < val2); // 50 < 80
        assert!(val1 != val2); // 50 != 80
        assert!(!(val1 > val2)); // !(50 > 80)
        assert_eq!(val1.partial_cmp(&val2), Some(std::cmp::Ordering::Less));
        assert!(val1.resolve() < val2.resolve()); // 60 < 90

        let func = |x| x + 64;
        let val1 = TransformedValue(22, func); // 86
        let val2 = TransformedValue(22, func); // 86
        assert!(!(val1 < val2)); // !(22 < 22)
        assert!(val1 == val2); // 22 == 22
        assert!(!(val1 > val2)); // !(22 > 22)
        assert_eq!(val1.partial_cmp(&val2), Some(std::cmp::Ordering::Equal));
        assert!(val1.resolve() == val2.resolve()); // 86 == 86

        let func = |x| x + 22;
        let val1 = TransformedValue(60, func); // 82
        let val2 = TransformedValue(32, func); // 54
        assert!(!(val1 < val2)); // !(60 < 32)
        assert!(val1 != val2); // 60 != 32
        assert!(val1 > val2); // 60 > 32
        assert_eq!(val1.partial_cmp(&val2), Some(std::cmp::Ordering::Greater));
        assert!(val1.resolve() > val2.resolve()); // 82 > 54
    }
    #[test]
    fn sigma_basic() {
        let val = sigma(1..=10, |val| val);
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(1 + 2 + 3 + 4 + 5 + 6 + 7 + 8 + 9 + 10)"
        );
        assert_eq!(val.resolve(), 55);
    }
    #[test]
    fn sigma_transform() {
        // ∑(1 → 5) [x => x ^ 2]
        // = (1 ^ 2) + (2 ^ 2) + (3 ^ 2) + (4 ^ 2) + (5 ^ 2)
        // = (1) + (4) + (9) + (16) + (25)
        // = 55
        let val = sigma(1..=5u8, |val| val.pow(2));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(1 + 2 + 3 + 4 + 5)"
        );
        assert_eq!(val.resolve(), 55);
    }
    #[test]
    fn sigma_add_unshared() {
        // (∑(1 → 3) [x => x ^ 2]) + (∑(4 → 5) [x => x + 20])
        // = ((1 ^ 2) + (2 ^ 2) + (3 ^ 2)) + ((4 + 20) + (5 + 20))
        // = ((1) + (4) + (9)) + ((24) + (25))
        // = (1 + 4 + 9) + (24 + 25)
        // = (14) + (49)
        // = (14 + 49)
        // = 63

        let val1 = sigma(1..=3u8, |val| val.pow(2));
        let val2 = sigma(4..=5u8, |val| val + 20);
        let val3 = val1 + val2;
        assert_eq!(
            val3.repr().expect("failed to represent math context"),
            "(1 + 2 + 3 + (4 + 5))"
        );
        assert_eq!(val3.resolve(), 63);
    }
    #[test]
    fn sigma_add_shared() {
        // func := x => x * 2
        // (∑(1 → 3) [func]) + (∑(4 → 5) [func])
        // = (∑(1 → 5) [x => x * 2])
        // = ((1 * 2) + (2 * 2) + (3 * 2) + (4 * 2) + (5 * 2))
        // = ((2) + (4) + (6) + (8) + (10))
        // = (2 + 4 + 6 + 8 + 10)
        // = 30

        let func = |x| x * 2;
        let val1 = sigma(1..=3, func);
        let val2 = sigma(4..=5, func);
        let val3 = val1 + val2;
        assert_eq!(
            val3.repr().expect("failed to represent math context"),
            "(1 + 2 + 3 + 4 + 5)"
        );
        assert_eq!(val3.resolve(), 30);
    }
    #[test]
    fn product_basic() {
        let val = product(1..=10, |val| val);
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5 * 6 * 7 * 8 * 9 * 10)"
        );
        assert_eq!(val.resolve(), 3628800);
    }
    #[test]
    fn product_transform() {
        // ∏(1 → 5) [x => x ^ 2]
        // = (1 ^ 2) * (2 ^ 2) * (3 ^ 2) * (4 ^ 2) * (5 ^ 2)
        // = (1) * (4) * (9) * (16) * (25)
        // = 14400
        let val = product(1..=5u16, |val| val.pow(2));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );
        assert_eq!(val.resolve(), 14400);
    }
    #[test]
    fn product_mul_unshared() {
        // (∏(1 → 3) [x => x + 4]) * (∏(4 → 5) [x => x + 3])
        // = ((1 + 4) * (2 + 4) * (3 + 4)) * ((4 + 3) * (5 + 3))
        // = ((5) * (6) * (7)) * ((7) * (8))
        // = (5 * 6 * 7) * (7 * 8)
        // = (210) * (56)
        // = (210 * 56)
        // = 11760

        let val1 = product(1..=3, |val| val + 4);
        let val2 = product(4..=5, |val| val + 3);
        let val3 = val1 * val2;
        assert_eq!(
            val3.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * (4 * 5))"
        );
        assert_eq!(val3.resolve(), 11760);
    }
    #[test]
    fn product_mul_shared() {
        // func := x => x + 55
        // (∑(1 → 3) [func]) + (∑(4 → 5) [func])
        // = (∑(1 → 5) [x => x + 55])
        // = ((1 + 55) * (2 + 55) * (3 + 55) * (4 + 55) * (5 + 55))
        // = ((56) * (57) * (58) * (59) * (60))
        // = (56 * 57 * 58 * 59 * 60)
        // = 655381440

        let func = |x| x + 55;
        let val1 = product(1..=3, func);
        let val2 = product(4..=5, func);
        let val3 = val1 * val2;
        assert_eq!(
            val3.repr().expect("failed to represent math context"),
            "(1 * 2 * 3 * 4 * 5)"
        );
        assert_eq!(val3.resolve(), 655381440);
    }
    #[test]
    fn repr_chars() {
        let val = sum(Type::Normal('a'..='f'));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(a + b + c + d + e + f)"
        );
    }
    #[test]
    fn repr_strings() {
        let val = mul(vec![
            Type::Normal("val1".to_string()),
            Type::Normal("val2".to_string()),
            Type::Normal("val3".to_string()),
            Type::Normal("val4".to_string()),
        ]);
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(val1 * val2 * val3 * val4)"
        );
    }
    #[test]
    fn repr_strings_mixed() {
        let val = sum(vec![
            Type::Normal(mul(Type::Normal('a'..='c'))),
            Type::Normal(mul(vec![
                Type::Normal("val1".to_string()),
                Type::Normal("val2".to_string()),
                Type::Normal("val3".to_string()),
            ])),
        ]);
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "((a * b * c) + (val1 * val2 * val3))"
        );
    }
    #[test]
    fn op_prim_rhs() {
        let val = sum(Type::Normal(3..=5)) + 6_i32;
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(3 + 4 + 5 + 6)"
        );

        let val = sum(Type::Normal(3..=5)) * 6_i32;
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "((3 + 4 + 5) * 6)"
        );

        let val = mul(Type::Normal(3..=5)) * 6_i32;
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(3 * 4 * 5 * 6)"
        );

        let val = mul(Type::Normal(3..=5)) + 6_i32;
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "((3 * 4 * 5) + 6)"
        );
    }
    #[test]
    fn op_prim_lhs() {
        let val = 2_i32 + sum(Type::Normal(3..=5));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(2 + 3 + 4 + 5)"
        );

        let val = 2_i32 * sum(Type::Normal(3..=5));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(2 * (3 + 4 + 5))"
        );

        let val = 2_i32 * mul(Type::Normal(3..=5));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(2 * 3 * 4 * 5)"
        );

        let val = 2_i32 + mul(Type::Normal(3..=5));
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(2 + (3 * 4 * 5))"
        );
    }
    #[test]
    fn to_context() {
        // nil transform
        assert_eq!(5_u8.to_context(), Context::Nil(Box::new(5_u8)));
        assert_eq!(20_usize.to_context(), Context::Nil(Box::new(20_usize)));

        let val = 3.to_context() + 5.to_context();
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(3 + 5)"
        );

        let val = 3.to_context() * 5.to_context();
        assert_eq!(
            val.repr().expect("failed to represent math context"),
            "(3 * 5)"
        );

        assert_ne!(
            TransformedValue(10, |val| val).to_context(),
            Context::Nil(Box::new(TransformedValue(10, |val| val)))
        );

        let func = |val| val;
        assert_eq!(
            TransformedValue(10, func).to_context(),
            Context::Nil(Box::new(TransformedValue(10, func)))
        );

        // no-op transform
        assert_eq!(
            sum(Type::Normal(3..=5)).to_context(),
            Context::Add(vec![
                Type::Normal(Box::new(3)),
                Type::Normal(Box::new(4)),
                Type::Normal(Box::new(5))
            ])
        );

        assert_eq!(
            mul(Type::Normal(8..=10)).to_context(),
            Context::Mul(vec![
                Type::Normal(Box::new(8)),
                Type::Normal(Box::new(9)),
                Type::Normal(Box::new(10))
            ])
        );
    }
    #[test]
    fn test_ctx_macro() {
        // define a & b within this context
        ctx!(a = 10, b = 20);
        let c = a + b;
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(10 + 20)"
        );
        assert_eq!(c.resolve(), 30);

        // define a, b & c within this context
        ctx!(a = 10, b = 20, c = a + b);
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(10 + 20)"
        );
        assert_eq!(c.resolve(), 30);

        // multi-define a & b to 20
        ctx!((a, b) = 20, c = a + b);
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(20 + 20)"
        );
        assert_eq!(c.resolve(), 40);

        // privatize all variables
        ctx!({a = 10, b = 20, c = a + b} {
            assert_eq!(
                c.repr().expect("failed to represent math context"),
                "(10 + 20)"
            );
            assert_eq!(c.resolve(), 30);
        });

        // privately multi-define a & b to 20
        ctx!({(a, b) = 20, c = a + b} {
            assert_eq!(
                c.repr().expect("failed to represent math context"),
                "(20 + 20)"
            );
            assert_eq!(c.resolve(), 40);
        });

        // privatize a & b, export result
        let c = ctx!({a = 10, b = 20} a + b);
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(10 + 20)"
        );
        assert_eq!(c.resolve(), 30);

        // declare variables as Contexts
        ctx!(a, b, c);
        a = 10.to_context();
        b = 20.to_context();
        c = a + b;
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(10 + 20)"
        );
        assert_eq!(c.resolve(), 30);

        // contextify expressions
        let a = ctx!({ 10 });
        let b = ctx!({ 20 });
        let c = a + b;
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(10 + 20)"
        );
        assert_eq!(c.resolve(), 30);

        // destructure tuple expression
        let (a, b) = ctx!({ (10, 20) });
        let c = a + b;
        assert_eq!(
            c.repr().expect("failed to represent math context"),
            "(10 + 20)"
        );
        assert_eq!(c.resolve(), 30);
    }
    #[test]
    fn test_helper_macros() {
        // (1 + 2 + (3 * 4) + 5 + (6 + 7))
        let eqn = add![
            n!(1),
            n!(2),
            n!(mul![n!(3), n!(4)]),
            n!(5),
            n!(add![n!(6), n!(7)])
        ];
        assert_eq!(
            eqn.repr().expect("failed to represent math context"),
            "(1 + 2 + (3 * 4) + 5 + (6 + 7))"
        );
        assert_eq!(eqn.resolve(), 33);

        // (a - b + c - d)
        // (a + c) - (b + d)
        assert_eq!(
            add![n!('a'), i!('b'), n!('c'), i!('d')]
                .repr()
                .expect("failed to represent math context"),
            "((a + c) - (b + d))"
        );
    }
}
