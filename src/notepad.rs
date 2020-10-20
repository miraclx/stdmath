use super::{core::Type, One, Zero};
use std::{
    any::Any,
    cmp::{Eq, Ordering, PartialEq},
    fmt::{self, Debug, Write},
    hash::{Hash, Hasher},
};

pub trait Simplify {
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result;
}

pub trait Resolve: Simplify {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;

    // methods needed for dynamicism
    fn as_any(&self) -> &dyn Any;
    fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering>;
    fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
        unimplemented!()
    }
    fn _debug(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
    fn _hash(&self, _state: &mut dyn Hasher) {
        unimplemented!()
    }
}

enum Identity {
    Add,
    Mul,
    Nil,
}

impl<X> PartialEq<dyn Resolve<Result = X>> for dyn Resolve<Result = X> {
    fn eq(&self, other: &dyn Resolve<Result = X>) -> bool {
        if let Some(Ordering::Equal) = self._cmp(other) {
            return true;
        }
        false
    }
}

impl<X> Eq for dyn Resolve<Result = X> {}

impl<X> PartialOrd<dyn Resolve<Result = X>> for dyn Resolve<Result = X> {
    fn partial_cmp(&self, other: &dyn Resolve<Result = X>) -> Option<Ordering> {
        self._cmp(other)
    }
}

impl<X> Debug for dyn Resolve<Result = X> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._debug(f)
    }
}

impl<X> Clone for Box<dyn Resolve<Result = X>> {
    fn clone(&self) -> Self {
        self._clone()
    }
}

impl<X> Hash for Box<dyn Resolve<Result = X>> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self._hash(state);
    }
}

macro_rules! stage_default_methods {
    () => {};
    (ALL) => {
        stage_default_methods!(as_any _cmp _debug _clone _hash);
    };
    (as_any $($rest:tt)*) => {
        #[inline]
        fn as_any(&self) -> &dyn Any {
            self
        }
        stage_default_methods!($($rest)*);
    };
    (_cmp $($rest:tt)*) => {
        #[inline]
        fn _cmp(&self, other: &dyn Resolve<Result = Self::Result>) -> Option<Ordering> {
            other
                .as_any()
                .downcast_ref::<Self>()
                .map_or(None, |other| PartialOrd::partial_cmp(self, other))
        }
        stage_default_methods!($($rest)*);
    };
    (_debug $($rest:tt)*) => {
        #[inline]
        fn _debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            Debug::fmt(self, f)
        }
        stage_default_methods!($($rest)*);
    };
    (_clone $($rest:tt)*) => {
        #[inline]
        fn _clone(&self) -> Box<dyn Resolve<Result = Self::Result>> {
            Box::new(self.clone()) as Box<dyn Resolve<Result = Self::Result>>
        }
        stage_default_methods!($($rest)*);
    };
    (_hash $($rest:tt)*) => {
        #[inline]
        fn _hash(&self, mut state: &mut dyn Hasher) {
            self.hash(&mut state)
        }
        stage_default_methods!($($rest)*);
    };
}

macro_rules! bulk_impl_traits {
    (@ [$($methods:tt)+] $type:ty) => {
        impl Resolve for $type {
            type Result = $type;
            stage_default_methods!($($methods)+);
            #[inline]
            fn resolve(self: Box<Self>) -> Self::Result {
                *self
            }
        }
        impl Simplify for $type {
            #[inline]
            fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
                write!(file, "{:?}", self)
            }
        }
    };
    (nohash($($type:ty),+)) => {
        $(bulk_impl_traits!(@ [as_any _cmp _debug _clone] $type);)+
    };
    ($($type:ty),+) => {
        $(bulk_impl_traits!(@ [ALL] $type);)+
    }
}

bulk_impl_traits!(i8, i16, i32, i64, isize);
bulk_impl_traits!(u8, u16, u32, u64, usize);
bulk_impl_traits!(nohash(f32, f64));
bulk_impl_traits!(i128, u128);

impl<T: 'static, X> Resolve for Box<T>
where
    T: Resolve<Result = X> + Clone + Hash + Debug + PartialOrd,
{
    type Result = X;
    stage_default_methods!(ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        (*self).resolve()
    }
}

impl<T> Simplify for Box<T>
where
    T: Simplify,
{
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
        (*self).simplify(file)
    }
}

#[derive(Clone, Hash, Debug, PartialEq, PartialOrd)]
pub enum Context<R> {
    Add(Vec<Type<Box<dyn Resolve<Result = R>>>>),
    Mul(Vec<Type<Box<dyn Resolve<Result = R>>>>),
}

impl<R: 'static> Context<R> {
    fn resolve(self) -> R
    where
        R: Clone + Hash + Debug + PartialOrd,
        //
        R: One
            + Zero
            + std::ops::Mul
            + std::ops::Add
            + std::ops::Div<Output = R>
            + std::ops::Sub<Output = R>,
    {
        Box::new(self).resolve()
    }
}

impl<R: 'static> Resolve for Context<R>
where
    R: Clone + Hash + Debug + PartialOrd,
    //
    R: One
        + Zero
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
{
    type Result = R;
    stage_default_methods!(ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        let (vec, default, [normal_op, inverse_op]): (_, fn() -> R, [fn(R, R) -> R; 2]) =
            match *self {
                Context::Add(vec) => (vec, || R::zero(), [std::ops::Add::add, std::ops::Sub::sub]),
                Context::Mul(vec) => (vec, || R::one(), [std::ops::Mul::mul, std::ops::Div::div]),
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

impl<R> Simplify for Context<R> {
    fn simplify(self: Box<Self>, file: &mut dyn Write) -> std::fmt::Result {
        todo!()
    }
}

pub fn main() {
    let vec: Vec<Type<Box<dyn Resolve<Result = i32>>>> = vec![
        Type::Normal(Box::new(10)),
        Type::Normal(Box::new(Context::Mul(vec![
            Type::Normal(Box::new(10)),
            Type::Normal(Box::new(13)),
        ]))),
    ];
    let a = Context::Add(vec);
    println!("{:?}", a.resolve());
}
