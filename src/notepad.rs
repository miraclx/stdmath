use super::{
    core::{Flippable, Type},
    exclude::ExcludedIteratorExt,
    One, Zero,
};
use std::{
    any::Any,
    cmp::{Eq, Ordering, PartialEq},
    fmt::{self, Debug, Write},
    hash::{Hash, Hasher},
};

pub trait Simplify {
    fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result;
    fn repr_into(&self, file: &mut dyn Write) -> std::fmt::Result {
        Simplify::simplify(self, file)
    }
    fn repr(&self) -> Result<String, std::fmt::Error> {
        let mut file = String::new();
        self.repr_into(&mut file)?;
        Ok(file)
    }
}

pub trait Resolve: Simplify {
    type Result;
    fn resolve(self: Box<Self>) -> Self::Result;

    // methods needed for dynamicism
    fn as_any(&self) -> &dyn Any;
    fn is_friendly_with(&self, other: &dyn Resolve<Result = Self::Result>) -> bool;
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
    (is_friendly_with $($rest:tt)*) => {
        #[inline]
        fn is_friendly_with(&self, other: &dyn Resolve<Result = Self::Result>) -> bool {
            other.as_any().is::<Self>()
        }
        stage_default_methods!($($rest)*);
    };
    (is_friendly_with_all $($rest:tt)*) => {
        #[inline]
        fn is_friendly_with(&self, _other: &dyn Resolve<Result = Self::Result>) -> bool {
            true
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
    (@ [$($methods:tt)+] $type:ty {$($items:item)*}) => {
        impl Resolve for $type {
            type Result = $type;
            stage_default_methods!($($methods)+);
            stage_default_methods!(is_friendly_with_all);
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
                stage_default_methods!(is_friendly_with_all ALL);
                fn resolve(self: Box<Self>) -> Self::Result {
                    unimplemented!("cannot resolve strings")
                }
            }
            impl Simplify for $type {
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

pub enum Context<R> {
    Add(Vec<Type<Box<dyn Resolve<Result = R>>>>),
    Mul(Vec<Type<Box<dyn Resolve<Result = R>>>>),
}

impl<R: 'static> PartialEq for Context<R> {
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
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        let id_me = unsafe { *(&std::mem::discriminant(self) as *const _ as *const usize) };
        let id_you = unsafe { *(&std::mem::discriminant(other) as *const _ as *const usize) };
        if id_me == id_you {
            self.get_ref().partial_cmp(other.get_ref())
        } else {
            id_me.partial_cmp(&id_you)
        }
    }
}

impl<R: 'static> Hash for Context<R> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.get_ref().hash(state)
    }
}

impl<R> Debug for Context<R> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (name, vec) = match self {
            Context::Add(vec) => ("Add", vec),
            Context::Mul(vec) => ("Mul", vec),
        };
        f.debug_tuple(name).field(vec).finish()
    }
}

impl<R> Clone for Context<R> {
    fn clone(&self) -> Self {
        match self {
            Context::Add(vec) => Context::Add(vec.clone()),
            Context::Mul(vec) => Context::Mul(vec.clone()),
        }
    }
}

impl<R: 'static> Context<R> {
    #[inline]
    pub fn resolve(self) -> R
    where
        R: One
            + Zero
            + std::ops::Mul
            + std::ops::Add
            + std::ops::Div<Output = R>
            + std::ops::Sub<Output = R>,
    {
        Box::new(self).resolve()
    }
    #[inline]
    pub fn dump(self) -> Vec<Type<Box<dyn Resolve<Result = R>>>> {
        match self {
            Context::Add(vec) => vec,
            Context::Mul(vec) => vec,
        }
    }
    #[inline]
    pub fn get_ref(&self) -> &Vec<Type<Box<dyn Resolve<Result = R>>>> {
        match self {
            Context::Add(vec) => vec,
            Context::Mul(vec) => vec,
        }
    }
    #[inline]
    pub fn is_additive(&self) -> bool {
        if let Context::Add(_) = self {
            return true;
        }
        false
    }
}

impl<R: 'static> Resolve for Context<R>
where
    R: One
        + Zero
        + std::ops::Mul
        + std::ops::Add
        + std::ops::Div<Output = R>
        + std::ops::Sub<Output = R>,
{
    type Result = R;
    stage_default_methods!(is_friendly_with_all ALL);
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

impl<R: 'static> Simplify for Context<R> {
    fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
        let (is_additive, vec) = (self.is_additive(), self.get_ref());
        let (mut normal, mut inverse) = (None, None);
        for item in vec {
            let is_inverted = item.is_inverted();
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

macro_rules! impl_ops {
    ($($trait:path[fn $method:ident($lhs_ident:ident, $rhs_ident:ident) -> $final_variant:path] => {$($rules:tt)+}),+) => {
        $(
            impl<R: 'static> $trait for Context<R>
            where
                R: One
                    + Zero
                    + std::ops::Mul
                    + std::ops::Add
                    + std::ops::Div<Output = R>
                    + std::ops::Sub<Output = R>,
            {
                type Output = Context<R>;
                fn $method(self, rhs: Self) -> Self::Output {
                    let ($lhs_ident, $rhs_ident) = (self, rhs);
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
    (dump_items $side:ident) => {$side.dump().into_iter()};
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

impl<T, R, F: Fn(T) -> R + Copy> TransformedValue<T, F> {
    #[inline]
    pub fn resolve(self) -> R
    where
        T: Simplify + Clone + Hash + Debug + PartialOrd,
        //
        T: 'static,
        R: 'static,
        F: 'static,
    {
        Resolve::resolve(Box::new(self))
    }
}

impl<T: Hash, F: 'static> Hash for TransformedValue<T, F> {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        self.1.type_id().hash(state);
        self.0.hash(state);
    }
}

impl<T: Debug, F> Debug for TransformedValue<T, F> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("TransformedValue").field(&self.0).finish()
    }
}

impl<T: PartialEq + 'static, F1: 'static, F2: 'static> PartialEq<TransformedValue<T, F2>>
    for TransformedValue<T, F1>
{
    fn eq(&self, other: &TransformedValue<T, F2>) -> bool {
        self.0 == other.0 && (&other.1 as &dyn Any).is::<F1>()
    }
}
impl<T: PartialOrd + 'static, F1: 'static, F2: 'static> PartialOrd<TransformedValue<T, F2>>
    for TransformedValue<T, F1>
{
    fn partial_cmp(&self, other: &TransformedValue<T, F2>) -> Option<Ordering> {
        if (&other.1 as &dyn Any).is::<F1>() {
            return self.0.partial_cmp(&other.0);
        }
        None
    }
}

impl<T, R, F: Fn(T) -> R + Copy> Resolve for TransformedValue<T, F>
where
    T: Simplify + Clone + Hash + Debug + PartialOrd,
    //
    T: 'static,
    R: 'static,
    F: 'static,
{
    type Result = R;
    stage_default_methods!(is_friendly_with ALL);
    fn resolve(self: Box<Self>) -> Self::Result {
        (self.1)(self.0)
    }
}

impl<T: Simplify, R> Simplify for TransformedValue<T, R> {
    fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
        self.0.simplify(file)
    }
}

type Sigma<R> = Context<R>;

fn sigma<I: IntoIterator<Item = T>, T, R, F: Fn(T) -> R + Copy>(iter: I, func: F) -> Sigma<R>
where
    T: Simplify + Clone + Hash + Debug + PartialOrd,
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

fn product<I: IntoIterator<Item = T>, T, R, F: Fn(T) -> R + Copy>(iter: I, func: F) -> Product<R>
where
    T: Simplify + Clone + Hash + Debug + PartialOrd,
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
        let val1 = TransformedValue(50, |val: u8| val + 50); // 100
        let val2 = TransformedValue(80, |val: u8| val + 11); // 91
        assert!(!(val1 < val2)); // can't compare
        assert!(val1 != val2); // can't compare
        assert!(!(val1 > val2)); // can't compare
        assert_eq!(val1.partial_cmp(&val2), None); // can't compare
        assert!(val1.resolve() > val2.resolve());

        let val1 = TransformedValue(60, |val: u8| val + 12); // 72
        let val2 = TransformedValue(32, |val: u8| val + 43); // 75
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

        let val1 = sigma(1..=3, |val: u8| val.pow(2));
        let val2 = sigma(4..=5, |val| val + 20);
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
}
