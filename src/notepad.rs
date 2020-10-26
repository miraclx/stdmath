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
    fn is_friendly_with(&self, other: &dyn Resolve<Result = Self::Result>) -> bool;

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
    (@ [$($methods:tt)+] $type:ty) => {
        impl Resolve for $type {
            type Result = $type;
            stage_default_methods!($($methods)+);
            stage_default_methods!(is_friendly_with_all);
            #[inline]
            fn resolve(self: Box<Self>) -> Self::Result {
                *self
            }
        }
        impl Simplify for $type {
            #[inline]
            fn simplify(&self, file: &mut dyn Write) -> std::fmt::Result {
                write!(file, "{:?}", self)
            }
        }
    };
    (nohash($($type:ty),+)) => {
        $(bulk_impl_traits!(@ [as_any _cmp _debug _clone] $type);)+
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
        $(bulk_impl_traits!(@ [ALL] $type);)+
    }
}

bulk_impl_traits!(i8, i16, i32, i64, isize);
bulk_impl_traits!(u8, u16, u32, u64, usize);
bulk_impl_traits!(nohash(f32, f64));
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
    std::ops::Sub[fn sub(lhs, rhs) -> Context::Add] => { default_inverse(+, lhs, rhs) },
    std::ops::Mul[fn mul(lhs, rhs) -> Context::Mul] => { default_normal(*, lhs, rhs) },
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

pub fn main() {
    let a = sum(vec![
        Type::Normal(mul(vec![Type::Normal(10)])),
        Type::Normal(mul(vec![Type::Normal(10), Type::Normal(13)])),
    ]);
    println!(
        "{:?}",
        a.clone().repr().expect("failed to represent math context")
    );
    println!(" = {:?}", a.resolve());

    let val1 = sum(vec![
        Type::Normal(mul(vec![Type::Normal(10)])),
        Type::Normal(mul(vec![Type::Normal(10), Type::Normal(13)])),
    ]);
    let val2 = mul(vec![
        Type::Normal(sum(vec![Type::Normal(10)])),
        Type::Normal(sum(vec![Type::Normal(10), Type::Normal(13)])),
    ]);

    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // test addition method 1
    //  merge two contexts if both match the operation
    //  i.e two additive contexts are merged with an additive operation

    // Example
    //  input:
    //   (5 - 10 - 6) + (-10 + 5 + 6)
    //  1: exclude inverse matches and merge
    //   (5 - 10 - 10 + 5)
    //  2: group variants
    //   (5 + 5) - (10 + 10)
    //  result:
    //   -10
    let val1 = sum(vec![Type::Normal(5), Type::Inverse(10), Type::Inverse(6)]);
    let val2 = sum(vec![Type::Inverse(10), Type::Normal(5), Type::Normal(6)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // test addition method 2
    //  include a side as-is into the result if the variant of the context
    //  doesn't conform to the operation
    //  i.e adding a mul context to an add will include the mul as an
    //      item within the add context
    //    > add[n(a), i(b)] + mul[n(c), i(d)]
    //    = add[n(a), i(b), n(mul[n(c), i(d)])]
    //    > mul[n(a), i(b)] + add[n(c), i(b)]
    //    = mul[n(a), i(b), n(add[n(c), i(b)])]

    // Example 1:
    //  input:
    //   (2 + 3) + (4 * 5)
    //  1: exclude rhs from lhs if present else merge rhs into lhs
    //   (2 + 3 + (4 * 5))
    //  2: group variants
    //   (2 + 3 + (4 * 5))
    //  result:
    //   25
    let val1 = sum(vec![Type::Normal(2), Type::Normal(3)]);
    let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // Example 2:
    //  input:
    //   (2 * 3) + (4 + 5)
    //  1: exclude lhs from rhs if present else merge lhs into rhs
    //   ((2 * 3) + 4 + 5)
    //  2: group variants
    //   ((2 * 3) + 4 + 5)
    //  result:
    //   15
    let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
    let val2 = sum(vec![Type::Normal(4), Type::Normal(5)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());

    // test addition method 3
    //  include both sides into the result as-is if they dont match the op
    //  i.e adding a mul context to a mul will include both as-is into the result
    //    > mul[ n(a), i(b) ] + mul[ n(c), i(d) ]
    //    = add[
    //        n(mul[ n(a), i(b) ]),
    //        n(mul[ n(c), i(d) ])
    //      ]

    // Example
    //  input:
    //   (2 * 3) + (4 * 5)
    //  1: exclude rhs from lhs if present else merge rhs into lhs
    //   ((2 * 3) + (4 * 5))
    //  2: group variants
    //   ((2 * 3) + (4 * 5))
    //  result:
    //   26
    let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
    let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
    let val3 = val1 + val2;
    println!(
        "{:?}",
        val3.clone()
            .repr()
            .expect("failed to represent math context")
    );
    println!(" = {:?}", val3.resolve());
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
    fn context_add_method_1() {
        // (1 - 2 + 3) + (-1 + 2 - 3)
        // ? 1: exclude inverse matches and merge
        //  (1 - 2 + 3 - 1 + 2 - 3)
        //  (1 - 1 + 2 - 2 + 3 - 3)
        //  ()
        // ? 2: group variants
        //  ()
        // ? result:
        //  0
        let val1 = sum(vec![Type::Normal(1), Type::Inverse(2), Type::Normal(3)]);
        let val2 = sum(vec![Type::Inverse(1), Type::Normal(2), Type::Inverse(3)]);
        let val3 = val1 + val2;
        assert_eq!(val3.repr().expect("failed to represent math context"), "");
        assert_eq!(val3.resolve(), 0);
    }
    #[test]
    fn context_add_method_2a() {
        // (2 + 3) + (4 * 5)
        // ? 1: exclude rhs from lhs if present else merge rhs into lhs
        //  (2 + 3 + (4 * 5))
        // ? 2: group variants
        //  (2 + 3 + (4 * 5))
        // ? result:
        //  25
        let val1 = sum(vec![Type::Normal(2), Type::Normal(3)]);
        let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
        let val3 = val1 + val2;
        assert_eq!(
            val3.repr().expect("failed to represent math context"),
            "(2 + 3 + (4 * 5))"
        );
        assert_eq!(val3.resolve(), 25);
    }
    #[test]
    fn context_add_method_2b() {
        // (2 * 3) + (4 + 5)
        // ? 1: exclude rhs from lhs if present else merge rhs into lhs
        //  ((2 * 3) + 4 + 5)
        // ? 2: group variants
        //  ((2 * 3) + 4 + 5)
        // ? result:
        //  15
        let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
        let val2 = sum(vec![Type::Normal(4), Type::Normal(5)]);
        let val3 = val1 + val2;
        match val3
            .repr()
            .expect("failed to represent math context")
            .as_str()
        {
            "((2 * 3) + 4 + 5)" | "((2 * 3) + 5 + 4)" => {}
            // fixme: asserting between multiple matches
            val => panic!(
                r#"assertion failed: `(left == right)`
  left: `{:?}`,
 right: `"((2 * 3) + 4 + 5)" or "((2 * 3) + 5 + 4)"`"#,
                val
            ),
        }
        assert_eq!(val3.resolve(), 15);
    }
    #[test]
    fn context_add_method_3() {
        // (2 * 3) + (4 * 5)
        // ? 1: exclude rhs from lhs if present else merge rhs into lhs
        //  ((2 * 3) + (4 * 5))
        // ? 2: group variants
        //  ((2 * 3) + (4 * 5))
        // ? result:
        //  26
        let val1 = mul(vec![Type::Normal(2), Type::Normal(3)]);
        let val2 = mul(vec![Type::Normal(4), Type::Normal(5)]);
        let val3 = val1 + val2;
        assert_eq!(
            val3.repr().expect("failed to represent math context"),
            "((2 * 3) + (4 * 5))"
        );
        assert_eq!(val3.resolve(), 26);
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
        // (∑(1 → 4) [x => x ^ 2]) + (∑(4 → 5) [x => x + 20])
        // = ((1 ^ 2) + (2 ^ 2) + (3 ^ 2) + (4 ^ 2)) + ((4 + 20) + (5 + 20))
        // = ((1) + (4) + (9) + (16)) + ((24) + (25))
        // = (1 + 4 + 9 + 16) + (24 + 25)
        // = (30) + (49)
        // = (30 + 49)
        // = 79

        let val1 = sigma(1..=4, |val: u8| val.pow(2));
        let val2 = sigma(4..=5, |val| val + 20);
        let val3 = val1 + val2;
        match val3
            .repr()
            .expect("failed to represent math context")
            .as_str()
        {
            "(1 + 2 + 3 + 4 + (5 + 4))" | "(1 + 2 + 3 + 4 + (4 + 5))" => {}
            // fixme: asserting between multiple matches
            val => panic!(
                r#"assertion failed: `(left == right)`
  left: `{:?}`,
 right: `"(1 + 2 + 3 + 4 + (4 + 5))" or "(1 + 2 + 3 + 4 + (5 + 4))"`"#,
                val
            ),
        }
        assert_eq!(val3.resolve(), 79);
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
        match val3
            .repr()
            .expect("failed to represent math context")
            .as_str()
        {
            "(1 + 2 + 3 + 4 + 5)" | "(1 + 2 + 3 + 5 + 4)" => {}
            // fixme: asserting between multiple matches
            val => panic!(
                r#"assertion failed: `(left == right)`
  left: `{:?}`,
 right: `"(1 + 2 + 3 + 4 + 5)" or "(1 + 2 + 3 + 5 + 4)"`"#,
                val
            ),
        }
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
