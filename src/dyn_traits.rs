use std::{
    any::Any,
    cmp::{Eq, Ordering, PartialEq},
    fmt::{self, Debug},
};

trait Value {
    fn as_any(&self) -> &dyn Any;
    fn _cmp(&self, other: &dyn Value) -> Option<Ordering>;
    fn _clone(&self) -> Box<dyn Value> {
        unimplemented!()
    }
    fn _debug(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        unimplemented!()
    }
}

impl PartialEq<dyn Value> for dyn Value {
    fn eq(&self, other: &dyn Value) -> bool {
        if let Some(Ordering::Equal) = self._cmp(other) {
            return true;
        }
        false
    }
}

impl Eq for dyn Value {}

impl PartialOrd<dyn Value> for dyn Value {
    fn partial_cmp(&self, other: &dyn Value) -> Option<Ordering> {
        self._cmp(other)
    }
}

impl Debug for dyn Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self._debug(f)
    }
}

impl Clone for Box<dyn Value> {
    fn clone(&self) -> Self {
        self._clone()
    }
}

macro_rules! stage_default_methods {
    () => {};
    (ALL) => {
        stage_default_methods!(as_any _cmp _debug _clone);
    };
    (as_any $($rest:tt)*) => {
        fn as_any(&self) -> &dyn Any {
            self
        }
        stage_default_methods!($($rest)*);
    };
    (_cmp $($rest:tt)*) => {
        fn _cmp(&self, other: &dyn Value) -> Option<Ordering> {
            other
                .as_any()
                .downcast_ref::<Self>()
                .map_or(None, |other| PartialOrd::partial_cmp(self, other))
        }
        stage_default_methods!($($rest)*);
    };
    (_debug $($rest:tt)*) => {
        fn _debug(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            Debug::fmt(self, f)
        }
        stage_default_methods!($($rest)*);
    };
    (_clone $($rest:tt)*) => {
        fn _clone(&self) -> Box<dyn Value> {
            Box::new(self.clone()) as Box<dyn Value>
        }
        stage_default_methods!($($rest)*);
    };
}

#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Debug)]
struct A;
impl Value for A {
    stage_default_methods!(ALL);
}
#[derive(Ord, PartialOrd, Eq, PartialEq, Clone, Debug)]
struct B;
impl Value for B {
    stage_default_methods!(ALL);
}

#[derive(Clone, Debug, Eq, PartialOrd)]
struct C {
    a: Box<dyn Value>,
    b: Box<dyn Value>,
}

impl PartialEq for C {
    fn eq(&self, other: &Self) -> bool {
        (&self.a, &self.b) == (&other.a, &other.b)
    }
}

impl Value for C {
    stage_default_methods!(ALL);
}

pub fn main() {
    let vec1: Vec<Box<dyn Value>> = vec![Box::new(A), Box::new(B)];
    let vec2: Vec<Box<dyn Value>> = vec![Box::new(A), Box::new(B)];
    let res = vec1 == vec2;
    println!("{}", res);

    println!(
        "{}",
        Box::new(A) as Box<dyn Value> == Box::new(B) as Box<dyn Value>
    );

    let a = A;
    let b = B;
    println!("{:?}", a);
    println!("{:?}", a.clone());
    println!("{:?}", b);
    println!("{:?}", b.clone());

    let c = Box::new(a) as Box<dyn Value>;
    println!("{:?}", c);
    println!("{:?}", c.clone());

    let val1 = C {
        a: Box::new(A),
        b: Box::new(B),
    };
    let val2 = C {
        a: Box::new(A),
        b: Box::new(B),
    };

    println!("{:?}", val1);
    println!("{:?}", val2);
    println!("{:?}", val1 == val2);

    let val3 = Box::new(val1) as Box<dyn Value>;
    println!("{:?}", val3);
}
