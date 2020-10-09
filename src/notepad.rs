use std::fmt::Write;
use stdmath::{One, Zero};

#[derive(Debug, Clone)]
pub enum Context1<R> {
    Add(Vec<Context1<R>>),
    Mul(Vec<Context1<R>>),
    Nil(R),
}

impl<R> Context1<R> {
    pub fn resolve(self) -> R
    where
        R: Zero + One,
    {
        let (items, is_additive) = match self {
            Context1::Add(items) => (items, true),
            Context1::Mul(items) => (items, false),
            Context1::Nil(val) => return val,
        };
        items
            .into_iter()
            .fold(None, |prev, item| {
                let val = item.resolve();
                let result = match prev {
                    Some(prev) => {
                        if is_additive {
                            prev + val
                        } else {
                            prev * val
                        }
                    }
                    None => val,
                };
                Some(result)
            })
            .unwrap_or_else(|| if is_additive { R::zero() } else { R::one() })
    }
    fn repr_into(self, file: &mut dyn Write) -> std::fmt::Result
    where
        R: std::fmt::Debug,
    {
        let (items, is_additive) = match self {
            Context1::Add(items) => (items, true),
            Context1::Mul(items) => (items, false),
            Context1::Nil(val) => return write!(file, "{:?}", val),
        };
        write!(file, "(")?;
        for (index, item) in items.into_iter().enumerate() {
            write!(
                file,
                "{}",
                if index != 0 {
                    if is_additive {
                        " + "
                    } else {
                        " * "
                    }
                } else {
                    ""
                }
            )?;
            item.repr_into(file)?;
        }
        write!(file, ")")
    }
    pub fn repr(self) -> Result<String, std::fmt::Error>
    where
        R: std::fmt::Debug,
    {
        let mut file = String::new();
        self.repr_into(&mut file)?;
        Ok(file)
    }
}

pub fn main() {
    // (1 * 2) + 1 + (1 + 2)
    let a = Context1::Add(vec![
        Context1::Mul(vec![Context1::Nil(1), Context1::Nil(2)]),
        Context1::Nil(1),
        Context1::Add(vec![Context1::Nil(1), Context1::Nil(2)]),
    ]);
    println!(
        "{}",
        a.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", a.resolve());

    let b = Context1::Add(
        (1..=5)
            .map(|val| {
                if val % 2 == 0 {
                    Context1::Mul(
                        (1..=val)
                            .map(|val| {
                                if val % 4 == 0 {
                                    Context1::Add(
                                        (1..=val).map(|val| Context1::Nil(val)).collect::<Vec<_>>(),
                                    )
                                } else {
                                    Context1::Nil(val)
                                }
                            })
                            .collect::<Vec<_>>(),
                    )
                } else if val == 1 {
                    Context1::Nil(val)
                } else {
                    Context1::Add((1..=val).map(|val| Context1::Nil(val)).collect::<Vec<_>>())
                }
            })
            .collect::<Vec<_>>(),
    );
    println!(
        "{}",
        b.clone().repr().expect("failed to represent math context")
    );
    println!(" = {}", b.resolve());
}
