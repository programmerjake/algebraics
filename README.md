## [Algebraic Numbers](https://en.wikipedia.org/wiki/Algebraic_number) Library

Use when you need exact arithmetic, speed is not critical, and rational numbers aren't good enough.

## Example:

```rust
use algebraics::prelude::*;
use algebraics::RealAlgebraicNumber as Number;

let two = Number::from(2);

// 2 is a rational number
assert!(two.is_rational());

// 1/2 is the reciprocal of 2
let one_half = two.recip();

// 1/2 is also a rational number
assert!(one_half.is_rational());

// 2^(1/4)
let root = (&two).pow((1, 4));

// we can use all the standard comparison operators
assert!(root != Number::from(3));
assert!(root < Number::from(2));
assert!(root > Number::from(1));

// we can use all of add, subtract, multiply, divide, and remainder
let sum = &root + &root;
let difference = &root - Number::from(47);
let product = &root * &one_half;
let quotient = &one_half / &root;
let remainder = &root % &one_half;

// root is not a rational number
assert!(!root.is_rational());

// the calculations are always exact
assert_eq!((&root).pow(4), two);

// lets compute 30 decimal places of root
let scale = Number::from(10).pow(30);
let scaled = &root * scale;
let digits = scaled.into_integer_trunc();
assert_eq!(
    digits.to_string(),
    1_18920_71150_02721_06671_74999_70560u128.to_string()
);

// get the minimal polynomial
let other_number = root + two.pow((1, 2));
assert_eq!(
    &other_number.minimal_polynomial().to_string(),
    "2 + -8*X + -4*X^2 + 0*X^3 + 1*X^4"
);

// works with really big numbers
let really_big = Number::from(1_00000_00000i64).pow(20) + Number::from(23);
assert_eq!(
    &really_big.to_integer_floor().to_string(),
    "100000000000000000000000000000000000000000000\
     000000000000000000000000000000000000000000000\
     000000000000000000000000000000000000000000000\
     000000000000000000000000000000000000000000000\
     000000000000000000023"
)
```

## Python support

Using algebraics from Python:

```bash
python3 -m pip install algebraics
```

```python
from algebraics import RealAlgebraicNumber
sqrt_2 = 2 ** (RealAlgebraicNumber(1) / 2)
assert sqrt_2 * sqrt_2 == 2
```

Using algebraics in your own Rust project:

```toml
[dependencies.algebraics]
version = "0.2"
```

Developing algebraics:

```bash
cargo install maturin
maturin develop --cargo-extra-args="--features python-extension"
```
