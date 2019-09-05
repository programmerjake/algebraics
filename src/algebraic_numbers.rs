// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::util::DebugAsDisplay;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_rational::Ratio;
use num_traits::One;
use std::fmt;

#[derive(Clone)]
pub struct RealAlgebraicNumber {
    minimal_polynomial: Polynomial<BigInt>,
    lower_bound: Ratio<BigInt>,
    upper_bound: Ratio<BigInt>,
}

impl fmt::Debug for RealAlgebraicNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("RealAlgebraicNumber")
            .field(
                "minimal_polynomial",
                &DebugAsDisplay(&self.minimal_polynomial),
            )
            .field("lower_bound", &DebugAsDisplay(&self.lower_bound))
            .field("upper_bound", &DebugAsDisplay(&self.upper_bound))
            .finish()
    }
}

macro_rules! impl_from_int_or_ratio {
    ($t:ident) => {
        impl From<$t> for RealAlgebraicNumber {
            fn from(value: $t) -> Self {
                let value = BigInt::from(value);
                Self {
                    minimal_polynomial: vec![-&value, BigInt::one()].into(),
                    lower_bound: value.clone().into(),
                    upper_bound: value.into(),
                }
            }
        }

        impl From<Ratio<$t>> for RealAlgebraicNumber {
            fn from(value: Ratio<$t>) -> Self {
                let (numer, denom) = value.into();
                let numer = BigInt::from(numer);
                if denom.is_one() {
                    return numer.into();
                }
                let denom = BigInt::from(denom);
                let neg_numer = -&numer;
                let ratio = Ratio::new_raw(numer, denom.clone());
                Self {
                    minimal_polynomial: vec![neg_numer, denom].into(),
                    lower_bound: ratio.clone(),
                    upper_bound: ratio,
                }
            }
        }
    };
}

impl_from_int_or_ratio!(u8);
impl_from_int_or_ratio!(u16);
impl_from_int_or_ratio!(u32);
impl_from_int_or_ratio!(u64);
impl_from_int_or_ratio!(u128);
impl_from_int_or_ratio!(usize);
impl_from_int_or_ratio!(BigUint);
impl_from_int_or_ratio!(i8);
impl_from_int_or_ratio!(i16);
impl_from_int_or_ratio!(i32);
impl_from_int_or_ratio!(i64);
impl_from_int_or_ratio!(i128);
impl_from_int_or_ratio!(isize);
impl_from_int_or_ratio!(BigInt);

impl RealAlgebraicNumber {
    pub fn new_unchecked(
        minimal_polynomial: Polynomial<BigInt>,
        lower_bound: Ratio<BigInt>,
        upper_bound: Ratio<BigInt>,
    ) -> Self {
        Self {
            minimal_polynomial,
            lower_bound,
            upper_bound,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i128, d: i128) -> Ratio<BigInt> {
        Ratio::new(BigInt::from(n), BigInt::from(d))
    }

    fn ri(v: i128) -> Ratio<BigInt> {
        Ratio::from(BigInt::from(v))
    }

    fn p(poly: &[i128]) -> Polynomial<BigInt> {
        poly.iter().copied().map(BigInt::from).collect()
    }

    #[test]
    fn test_debug() {
        fn test_case(
            poly: Polynomial<BigInt>,
            lower_bound: Ratio<BigInt>,
            upper_bound: Ratio<BigInt>,
            expected: &str,
        ) {
            let real_algebraic_number =
                RealAlgebraicNumber::new_unchecked(poly, lower_bound, upper_bound);
            let string = format!("{:?}", real_algebraic_number);
            assert_eq!(&string, expected);
        }

        test_case(
            p(&[0, 1]),
            ri(0),
            ri(0),
            "RealAlgebraicNumber { minimal_polynomial: 0 + 1*x, lower_bound: 0, upper_bound: 0 }",
        );

        test_case(
            p(&[-2, 0, 1]),
            ri(1),
            ri(2),
            "RealAlgebraicNumber { minimal_polynomial: -2 + 0*x + 1*x^2, lower_bound: 1, upper_bound: 2 }",
        );

        test_case(
            p(&[
                10_788_246_961,
                1_545_510_240,
                -29_925_033_224,
                1_820_726_496,
                19_259_216_972,
                -6_781_142_688,
                -2_872_989_528,
                2_147_919_840,
                -306_405_418,
                -105_773_280,
                53_150_088,
                -10_681_440,
                1_243_820,
                -89568,
                3928,
                -96,
                1,
            ]),
            r(22_46827, 100_000),
            r(22_4683, 10_000),
            "RealAlgebraicNumber { minimal_polynomial: 10788246961 \
             + 1545510240*x \
             + -29925033224*x^2 \
             + 1820726496*x^3 \
             + 19259216972*x^4 \
             + -6781142688*x^5 \
             + -2872989528*x^6 \
             + 2147919840*x^7 \
             + -306405418*x^8 \
             + -105773280*x^9 \
             + 53150088*x^10 \
             + -10681440*x^11 \
             + 1243820*x^12 \
             + -89568*x^13 \
             + 3928*x^14 \
             + -96*x^15 \
             + 1*x^16, \
             lower_bound: 2246827/100000, \
             upper_bound: 224683/10000 }",
        );
    }
}
