// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::util::DebugAsDisplay;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::One;
use std::convert::TryFrom;
use std::fmt;
use std::ops::Neg;

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RealAlgebraicNumberData {
    pub minimal_polynomial: Polynomial<BigInt>,
    pub lower_bound: Ratio<BigInt>,
    pub upper_bound: Ratio<BigInt>,
}

fn debug_real_algebraic_number(
    data: &RealAlgebraicNumberData,
    f: &mut fmt::Formatter,
    struct_name: &str,
) -> fmt::Result {
    f.debug_struct(struct_name)
        .field(
            "minimal_polynomial",
            &DebugAsDisplay(&data.minimal_polynomial),
        )
        .field("lower_bound", &DebugAsDisplay(&data.lower_bound))
        .field("upper_bound", &DebugAsDisplay(&data.upper_bound))
        .finish()
}

impl fmt::Debug for RealAlgebraicNumberData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug_real_algebraic_number(self, f, "RealAlgebraicNumberData")
    }
}

#[derive(Clone)]
pub struct RealAlgebraicNumber {
    data: RealAlgebraicNumberData,
}

impl fmt::Debug for RealAlgebraicNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug_real_algebraic_number(&self.data, f, "RealAlgebraicNumber")
    }
}

macro_rules! impl_from_int_or_ratio {
    ($t:ident) => {
        impl From<$t> for RealAlgebraicNumber {
            fn from(value: $t) -> Self {
                let value = BigInt::from(value);
                Self::new_unchecked(
                    [-&value, BigInt::one()].into(),
                    value.clone().into(),
                    value.into(),
                )
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
                Self::new_unchecked([neg_numer, denom].into(), ratio.clone(), ratio)
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
            data: RealAlgebraicNumberData {
                minimal_polynomial,
                lower_bound,
                upper_bound,
            },
        }
    }
    #[inline]
    pub fn minimal_polynomial(&self) -> &Polynomial<BigInt> {
        &self.data.minimal_polynomial
    }
    #[inline]
    pub fn data(&self) -> &RealAlgebraicNumberData {
        &self.data
    }
    #[inline]
    pub fn into_data(self) -> RealAlgebraicNumberData {
        self.data
    }
    pub fn degree(&self) -> usize {
        self.minimal_polynomial()
            .degree()
            .expect("known to be non-zero")
    }
    #[inline]
    pub fn is_rational(&self) -> bool {
        self.degree() <= 1
    }
    pub fn is_integer(&self) -> bool {
        self.is_rational() && self.minimal_polynomial().coefficient(1).is_one()
    }
    pub fn to_rational(&self) -> Option<Ratio<BigInt>> {
        if self.is_rational() {
            Some(Ratio::new_raw(
                -self.minimal_polynomial().coefficient(0),
                self.minimal_polynomial().coefficient(1),
            ))
        } else {
            None
        }
    }
    pub fn to_integer(&self) -> Option<BigInt> {
        if self.is_integer() {
            Some(-self.minimal_polynomial().coefficient(0))
        } else {
            None
        }
    }
    #[inline]
    pub fn lower_bound(&self) -> &Ratio<BigInt> {
        &self.data.lower_bound
    }
    #[inline]
    pub fn upper_bound(&self) -> &Ratio<BigInt> {
        &self.data.upper_bound
    }
    #[inline]
    pub fn shrink_bounds(&mut self) {
        if self.lower_bound() == self.upper_bound() {
            return;
        }
        if let Some(value) = self.to_rational() {
            self.data.lower_bound = value.clone();
            self.data.upper_bound = value;
        } else {
            unimplemented!();
        }
    }
}

impl Neg for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn neg(self) -> Self::Output {
        let degree_is_odd = self.degree().is_odd();
        let minimal_polynomial = self
            .minimal_polynomial()
            .iter()
            .enumerate()
            .map(|(index, coefficient)| {
                if index.is_odd() == degree_is_odd {
                    coefficient
                } else {
                    -coefficient
                }
            })
            .collect();

        // swap and negate bounds
        let lower_bound = -&self.data().upper_bound;
        let upper_bound = -&self.data().lower_bound;
        RealAlgebraicNumber::new_unchecked(minimal_polynomial, lower_bound, upper_bound)
    }
}

impl Neg for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn neg(self) -> Self::Output {
        -&self
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

    #[test]
    fn test_neg() {
        fn test_case(
            real_algebraic_number: RealAlgebraicNumber,
            expected: RealAlgebraicNumberData,
        ) {
            assert_eq!(real_algebraic_number.neg().into_data(), expected);
        }
        test_case(
            RealAlgebraicNumber::new_unchecked(p(&[-1, -2, 1]), ri(2), ri(3)),
            RealAlgebraicNumberData {
                minimal_polynomial: p(&[-1, 2, 1]),
                lower_bound: ri(-3),
                upper_bound: ri(-2),
            },
        );
        test_case(
            RealAlgebraicNumber::from(1),
            RealAlgebraicNumber::from(-1).into_data(),
        );
        test_case(
            RealAlgebraicNumber::from(r(4, 5)),
            RealAlgebraicNumber::from(r(-4, 5)).into_data(),
        );
    }
}
