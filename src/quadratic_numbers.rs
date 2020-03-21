// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

// FIXME: remove when module made public again
#![allow(dead_code)]

use crate::{
    polynomial::{Polynomial, PolynomialCoefficient},
    traits::GCD,
};
use num_bigint::{BigInt, BigUint, Sign};
use num_rational::{BigRational, Ratio};
use num_traits::{
    cast::ToPrimitive, CheckedAdd, CheckedDiv, CheckedMul, CheckedRem, CheckedSub, Num, One,
    Signed, Zero,
};
use std::{
    cmp::Ordering,
    error::Error,
    fmt, mem,
    ops::{Add, Div, Mul, Neg, Rem, Sub},
};

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug, Default)]
pub(crate) struct QuadraticPolynomial<T> {
    pub(crate) constant_term: T,
    pub(crate) linear_term: T,
    pub(crate) quadratic_term: T,
}

impl<T: Zero + PolynomialCoefficient> From<QuadraticPolynomial<T>> for Polynomial<T> {
    fn from(poly: QuadraticPolynomial<T>) -> Self {
        vec![poly.constant_term, poly.linear_term, poly.quadratic_term].into()
    }
}

impl<T: Neg> Neg for QuadraticPolynomial<T> {
    type Output = QuadraticPolynomial<T::Output>;
    fn neg(self) -> Self::Output {
        QuadraticPolynomial {
            constant_term: -self.constant_term,
            linear_term: -self.linear_term,
            quadratic_term: -self.quadratic_term,
        }
    }
}

impl<'a, T> Neg for &'a QuadraticPolynomial<T>
where
    &'a T: Neg,
{
    type Output = QuadraticPolynomial<<&'a T as Neg>::Output>;
    fn neg(self) -> Self::Output {
        QuadraticPolynomial {
            constant_term: -&self.constant_term,
            linear_term: -&self.linear_term,
            quadratic_term: -&self.quadratic_term,
        }
    }
}

impl<T> QuadraticPolynomial<T> {
    pub(crate) fn discriminant(&self) -> T
    where
        for<'a> &'a T: Mul<Output = T>,
        u8: Into<T>,
        T: Sub<Output = T> + Mul<Output = T>,
    {
        &self.linear_term * &self.linear_term
            - &self.quadratic_term * &self.constant_term * 4.into()
    }
    pub(crate) fn swapped_roots<'a>(&'a self) -> Self
    where
        &'a T: Neg<Output = T>,
    {
        -self
    }
    pub(crate) fn into_swapped_roots(self) -> Self
    where
        T: Neg<Output = T>,
    {
        -self
    }
}

pub(crate) type BigQuadraticPolynomial = QuadraticPolynomial<BigInt>;

/// quadratic number (root of quadratic polynomial)
///
/// When `quadratic_term` is zero, the represented root is the standard
/// solution: `-constant_term / linear_term`
///
/// When `quadratic_term` is non-zero, the represented root is:
/// `(-linear_term + sqrt(discriminant())) / (2 * quadratic_term)`
///
/// the more negative root can be represented by negating the polynomial terms.
///
#[derive(Clone, Eq, PartialEq, Hash, Debug)]
pub(crate) struct RealQuadraticNumber {
    poly: BigQuadraticPolynomial,
}

impl Default for RealQuadraticNumber {
    fn default() -> Self {
        RealQuadraticNumber {
            poly: QuadraticPolynomial {
                constant_term: 0.into(),
                linear_term: 1.into(),
                quadratic_term: 0.into(),
            },
        }
    }
}

impl AsRef<BigQuadraticPolynomial> for RealQuadraticNumber {
    fn as_ref(&self) -> &BigQuadraticPolynomial {
        &self.poly
    }
}

impl Zero for RealQuadraticNumber {
    fn zero() -> Self {
        Self::from_integer(0.into())
    }
    fn is_zero(&self) -> bool {
        self.constant_term().is_zero()
            && self.linear_term().is_one()
            && self.quadratic_term().is_zero()
    }
}

impl One for RealQuadraticNumber {
    fn one() -> Self {
        Self::from_integer(1.into())
    }
    fn is_one(&self) -> bool {
        *self.constant_term() == BigInt::from(-1)
            && self.linear_term().is_one()
            && self.quadratic_term().is_zero()
    }
}

macro_rules! from_int {
    ($t:ty) => {
        impl From<$t> for RealQuadraticNumber {
            fn from(value: $t) -> Self {
                Self::from_integer(value.into())
            }
        }
    };
}

from_int!(u8);
from_int!(u16);
from_int!(u32);
from_int!(u64);
from_int!(u128);
from_int!(usize);
from_int!(BigUint);
from_int!(i8);
from_int!(i16);
from_int!(i32);
from_int!(i64);
from_int!(i128);
from_int!(isize);
from_int!(BigInt);

macro_rules! from_ratio {
    ($t:ty) => {
        impl From<Ratio<$t>> for RealQuadraticNumber {
            fn from(value: Ratio<$t>) -> Self {
                let (numer, denom) = value.into();
                Self::from_ratio(numer.into(), denom.into())
            }
        }
    };
}

from_ratio!(u8);
from_ratio!(u16);
from_ratio!(u32);
from_ratio!(u64);
from_ratio!(u128);
from_ratio!(usize);
from_ratio!(BigUint);
from_ratio!(i8);
from_ratio!(i16);
from_ratio!(i32);
from_ratio!(i64);
from_ratio!(i128);
from_ratio!(isize);
from_ratio!(BigInt);

#[derive(Copy, Clone, Debug)]
pub(crate) struct NonQuadraticResult;

impl fmt::Display for NonQuadraticResult {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "result of operation is not a quadratic number")
    }
}

impl Error for NonQuadraticResult {}

impl From<NonQuadraticResult> for std::io::Error {
    fn from(err: NonQuadraticResult) -> Self {
        Self::new(std::io::ErrorKind::InvalidInput, err)
    }
}

fn add_sub_sqrts_a_is_perfect_square(
    a: BigInt,
    b: BigInt,
    isqrt_a: BigInt,
) -> (BigQuadraticPolynomial, BigQuadraticPolynomial) {
    let constant_term = a - b;
    let linear_term = 2 * isqrt_a;
    let quadratic_term = 1.into();
    let mut poly2 = BigQuadraticPolynomial {
        constant_term,
        linear_term,
        quadratic_term,
    };
    let poly1 = poly2.clone();
    poly2.linear_term = -poly2.linear_term;
    (poly1, poly2)
}

fn add_sub_sqrts(
    a: BigInt,
    b: BigInt,
) -> Result<(BigQuadraticPolynomial, BigQuadraticPolynomial), NonQuadraticResult> {
    assert!(!a.is_negative());
    assert!(!b.is_negative());
    let isqrt_a = a.sqrt();
    if &isqrt_a * &isqrt_a == a {
        return Ok(add_sub_sqrts_a_is_perfect_square(a, b, isqrt_a));
    }
    let isqrt_b = b.sqrt();
    if &isqrt_b * &isqrt_b == a {
        return Ok(add_sub_sqrts_a_is_perfect_square(b, a, isqrt_b));
    }
    let a_b = &a * &b;
    let isqrt_a_b = a_b.sqrt();
    if &isqrt_a_b * &isqrt_a_b == a_b {
        let a_plus_b = &a + &b;
        let two_isqrt_a_b: BigInt = 2 * isqrt_a_b;
        let poly1 = BigQuadraticPolynomial {
            constant_term: &two_isqrt_a_b - &a_plus_b,
            linear_term: 0.into(),
            quadratic_term: 1.into(),
        };
        let poly2 = BigQuadraticPolynomial {
            constant_term: -two_isqrt_a_b - a_plus_b,
            linear_term: 0.into(),
            quadratic_term: 1.into(),
        };
        return Ok((poly1, poly2));
    }
    Err(NonQuadraticResult)
}

fn add_rational_with_real_quadratic_number(
    lhs_numerator: BigInt,
    lhs_denominator: BigInt,
    rhs: RealQuadraticNumber,
) -> RealQuadraticNumber {
    let mut poly = rhs.into_polynomial();
    let denominator_squared = &lhs_denominator * &lhs_denominator;
    let denominator_times_numerator = &lhs_denominator * &lhs_numerator;
    let numerator_squared = &lhs_numerator * &lhs_numerator;
    poly.constant_term = poly.constant_term * &denominator_squared
        - &poly.linear_term * &denominator_times_numerator
        + &poly.quadratic_term * numerator_squared;
    poly.linear_term = poly.linear_term * &denominator_squared
        - BigInt::from(2) * &poly.quadratic_term * denominator_times_numerator;
    poly.quadratic_term *= denominator_squared;
    RealQuadraticNumber { poly }.into_reduced()
}

impl RealQuadraticNumber {
    pub(crate) fn new(poly: BigQuadraticPolynomial) -> Option<Self> {
        if (poly.quadratic_term.is_zero() && poly.linear_term.is_zero())
            || poly.discriminant().is_negative()
        {
            None
        } else {
            Some(Self { poly }.into_reduced())
        }
    }
    pub(crate) fn constant_term(&self) -> &BigInt {
        &self.poly.constant_term
    }
    pub(crate) fn linear_term(&self) -> &BigInt {
        &self.poly.linear_term
    }
    pub(crate) fn quadratic_term(&self) -> &BigInt {
        &self.poly.quadratic_term
    }
    pub(crate) fn polynomial(&self) -> &BigQuadraticPolynomial {
        &self.poly
    }
    pub(crate) fn into_polynomial(self) -> BigQuadraticPolynomial {
        self.poly
    }
    fn from_negated_integer(negated_value: BigInt) -> Self {
        Self {
            poly: BigQuadraticPolynomial {
                constant_term: negated_value,
                linear_term: 1.into(),
                quadratic_term: 0.into(),
            },
        }
    }
    pub(crate) fn from_integer(value: BigInt) -> Self {
        Self::from_negated_integer(-value)
    }
    fn from_negated_reduced_ratio(negated_numerator: BigInt, denominator: BigInt) -> Self {
        Self {
            poly: BigQuadraticPolynomial {
                constant_term: negated_numerator,
                linear_term: denominator,
                quadratic_term: 0.into(),
            },
        }
    }
    fn from_negated_reduced_ratio_checked(
        negated_numerator: BigInt,
        denominator: BigInt,
    ) -> Result<Self, NonQuadraticResult> {
        if denominator.is_zero() {
            return Err(NonQuadraticResult);
        }
        Ok(Self::from_negated_reduced_ratio(
            negated_numerator,
            denominator,
        ))
    }
    fn from_reduced_ratio(numerator: BigInt, denominator: BigInt) -> Self {
        Self::from_negated_reduced_ratio(-numerator, denominator)
    }
    fn from_ratio_non_inf(numerator: BigInt, denominator: BigInt) -> Self {
        let mut gcd = numerator.gcd(&denominator);
        let mut neg_gcd = -&gcd;
        if denominator.is_negative() {
            mem::swap(&mut gcd, &mut neg_gcd);
        }
        Self::from_negated_reduced_ratio(numerator / neg_gcd, denominator / gcd)
    }
    pub(crate) fn from_ratio_checked(
        numerator: BigInt,
        denominator: BigInt,
    ) -> Result<Self, NonQuadraticResult> {
        if denominator.is_zero() {
            return Err(NonQuadraticResult);
        }
        Ok(Self::from_ratio_non_inf(numerator, denominator))
    }
    pub(crate) fn from_ratio(numerator: BigInt, denominator: BigInt) -> Self {
        assert!(!denominator.is_zero(), "denominator is zero");
        Self::from_ratio_non_inf(numerator, denominator)
    }
    pub(crate) fn is_ratio(&self) -> bool {
        self.quadratic_term().is_zero()
    }
    pub(crate) fn is_integer(&self) -> bool {
        self.is_ratio() && self.linear_term().is_one()
    }
    pub(crate) fn to_integer(&self) -> Option<BigInt> {
        if self.is_integer() {
            Some(-self.constant_term())
        } else {
            None
        }
    }
    pub(crate) fn to_tuple_ratio(&self) -> Option<(BigInt, BigInt)> {
        if self.is_ratio() {
            Some((-self.constant_term(), self.linear_term().clone()))
        } else {
            None
        }
    }
    pub(crate) fn to_ratio(&self) -> Option<BigRational> {
        self.to_tuple_ratio()
            .map(|(numer, denom)| BigRational::new_raw(numer, denom))
    }
    fn into_reduced(mut self) -> Self {
        if self.quadratic_term().is_zero() {
            // handle ratios
            return Self::from_ratio(-self.poly.constant_term, self.poly.linear_term);
        }
        let gcd = self
            .constant_term()
            .gcd(&self.linear_term())
            .gcd(&self.quadratic_term());
        // gcd is always positive since quadratic_term is not zero
        debug_assert!(gcd.is_positive());
        self.poly.constant_term /= &gcd;
        self.poly.linear_term /= &gcd;
        self.poly.quadratic_term /= gcd;
        let discriminant = self.poly.discriminant();
        assert!(!discriminant.is_negative(), "complex roots");
        let isqrt_discriminant = discriminant.sqrt();
        if &isqrt_discriminant * &isqrt_discriminant == discriminant {
            // rational root
            return Self::from_ratio(
                -self.poly.linear_term + isqrt_discriminant,
                2 * self.poly.quadratic_term,
            );
        }
        self
    }
    pub(crate) fn checked_add(&self, rhs: &Self) -> Result<Self, NonQuadraticResult> {
        if let Some((lhs_numerator, lhs_denominator)) = self.to_tuple_ratio() {
            return Ok(add_rational_with_real_quadratic_number(
                lhs_numerator,
                lhs_denominator,
                rhs.clone(),
            ));
        } else if let Some((rhs_numerator, rhs_denominator)) = rhs.to_tuple_ratio() {
            return Ok(add_rational_with_real_quadratic_number(
                rhs_numerator,
                rhs_denominator,
                self.clone(),
            ));
        }
        let _sqrts_sum_diff = add_sub_sqrts(
            self.poly.discriminant() * rhs.quadratic_term().abs() * 2,
            rhs.poly.discriminant() * self.quadratic_term().abs() * 2,
        )?;
        unimplemented!()
    }
    pub(crate) fn checked_sub(&self, rhs: &Self) -> Result<Self, NonQuadraticResult> {
        self.checked_add(&-rhs)
    }
    pub(crate) fn checked_recip(&self) -> Result<Self, NonQuadraticResult> {
        if self.is_ratio() {
            return Self::from_negated_reduced_ratio_checked(
                self.linear_term().clone(),
                self.constant_term().clone(),
            );
        }
        unimplemented!()
    }
    pub(crate) fn checked_rem(&self, _rhs: &Self) -> Result<Self, NonQuadraticResult> {
        unimplemented!()
    }
    pub(crate) fn checked_mul(&self, _rhs: &Self) -> Result<Self, NonQuadraticResult> {
        unimplemented!()
    }
    pub(crate) fn checked_div(&self, _rhs: &Self) -> Result<Self, NonQuadraticResult> {
        unimplemented!()
    }
    pub(crate) fn to_f64(&self) -> Option<f64> {
        Some(if self.is_ratio() {
            -self.constant_term().to_f64()? / self.linear_term().to_f64()?
        } else {
            let sqrt_discriminant = self.poly.discriminant().to_f64()?.sqrt();
            (-self.linear_term().to_f64()? + sqrt_discriminant)
                / (2.0 * self.quadratic_term().to_f64()?)
        })
    }
}

impl Neg for RealQuadraticNumber {
    type Output = RealQuadraticNumber;
    fn neg(mut self) -> RealQuadraticNumber {
        self.poly.constant_term = -self.poly.constant_term;
        self.poly.quadratic_term = -self.poly.quadratic_term;
        self
    }
}

impl Neg for &'_ RealQuadraticNumber {
    type Output = RealQuadraticNumber;
    fn neg(self) -> RealQuadraticNumber {
        self.clone().neg()
    }
}

pub(crate) struct FromStrRadixError;

impl Num for RealQuadraticNumber {
    type FromStrRadixErr = FromStrRadixError;
    fn from_str_radix(_str: &str, _radix: u32) -> Result<Self, FromStrRadixError> {
        unimplemented!()
    }
}

impl Signed for RealQuadraticNumber {
    fn abs(&self) -> Self {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }
    fn abs_sub(&self, _other: &Self) -> Self {
        unimplemented!()
    }
    fn signum(&self) -> Self {
        if self.is_zero() {
            0
        } else if self.is_positive() {
            1
        } else {
            -1
        }
        .into()
    }
    fn is_positive(&self) -> bool {
        let quadratic_term_sign = self.quadratic_term().sign();
        let is_reversed = match quadratic_term_sign {
            Sign::NoSign => {
                // rational; check numerator
                return self.constant_term().is_negative();
            }
            Sign::Minus => true,
            Sign::Plus => false,
        };
        if self.linear_term().is_negative() {
            return !is_reversed;
        }
        self.constant_term().is_negative()
    }
    fn is_negative(&self) -> bool {
        if self.is_zero() {
            false
        } else {
            !self.is_positive()
        }
    }
}

impl PartialOrd for RealQuadraticNumber {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl PartialEq<BigRational> for RealQuadraticNumber {
    fn eq(&self, rhs: &BigRational) -> bool {
        self.is_ratio()
            && self.linear_term() == rhs.denom()
            && &-self.constant_term() == rhs.numer()
    }
}

impl PartialEq<RealQuadraticNumber> for BigRational {
    fn eq(&self, rhs: &RealQuadraticNumber) -> bool {
        *rhs == *self
    }
}

impl PartialOrd<RealQuadraticNumber> for BigRational {
    fn partial_cmp(&self, rhs: &RealQuadraticNumber) -> Option<Ordering> {
        rhs.partial_cmp(self).map(Ordering::reverse)
    }
}

impl PartialOrd<BigRational> for RealQuadraticNumber {
    fn partial_cmp(&self, rhs: &BigRational) -> Option<Ordering> {
        if let Some(lhs) = self.to_ratio() {
            Some(lhs.cmp(rhs))
        } else if self.lt(rhs) {
            Some(Ordering::Less)
        } else {
            Some(Ordering::Greater)
        }
    }
    fn lt(&self, rhs: &BigRational) -> bool {
        debug_assert!(rhs.denom().is_positive());
        debug_assert!(!self.poly.discriminant().is_negative());
        let abs_quadratic_term = self.quadratic_term().abs();
        if let Some(lhs) = self.to_ratio() {
            lhs < *rhs
        } else if self.quadratic_term().is_negative() {
            if self.linear_term() * rhs.denom() < 2 * abs_quadratic_term * rhs.numer() {
                true
            } else {
                self.constant_term() * rhs.denom() * rhs.denom()
                    > -rhs.numer()
                        * (self.quadratic_term() * rhs.numer() + self.linear_term() * rhs.denom())
            }
        } else if self.linear_term() * rhs.denom() > -2 * abs_quadratic_term * rhs.numer() {
            self.constant_term() * rhs.denom() * rhs.denom()
                > -rhs.numer()
                    * (self.quadratic_term() * rhs.numer() + self.linear_term() * rhs.denom())
        } else {
            false
        }
    }
}

fn quadratic_less_than(lhs: &RealQuadraticNumber, rhs: &RealQuadraticNumber) -> bool {
    let p_plus_sqrt_r_all_over_q_less_than_zero = |p: &BigInt, r: &BigInt, q: &BigInt| {
        // returns (p + sqrt(r)) / q < 0 where sqrt(r) doesn't truncate the result
        debug_assert!(!q.is_zero());
        if q.is_positive() {
            *r < p * p && !r.is_negative() && !p.is_positive()
        } else if p.is_positive() {
            !r.is_negative()
        } else {
            *r > p * p
        }
    };
    debug_assert!(!lhs.quadratic_term().is_zero());
    debug_assert!(!rhs.quadratic_term().is_zero());
    debug_assert!(!lhs.poly.discriminant().is_negative());
    debug_assert!(!rhs.poly.discriminant().is_negative());
    let a1 = lhs.quadratic_term();
    let b1 = lhs.linear_term();
    let c1 = lhs.constant_term();
    let a2 = rhs.quadratic_term();
    let b2 = rhs.linear_term();
    let c2 = rhs.constant_term();
    let const2 = BigInt::from(2);
    let const4 = BigInt::from(4);
    match (a1.is_negative(), a2.is_negative()) {
        (false, false) => {
            let p = b2 * a1 - b1 * a2;
            let r = (b1 * b1 - &const4 * a1 * c1) * (a2 * a2);
            if p_plus_sqrt_r_all_over_q_less_than_zero(&p, &r, a1) {
                true
            } else if p.is_negative() {
                let r2n = (b2 * b2 - const4 * a2 * c2) * (a1 * a1) - &r - &p * &p;
                let r2d = const2 * p;
                if r2n.is_positive() {
                    true
                } else {
                    r * (&r2d * &r2d) > &r2n * &r2n
                }
            } else {
                let r2n = (b2 * b2 - const4 * a2 * c2) * (a1 * a1) - &r - &p * &p;
                let r2d = const2 * p;
                if r2n.is_negative() {
                    false
                } else {
                    r * (&r2d * &r2d) < &r2n * &r2n
                }
            }
        }
        (false, true) => {
            let d1 = b1 * b1 - &const4 * a1 * c1;
            let p = b1 * a2 - b2 * a1;
            let r = (b2 * b2 - const4 * a2 * c2) * (a1 * a1);
            if p_plus_sqrt_r_all_over_q_less_than_zero(&p, &r, a2) {
                false
            } else if p.is_positive() {
                let r2n = d1 * (a2 * a2) - &p * &p - &r;
                let r2d = const2 * p;
                if r2n.is_negative() {
                    true
                } else {
                    r * &r2d * &r2d > &r2n * &r2n
                }
            } else {
                let r2n = d1 * (a2 * a2) - &p * &p - &r;
                let r2d = const2 * p;
                if r2n.is_positive() {
                    false
                } else {
                    r * &r2d * &r2d < &r2n * &r2n
                }
            }
        }
        (true, false) => {
            let d1 = b1 * b1 - &const4 * a1 * c1;
            let d2 = b2 * b2 - const4 * a2 * c2;
            let p = b2 * a1 - b1 * a2;
            let r = d2 * (a1 * a1);
            if p_plus_sqrt_r_all_over_q_less_than_zero(&p, &r, &-a2) {
                true
            } else if p.is_positive() {
                let r2n = d1 * (a2 * a2) - &p * &p - &r;
                let r2d = const2 * p;
                if r2n.is_negative() {
                    false
                } else {
                    r * &r2d * &r2d < &r2n * &r2n
                }
            } else {
                let r2n = d1 * (a2 * a2) - &p * &p - &r;
                let r2d = const2 * &p;
                if r2n.is_positive() {
                    true
                } else {
                    r * &r2d * &r2d > &r2n * &r2n
                }
            }
        }
        (true, true) => quadratic_less_than(&-rhs, &-lhs),
    }
}

impl Ord for RealQuadraticNumber {
    fn cmp(&self, rhs: &Self) -> Ordering {
        if let Some(rhs) = rhs.to_ratio() {
            self.partial_cmp(&rhs).unwrap()
        } else if let Some(lhs) = self.to_ratio() {
            lhs.partial_cmp(rhs).unwrap()
        } else if self == rhs {
            Ordering::Equal
        } else if quadratic_less_than(self, rhs) {
            Ordering::Less
        } else {
            Ordering::Greater
        }
    }
}

macro_rules! impl_binary_ops_using_ref_ref {
    ($op:ident, $fn:ident, $l_type:ident, $r_type:ident) => {
        impl $op<$r_type> for $l_type {
            type Output = <&'static $l_type as $op<&'static $r_type>>::Output;
            fn $fn(self, rhs: $r_type) -> Self::Output {
                (&self).$fn(&rhs)
            }
        }
        impl $op<&'_ $r_type> for $l_type {
            type Output = <&'static $l_type as $op<&'static $r_type>>::Output;
            fn $fn(self, rhs: &$r_type) -> Self::Output {
                (&self).$fn(rhs)
            }
        }
        impl $op<$l_type> for &'_ $l_type {
            type Output = <&'static $l_type as $op<&'static $r_type>>::Output;
            fn $fn(self, rhs: $r_type) -> Self::Output {
                self.$fn(&rhs)
            }
        }
    };
}

macro_rules! impl_binary_ops_using_member_fn {
    ($op:ident, $fn:ident, $checked_op:ident, $checked_fn:ident, $member_fn:ident) => {
        impl_binary_ops_using_ref_ref!($op, $fn, RealQuadraticNumber, RealQuadraticNumber);
        impl<'a, 'b> $op<&'a RealQuadraticNumber> for &'b RealQuadraticNumber {
            type Output = RealQuadraticNumber;
            fn $fn(self, rhs: &RealQuadraticNumber) -> RealQuadraticNumber {
                self.$member_fn(rhs).unwrap()
            }
        }
        impl $checked_op for RealQuadraticNumber {
            fn $checked_fn(&self, rhs: &Self) -> Option<Self> {
                self.$member_fn(rhs).ok()
            }
        }
    };
}

impl_binary_ops_using_member_fn!(Add, add, CheckedAdd, checked_add, checked_add);
impl_binary_ops_using_member_fn!(Sub, sub, CheckedSub, checked_sub, checked_sub);
impl_binary_ops_using_member_fn!(Mul, mul, CheckedMul, checked_mul, checked_mul);
impl_binary_ops_using_member_fn!(Div, div, CheckedDiv, checked_div, checked_div);
impl_binary_ops_using_member_fn!(Rem, rem, CheckedRem, checked_rem, checked_rem);

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn test_quad_poly_into_poly() {
        assert_eq!(
            Polynomial::from(QuadraticPolynomial {
                constant_term: 1,
                linear_term: 2,
                quadratic_term: 3
            })
            .to_string(),
            "1 + 2*X + 3*X^2"
        );
    }
    #[test]
    fn test_quad_poly_neg() {
        assert_eq!(
            Polynomial::from(-QuadraticPolynomial {
                constant_term: 1,
                linear_term: 2,
                quadratic_term: 3
            })
            .to_string(),
            "-1 + -2*X + -3*X^2"
        );
        assert_eq!(
            Polynomial::from(-&QuadraticPolynomial {
                constant_term: 1,
                linear_term: 2,
                quadratic_term: 3
            })
            .to_string(),
            "-1 + -2*X + -3*X^2"
        );
    }
    #[test]
    fn test_discriminant() {
        for (a, b, c) in &[(1, 2, 3), (4, 645, 12), (2343, 3453, 2364)] {
            let poly = QuadraticPolynomial::<i32> {
                constant_term: *c,
                linear_term: *b,
                quadratic_term: *a,
            };
            assert_eq!(poly.discriminant(), b * b - 4 * a * c);
        }
    }
    #[test]
    fn test_real_quadratic_number_default_zero() {
        let v = RealQuadraticNumber::default();
        assert_eq!(v.constant_term(), &BigInt::zero());
        assert_eq!(v.linear_term(), &BigInt::one());
        assert_eq!(v.quadratic_term(), &BigInt::zero());
        assert_eq!(v, RealQuadraticNumber::from(0));
        assert_eq!(v, RealQuadraticNumber::zero());
    }
    #[test]
    fn test_real_quadratic_number_one() {
        let v = RealQuadraticNumber::one();
        assert_eq!(v.constant_term(), &-BigInt::one());
        assert_eq!(v.linear_term(), &BigInt::one());
        assert_eq!(v.quadratic_term(), &BigInt::zero());
        assert_eq!(v, RealQuadraticNumber::from(1));
    }
    #[test]
    fn test_real_quadratic_number_from_ratio() {
        let v = RealQuadraticNumber::from(Ratio::new(2, 3));
        assert_eq!(v.constant_term(), &BigInt::from(-2));
        assert_eq!(v.linear_term(), &BigInt::from(3));
        assert_eq!(v.quadratic_term(), &BigInt::zero());
        assert_eq!(v, RealQuadraticNumber::from_ratio(4.into(), 6.into()));
        assert!(RealQuadraticNumber::from_ratio_checked(1.into(), 0.into()).is_err());
    }
    #[test]
    fn test_real_quadratic_number_into_reduced() {
        for ((a, b, c), reduced) in [
            ((-15, 36, 45), Some((-5, 12, 15))), // 6/5 - sqrt(111)/5 == -0.9071307505705477
            ((9, 1, 90), None),                  // complex
            ((90, 0, 15), None),                 // complex
            ((-40, 2, 1), Some((-40, 2, 1))),    // 1/40 - sqrt(41)/40 == -0.1350781059358212
            ((0, 0, -10), None),                 // non-finite
            ((-8, 0, 1), Some((-8, 0, 1))),      // -sqrt(2)/4 == -0.3535533905932738
            ((9, 1, -24), Some((9, 1, -24))),    // -1/18 + sqrt(865)/18 == 1.5783823522058602
            ((12, 0, 3), None),                  // complex
            ((0, -72, -9), Some((0, 8, 1))),     // -1/8 == -0.125
            ((12, 5, -60), Some((12, 5, -60))),  // -5/24 + sqrt(2905)/24 == 2.0374188297019775
            ((1, 1, 0), Some((0, 1, 0))),        // 0 == 0
            ((-15, 1, 0), Some((0, 1, 0))),      // 0 == 0
            ((0, 1, -6), Some((0, 1, -6))),      // 6 == 6
            ((1, -8, 40), None),                 // complex
            ((12, 0, 0), Some((0, 1, 0))),       // 0 == 0
            ((10, 1, 0), Some((0, 1, 0))),       // 0 == 0
            ((45, -10, 24), None),               // complex
            ((5, 1, 72), None),                  // complex
            ((-9, 4, -36), None),                // complex
            ((12, 0, -12), Some((0, 1, -1))),    // 1 == 1
            ((-180, -2, 45), Some((-180, -2, 45))), // -sqrt(8101)/180 - 1/180 == -0.5055864188005466
            ((-90, 0, 20), Some((-9, 0, 2))),       // -sqrt(2)/3 == -0.4714045207910317
            ((72, -15, 180), None),                 // complex
            ((1, 1, -120), Some((1, 1, -120))),     // -1/2 + sqrt(481)/2 == 10.465856099730654
            ((0, -90, 0), Some((0, 1, 0))),         // 0 == 0
            ((-2, 1, 0), Some((0, 1, 0))),          // 0 == 0
            ((1, 1, 1), None),                      // complex
            ((-90, 24, 72), Some((-15, 4, 12))),    // 2/15 - 2*sqrt(46)/15 == -0.7709773310833691
            ((36, -30, 6), Some((0, 2, -1))),       // 1/2 == 0.5
            ((-40, -30, 5), Some((-8, -6, 1))),     // -sqrt(17)/8 - 3/8 == -0.8903882032022075
            ((0, -3, 24), Some((0, 1, -8))),        // 8 == 8
            ((1, 20, -8), Some((1, 20, -8))),       // -10 + 6*sqrt(3) == 0.39230484541326405
            ((1, -18, 72), Some((0, 1, -12))),      // 12 == 12
            ((-36, -30, 1), Some((-36, -30, 1))),   // -sqrt(29)/12 - 5/12 == -0.8654304005945419
            ((1, 8, 1), Some((1, 8, 1))),           // -4 + sqrt(15) == -0.12701665379258298
            ((15, -60, 1), Some((15, -60, 1))),     // sqrt(885)/15 + 2 == 3.9832633040858023
            ((2, 90, 72), Some((1, 45, 36))),       // -45/2 + 3*sqrt(209)/2 == -0.8147515577985587
            ((90, -3, 360), None),                  // complex
            ((1, 0, 0), Some((0, 1, 0))),           // 0 == 0
            ((0, -360, 36), Some((0, 10, -1))),     // 1/10 == 0.1
            ((-1, 90, -60), Some((-1, 90, -60))),   // 45 - sqrt(1965) == 0.6716794813969997
            ((1, -120, -120), Some((1, -120, -120))), // 60 + 2*sqrt(930) == 120.99180272790763
            ((360, 6, -60), Some((0, 5, -2))),      // 2/5 == 0.4
            ((0, 0, -1), None),                     // non-finite
            ((8, 2, -2), Some((4, 1, -1))),         // -1/8 + sqrt(17)/8 == 0.3903882032022076
            ((0, 180, 0), Some((0, 1, 0))),         // 0 == 0
            ((-15, 3, 0), Some((0, 1, 0))),         // 0 == 0
            ((30, -90, 15), Some((2, -6, 1))),      // sqrt(7)/2 + 3/2 == 2.8228756555322954
            ((-3, 0, -45), None),                   // complex
            ((10, -30, 24), None),                  // complex
        ]
        .iter()
        .copied()
        {
            let poly = QuadraticPolynomial {
                constant_term: c.into(),
                linear_term: b.into(),
                quadratic_term: a.into(),
            };
            println!("{}", Polynomial::from(poly.clone()));
            let num = RealQuadraticNumber::new(poly);
            if let Some((reduced_a, reduced_b, reduced_c)) = reduced {
                assert!(num.is_some());
                let num = num.unwrap();
                assert_eq!(num.constant_term(), &BigInt::from(reduced_c));
                assert_eq!(num.linear_term(), &BigInt::from(reduced_b));
                assert_eq!(num.quadratic_term(), &BigInt::from(reduced_a));
            } else {
                assert!(num.is_none());
            }
        }
    }
    #[allow(clippy::unreadable_literal)]
    const FLOAT_TEST_CASES: &[(i32, i32, i32, f64)] = &[
        (-15, 36, 45, -0.9071307505705477),   // 6/5 - sqrt(111)/5
        (-40, 2, 1, -0.1350781059358212),     // 1/40 - sqrt(41)/40
        (-10, 24, 3, -0.11909059582729195),   // 6/5 - sqrt(174)/10
        (0, 9, 1, -0.1111111111111111),       // -1/9
        (-24, 180, 1, -0.005551446414582865), // 15/4 - sqrt(2031)/12
        (1, 1, -72, 8.0),                     // 8
        (30, -90, 1, 2.988847428941819),      // sqrt(1995)/30 + 3/2
        (-9, 9, 0, 0.0),                      // 0
        (-15, 0, 0, 0.0),                     // 0
        (1, -6, -60, 11.306623862918075),     // 3 + sqrt(69)
        (45, -15, 0, 0.3333333333333333),     // 1/3
        (0, 1, -90, 90.0),                    // 90
        (45, 6, -60, 1.0899567715264982),     // -1/15 + sqrt(301)/15
        (-20, 1, 18, -0.9240126448051154),    // 1/40 - sqrt(1441)/40
        (1, 60, -180, 2.8633534503099654),    // -30 + 6*sqrt(30)
        (-9, 45, 0, 0.0),                     // 0
        (-90, 0, 20, -0.4714045207910317),    // -sqrt(2)/3
        (1, 1, -120, 10.465856099730654),     // -1/2 + sqrt(481)/2
        (0, -90, 0, 0.0),                     // 0
        (-2, 1, 0, 0.0),                      // 0
        (-90, 24, 72, -0.7709773310833691),   // 2/15 - 2*sqrt(46)/15
        (36, -30, 6, 0.5),                    // 1/2
        (0, 1, -6, 6.0),                      // 6
        (-10, 18, 1, -0.053939201416945616),  // 9/10 - sqrt(91)/10
        (-3, 24, 1, -0.04145188432738026),    // 4 - 7*sqrt(3)/3
        (1, -5, 5, 3.618033988749895),        // sqrt(5)/2 + 5/2
        (0, 18, 72, -4.0),                    // -4
        (1, 12, 1, -0.08392021690038387),     // -6 + sqrt(35)
        (-24, 120, 1, -0.008319490548735153), // 5/2 - sqrt(906)/12
        (1, 12, -2, 0.16441400296897601),     // -6 + sqrt(38)
        (1, -40, 3, 39.92485884517127),       // sqrt(397) + 20
        (-6, 0, 1, -0.40824829046386296),     // -sqrt(6)/6
        (1, -90, 0, 90.0),                    // 90
        (-5, -90, 0, -18.0),                  // -18
        (4, 1, -36, 2.8776030373660784),      // -1/8 + sqrt(577)/8
        (1, -40, 0, 40.0),                    // 40
        (-60, 1, 2, -0.1744309349955109),     // 1/120 - sqrt(481)/120
    ];
    #[test]
    fn test_real_quadratic_number_to_f64() {
        for (a, b, c, f) in FLOAT_TEST_CASES.iter().copied() {
            let poly = QuadraticPolynomial {
                constant_term: c.into(),
                linear_term: b.into(),
                quadratic_term: a.into(),
            };
            println!("{}: {}", Polynomial::from(poly.clone()), f);
            let rqn = RealQuadraticNumber::new(poly).unwrap();
            let num = rqn.to_f64().unwrap();
            assert!((num - f).abs() < 1e-10, format!("{} != {}", num, f));
        }
    }
    #[test]
    fn test_real_quadratic_number_neg() {
        for (a, b, c, f) in FLOAT_TEST_CASES.iter().copied() {
            let poly = QuadraticPolynomial {
                constant_term: c.into(),
                linear_term: b.into(),
                quadratic_term: a.into(),
            };
            println!("{}: {}", Polynomial::from(poly.clone()), f);
            let rqn = RealQuadraticNumber::new(poly).unwrap();
            let num = (-rqn).to_f64().unwrap();
            let f = -f;
            assert!((num - f).abs() < 1e-10, format!("{} != {}", num, f));
        }
    }
    #[test]
    fn test_real_quadratic_number_signum() {
        for (a, b, c, f) in FLOAT_TEST_CASES.iter().copied() {
            let poly = QuadraticPolynomial {
                constant_term: c.into(),
                linear_term: b.into(),
                quadratic_term: a.into(),
            };
            println!("{}: {}", Polynomial::from(poly.clone()), f);
            let rqn = RealQuadraticNumber::new(poly).unwrap();
            let signum = rqn.signum().to_integer().unwrap().to_i32().unwrap();
            let expected = match f.partial_cmp(&0.0) {
                Some(Ordering::Greater) => 1,
                Some(Ordering::Less) => -1,
                _ => 0,
            };
            assert_eq!(signum, expected, "({}, {})", rqn.to_f64().unwrap(), f);
        }
    }
    #[test]
    fn test_real_quadratic_number_cmp_rational() {
        for (a, b, c, f) in FLOAT_TEST_CASES.iter().copied() {
            let poly = QuadraticPolynomial {
                constant_term: c.into(),
                linear_term: b.into(),
                quadratic_term: a.into(),
            };
            let rqn = RealQuadraticNumber::new(poly.clone()).unwrap();
            for n in -20..=20 {
                for d in 1..20 {
                    let q = f64::from(n) / f64::from(d);
                    println!(
                        "{}: {} <=> {}/{} == {}",
                        Polynomial::from(poly.clone()),
                        f,
                        n,
                        d,
                        q
                    );
                    let rat = BigRational::new(n.into(), d.into());
                    let cmp_results = rqn.partial_cmp(&BigRational::new(n.into(), d.into()));
                    let expected = f.partial_cmp(&q);
                    assert_eq!(
                        cmp_results,
                        expected,
                        "{} <=> {}",
                        Polynomial::from(rqn.into_polynomial()),
                        rat
                    );
                }
            }
        }
    }

    fn get_float_test_cases_big() -> impl Iterator<Item = (i32, i32, i32, f64)> {
        fn range() -> impl Iterator<Item = i32> {
            -3..=3
        }
        range()
            .flat_map(|a| range().flat_map(move |b| range().map(move |c| (a, b, c))))
            .filter_map(|(a, b, c)| {
                if a == 0 && b <= 0 {
                    // skip cases that divide by zero; also skip cases that
                    // are rational with a negative denominator to save time
                    return None;
                }
                let af = f64::from(a);
                let bf = f64::from(b);
                let cf = f64::from(c);
                let d = bf * bf - 4.0 * af * cf;
                if d < 0.0 {
                    return None;
                }
                if a == 0 {
                    Some((a, b, c, -cf / bf))
                } else {
                    Some((a, b, c, (-bf + d.sqrt()) / (2.0 * af)))
                }
            })
    }

    #[test]
    #[ignore = "slow"]
    fn test_real_quadratic_number_cmp() {
        for (a1, b1, c1, f1) in get_float_test_cases_big() {
            let poly1 = QuadraticPolynomial {
                constant_term: c1.into(),
                linear_term: b1.into(),
                quadratic_term: a1.into(),
            };
            let rqn1 = RealQuadraticNumber::new(poly1.clone()).unwrap();
            for (a2, b2, c2, f2) in get_float_test_cases_big() {
                let poly2 = QuadraticPolynomial {
                    constant_term: c2.into(),
                    linear_term: b2.into(),
                    quadratic_term: a2.into(),
                };
                let rqn2 = RealQuadraticNumber::new(poly2.clone()).unwrap();
                println!(
                    "{}: {}: {} <=> {}",
                    Polynomial::from(poly1.clone()),
                    Polynomial::from(poly2.clone()),
                    f1,
                    f2
                );
                let cmp_results = rqn1.partial_cmp(&rqn2);
                let expected = f1.partial_cmp(&f2);
                assert_eq!(
                    cmp_results,
                    expected,
                    "{} <=> {}",
                    Polynomial::from(rqn1.into_polynomial()),
                    Polynomial::from(rqn2.into_polynomial())
                );
            }
        }
    }
}
