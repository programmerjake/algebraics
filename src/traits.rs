// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{CheckedDiv, CheckedMul, Signed, Zero};

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct GCDAndLCM<T> {
    pub gcd: T,
    pub lcm: T,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExtendedGCDResult<T> {
    pub gcd: T,
    pub x: T,
    pub y: T,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExtendedGCDAndLCM<T> {
    pub gcd: T,
    pub x: T,
    pub y: T,
    pub lcm: T,
}

pub trait GCD<Rhs = Self> {
    type Output;
    fn gcd(&self, rhs: &Rhs) -> Self::Output {
        self.gcd_lcm(rhs).gcd
    }
    fn lcm(&self, rhs: &Rhs) -> Self::Output {
        self.gcd_lcm(rhs).lcm
    }
    fn gcd_lcm(&self, rhs: &Rhs) -> GCDAndLCM<Self::Output>;
}

pub trait ExtendedGCD<Rhs = Self>: GCD<Rhs> {
    fn extended_gcd(&self, rhs: &Rhs) -> ExtendedGCDResult<Self::Output> {
        let ExtendedGCDAndLCM { gcd, x, y, .. } = self.extended_gcd_lcm(rhs);
        ExtendedGCDResult { gcd, x, y }
    }
    fn extended_gcd_lcm(&self, rhs: &Rhs) -> ExtendedGCDAndLCM<Self::Output>;
}

impl<T: Integer + Clone + Signed> GCD for T {
    type Output = T;
    fn gcd(&self, rhs: &T) -> T {
        Integer::gcd(self, rhs)
    }
    fn lcm(&self, rhs: &T) -> T {
        Integer::lcm(self, rhs)
    }
    fn gcd_lcm(&self, rhs: &T) -> GCDAndLCM<T> {
        let (gcd, lcm) = Integer::gcd_lcm(self, rhs);
        GCDAndLCM { gcd, lcm }
    }
}
impl<T: Integer + Clone + Signed> ExtendedGCD for T {
    fn extended_gcd(&self, rhs: &T) -> ExtendedGCDResult<Self::Output> {
        let num_integer::ExtendedGcd { gcd, x, y, .. } = Integer::extended_gcd(self, rhs);
        ExtendedGCDResult { gcd, x, y }
    }
    fn extended_gcd_lcm(&self, rhs: &T) -> ExtendedGCDAndLCM<Self::Output> {
        let (num_integer::ExtendedGcd { gcd, x, y, .. }, lcm) =
            Integer::extended_gcd_lcm(self, rhs);
        ExtendedGCDAndLCM { gcd, x, y, lcm }
    }
}

/// Division with Remainder where division returns the Nearest representable result.
///
/// Unsigned Integer Examples:
/// ```
/// # use algebraics::traits::DivRemNearest;
/// // Division by zero
/// assert_eq!((0u32).checked_div_rem_nearest(&0), None);
/// // Quotient is rounded down since remainder can't be negative
/// assert_eq!((5u32).div_rem_nearest(&8), (0, 5));
/// assert_eq!((8u32).div_rem_nearest(&5), (1, 3));
/// ```
///
/// Signed Integer Examples:
/// ```
/// # use algebraics::traits::DivRemNearest;
/// // Division by zero
/// assert_eq!((0i32).checked_div_rem_nearest(&0), None);
/// // Overflow
/// assert_eq!((-0x80i8).checked_div_rem_nearest(&-1), None);
/// // Quotient is rounded to nearest
/// assert_eq!((4i32).div_rem_nearest(&9), (0, 4));
/// assert_eq!((5i32).div_rem_nearest(&9), (1, -4));
/// // Halfway cases are rounded towards zero
/// assert_eq!((4i32).div_rem_nearest(&8), (0, 4));
/// assert_eq!((-15i32).div_rem_nearest(&10), (-1, -5));
/// ```
///
/// Rational Examples:
/// ```
/// # use algebraics::traits::DivRemNearest;
/// # use num_rational::{BigRational, ParseRatioError};
/// # use num_traits::Zero;
/// let ratio = str::parse::<BigRational>;
/// // Division by zero
/// assert_eq!(ratio("0")?.checked_div_rem_nearest(&ratio("0")?), None);
/// // All divisions produce a zero remainder
/// assert_eq!(ratio("3/4")?.div_rem_nearest(&ratio("-5/7")?), (ratio("-21/20")?, ratio("0")?));
/// # Ok::<(), ParseRatioError>(())
/// ```
pub trait DivRemNearest<Rhs = Self>: Sized {
    type DivOutput;
    type RemOutput;
    fn checked_div_rem_nearest(&self, rhs: &Rhs) -> Option<(Self::DivOutput, Self::RemOutput)>;
    fn div_rem_nearest(&self, rhs: &Rhs) -> (Self::DivOutput, Self::RemOutput) {
        self.checked_div_rem_nearest(rhs).expect("division by zero")
    }
}

impl<T: Clone + Integer + CheckedMul> DivRemNearest for Ratio<T> {
    type DivOutput = Ratio<T>;
    type RemOutput = Ratio<T>;
    fn checked_div_rem_nearest(&self, rhs: &Self) -> Option<(Self, Self)> {
        Some((self.checked_div(rhs)?, Zero::zero()))
    }
}

macro_rules! impl_div_rem_signed_int {
    ($t:ty, $u:ty) => {
        impl DivRemNearest for $t {
            type DivOutput = $t;
            type RemOutput = $t;
            fn checked_div_rem_nearest(&self, rhs: &$t) -> Option<($t, $t)> {
                let lhs = *self;
                let rhs = *rhs;
                if rhs == 0 {
                    return None; // division by zero
                }
                if rhs == -1 && lhs == <$t>::min_value() {
                    return None; // overflow
                }
                let mut quotient = lhs / rhs;
                let mut remainder = lhs % rhs;
                let rhs_magnitude = rhs.wrapping_abs() as $u;
                let remainder_magnitude = remainder.wrapping_abs() as $u;
                if rhs != <$t>::min_value() && remainder_magnitude > rhs_magnitude / 2 {
                    let (quotient_offset, remainder_offset) =
                        if rhs < 0 { (-1, rhs) } else { (1, -rhs) };
                    quotient = quotient.checked_add(quotient_offset)?;
                    remainder = remainder.checked_add(remainder_offset)?;
                }
                Some((quotient, remainder))
            }
        }
    };
}

macro_rules! impl_div_rem_unsigned_int {
    ($t:ty) => {
        impl DivRemNearest for $t {
            type DivOutput = $t;
            type RemOutput = $t;
            fn checked_div_rem_nearest(&self, rhs: &$t) -> Option<($t, $t)> {
                if *rhs == 0 {
                    return None;
                }
                Some((self / rhs, self % rhs))
            }
        }
    };
}

impl_div_rem_unsigned_int!(u8);
impl_div_rem_unsigned_int!(u16);
impl_div_rem_unsigned_int!(u32);
impl_div_rem_unsigned_int!(u64);
impl_div_rem_unsigned_int!(u128);
impl_div_rem_unsigned_int!(usize);
impl_div_rem_signed_int!(i8, u8);
impl_div_rem_signed_int!(i16, u16);
impl_div_rem_signed_int!(i32, u32);
impl_div_rem_signed_int!(i64, u64);
impl_div_rem_signed_int!(i128, u128);
impl_div_rem_signed_int!(isize, usize);

impl DivRemNearest for BigInt {
    type DivOutput = BigInt;
    type RemOutput = BigInt;
    fn checked_div_rem_nearest(&self, rhs: &BigInt) -> Option<(BigInt, BigInt)> {
        if rhs.is_zero() {
            return None;
        }
        let (mut quotient, mut remainder) = self.div_rem(rhs);
        let rhs_magnitude = rhs.abs();
        let remainder_magnitude = remainder.abs();
        if &rhs_magnitude - &remainder_magnitude > remainder_magnitude {
            if rhs.is_negative() {
                quotient -= 1;
                remainder -= rhs_magnitude;
            } else {
                quotient += 1;
                remainder += rhs_magnitude;
            }
        }
        Some((quotient, remainder))
    }
}

impl DivRemNearest for BigUint {
    type DivOutput = BigUint;
    type RemOutput = BigUint;
    fn checked_div_rem_nearest(&self, rhs: &BigUint) -> Option<(BigUint, BigUint)> {
        if rhs.is_zero() {
            return None;
        }
        Some(self.div_rem(rhs))
    }
}

pub trait IsolatedRealRoot<T: PolynomialCoefficient + Integer> {
    fn root_polynomial(&self) -> &Polynomial<T>;
    fn multiplicity(&self) -> usize;
    fn lower_bound(&self) -> &Ratio<T>;
    fn upper_bound(&self) -> &Ratio<T>;
}
