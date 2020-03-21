// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::polynomial::{Polynomial, PolynomialCoefficient};
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{CheckedDiv, CheckedMul, CheckedRem, NumAssign, One, Signed, ToPrimitive, Zero};
use std::{
    fmt,
    ops::{Add, Div, DivAssign, Mul},
};

/// GCD and LCM
///
/// ```no_build
/// let result = GCD::gcd_lcm(a, b);
/// assert_eq!(result.gcd * result.lcm, a * b);
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct GCDAndLCM<T> {
    pub gcd: T,
    pub lcm: T,
}

/// GCD and Bézout coefficients
///
/// ```no_build
/// let result = ExtendedGCD::extended_gcd(a, b);
/// assert_eq!(result.x * a + result.y * b, result.gcd);
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExtendedGCDResult<T> {
    pub gcd: T,
    pub x: T,
    pub y: T,
}

/// GCD, LCM, and Bézout coefficients
///
/// ```no_build
/// let result = ExtendedGCD::extended_gcd_lcm(a, b);
/// assert_eq!(result.x * a + result.y * b, result.gcd);
/// assert_eq!(result.gcd * result.lcm, a * b);
/// ```
#[derive(Copy, Clone, Debug, Eq, PartialEq, Hash)]
pub struct ExtendedGCDAndLCM<T> {
    pub gcd: T,
    pub x: T,
    pub y: T,
    pub lcm: T,
}

pub trait GCD<Rhs = Self> {
    type Output;
    #[must_use]
    fn gcd(&self, rhs: &Rhs) -> Self::Output {
        self.gcd_lcm(rhs).gcd
    }
    #[must_use]
    fn lcm(&self, rhs: &Rhs) -> Self::Output {
        self.gcd_lcm(rhs).lcm
    }
    #[must_use]
    fn gcd_lcm(&self, rhs: &Rhs) -> GCDAndLCM<Self::Output>;
}

pub trait ExtendedGCD<Rhs = Self>: GCD<Rhs> {
    #[must_use]
    fn extended_gcd(&self, rhs: &Rhs) -> ExtendedGCDResult<Self::Output> {
        let ExtendedGCDAndLCM { gcd, x, y, .. } = self.extended_gcd_lcm(rhs);
        ExtendedGCDResult { gcd, x, y }
    }
    #[must_use]
    fn extended_gcd_lcm(&self, rhs: &Rhs) -> ExtendedGCDAndLCM<Self::Output>;
}

macro_rules! impl_gcd_for_int {
    ($t:ty) => {
        impl GCD for $t {
            type Output = $t;
            fn gcd(&self, rhs: &$t) -> $t {
                Integer::gcd(self, rhs)
            }
            fn lcm(&self, rhs: &$t) -> $t {
                Integer::lcm(self, rhs)
            }
            fn gcd_lcm(&self, rhs: &$t) -> GCDAndLCM<$t> {
                let (gcd, lcm) = Integer::gcd_lcm(self, rhs);
                GCDAndLCM { gcd, lcm }
            }
        }
    };
}

macro_rules! impl_gcd_for_signed_int {
    ($t:ty) => {
        impl_gcd_for_int!($t);

        impl ExtendedGCD for $t {
            fn extended_gcd(&self, rhs: &$t) -> ExtendedGCDResult<$t> {
                let num_integer::ExtendedGcd { gcd, x, y, .. } = Integer::extended_gcd(self, rhs);
                ExtendedGCDResult { gcd, x, y }
            }
            fn extended_gcd_lcm(&self, rhs: &$t) -> ExtendedGCDAndLCM<$t> {
                let (num_integer::ExtendedGcd { gcd, x, y, .. }, lcm) =
                    Integer::extended_gcd_lcm(self, rhs);
                ExtendedGCDAndLCM { gcd, x, y, lcm }
            }
        }
    };
}

impl_gcd_for_int!(u8);
impl_gcd_for_signed_int!(i8);
impl_gcd_for_int!(u16);
impl_gcd_for_signed_int!(i16);
impl_gcd_for_int!(u32);
impl_gcd_for_signed_int!(i32);
impl_gcd_for_int!(u64);
impl_gcd_for_signed_int!(i64);
impl_gcd_for_int!(u128);
impl_gcd_for_signed_int!(i128);
impl_gcd_for_int!(usize);
impl_gcd_for_signed_int!(isize);
impl_gcd_for_int!(BigUint);
impl_gcd_for_signed_int!(BigInt);

impl<T: Integer + Clone + for<'a> Mul<&'a T, Output = T>> GCD for Ratio<T> {
    type Output = Self;
    fn gcd_lcm(&self, rhs: &Self) -> GCDAndLCM<Self> {
        if self.is_zero() {
            return GCDAndLCM {
                gcd: rhs.clone(),
                lcm: Zero::zero(),
            };
        }
        if rhs.is_zero() {
            return GCDAndLCM {
                gcd: self.clone(),
                lcm: Zero::zero(),
            };
        }
        let (gcd_numer, lcm_numer) =
            (self.numer().clone() * rhs.denom()).gcd_lcm(&(rhs.numer().clone() * self.denom()));
        let denom: T = self.denom().clone() * rhs.denom();
        GCDAndLCM {
            gcd: Ratio::new(gcd_numer, denom.clone()),
            lcm: Ratio::new(lcm_numer, denom),
        }
    }
}

impl<T: Integer + Clone + Signed + for<'a> Mul<&'a T, Output = T>> ExtendedGCD for Ratio<T> {
    fn extended_gcd_lcm(&self, rhs: &Self) -> ExtendedGCDAndLCM<Self> {
        let (gcd_numer, lcm_numer) = (self.numer().clone() * rhs.denom())
            .extended_gcd_lcm(&(rhs.numer().clone() * self.denom()));
        let denom: T = self.denom().clone() * rhs.denom();
        ExtendedGCDAndLCM {
            gcd: Ratio::new(gcd_numer.gcd, denom.clone()),
            x: gcd_numer.x.into(),
            y: gcd_numer.y.into(),
            lcm: Ratio::new(lcm_numer, denom),
        }
    }
}

/// Division with Remainder where division returns the Nearest representable result.
///
/// Unsigned Integer Examples:
/// ```ignored
/// # use algebraics::traits::DivRemNearest;
/// // Division by zero
/// assert_eq!((0u32).checked_div_rem_nearest(&0), None);
/// // Quotient is rounded down since remainder can't be negative
/// assert_eq!((5u32).div_rem_nearest(&8), (0, 5));
/// assert_eq!((8u32).div_rem_nearest(&5), (1, 3));
/// ```
///
/// Signed Integer Examples:
/// ```ignored
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
/// ```ignored
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
// FIXME: unignore doctest when pub
pub(crate) trait DivRemNearest<Rhs = Self>: Sized {
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

pub trait IntegerBits {
    const BITS: usize;
    /// returns Self::BITS
    fn type_bits(&self) -> usize {
        Self::BITS
    }
}

macro_rules! impl_integer_bits {
    ($($t:ty),*) => {
        $(
            impl IntegerBits for $t {
                const BITS: usize = (0 as $t).trailing_zeros() as usize;
            }
        )*
    };
}

impl_integer_bits!(u8, i8, u16, i16, u32, i32, u64, i64, u128, i128, usize, isize);

pub trait FloorLog2: Integer {
    /// returns floor(log2(self)) if self is positive
    /// returns `None` for zero or negative
    fn floor_log2(&self) -> Option<usize>;
}

pub trait CeilLog2: Integer {
    /// returns ceil(log2(self)) if self is positive
    /// returns `None` for zero or negative
    fn ceil_log2(&self) -> Option<usize>;
}

pub trait TrailingZeros: Integer {
    /// returns number of trailing zero bits in the two's complement representation of `Self`
    /// returns `None` for zero
    fn trailing_zeros(&self) -> Option<usize>;
}

macro_rules! impl_prim_trailing_zeros_and_log2 {
    ($t:ty) => {
        impl FloorLog2 for $t {
            fn floor_log2(&self) -> Option<usize> {
                if *self <= 0 {
                    None
                } else {
                    Some(<Self as IntegerBits>::BITS - self.leading_zeros() as usize - 1)
                }
            }
        }
        impl CeilLog2 for $t {
            fn ceil_log2(&self) -> Option<usize> {
                if *self <= 0 {
                    None
                } else {
                    Some(<Self as IntegerBits>::BITS - (*self - 1).leading_zeros() as usize)
                }
            }
        }
        impl TrailingZeros for $t {
            fn trailing_zeros(&self) -> Option<usize> {
                if *self == 0 {
                    None
                } else {
                    Some((*self).trailing_zeros() as usize)
                }
            }
        }
    };
}

impl_prim_trailing_zeros_and_log2!(u8);
impl_prim_trailing_zeros_and_log2!(u16);
impl_prim_trailing_zeros_and_log2!(u32);
impl_prim_trailing_zeros_and_log2!(u64);
impl_prim_trailing_zeros_and_log2!(u128);
impl_prim_trailing_zeros_and_log2!(usize);
impl_prim_trailing_zeros_and_log2!(i8);
impl_prim_trailing_zeros_and_log2!(i16);
impl_prim_trailing_zeros_and_log2!(i32);
impl_prim_trailing_zeros_and_log2!(i64);
impl_prim_trailing_zeros_and_log2!(i128);
impl_prim_trailing_zeros_and_log2!(isize);

impl CeilLog2 for BigUint {
    fn ceil_log2(&self) -> Option<usize> {
        if self.is_zero() {
            None
        } else {
            Some((self - 1u32).bits())
        }
    }
}

impl FloorLog2 for BigUint {
    fn floor_log2(&self) -> Option<usize> {
        if self.is_zero() {
            None
        } else {
            Some(self.bits() - 1)
        }
    }
}

impl TrailingZeros for BigUint {
    fn trailing_zeros(&self) -> Option<usize> {
        let ceil_log2 = self.ceil_log2();
        // handle self == 0 by returning None
        let ceil_log2 = ceil_log2?;
        if let Some(v) = self.to_u32() {
            return Some(v.trailing_zeros() as usize);
        }
        let mut bit = 1;
        while bit < ceil_log2 {
            bit <<= 1;
        }
        let mut retval = 0;
        let mut value = self.clone();
        while bit != 0 {
            let shifted_right = &value >> bit;
            if &shifted_right << bit == value {
                retval |= bit;
                value = shifted_right;
            }
            bit >>= 1;
        }
        Some(retval)
    }
}

impl CeilLog2 for BigInt {
    fn ceil_log2(&self) -> Option<usize> {
        if self.is_positive() {
            Some((self - 1u32).bits())
        } else {
            None
        }
    }
}

impl FloorLog2 for BigInt {
    fn floor_log2(&self) -> Option<usize> {
        if self.is_positive() {
            Some(self.bits() - 1)
        } else {
            None
        }
    }
}

impl TrailingZeros for BigInt {
    fn trailing_zeros(&self) -> Option<usize> {
        TrailingZeros::trailing_zeros(
            &self
                .abs()
                .to_biguint()
                .expect("abs should return non-negative values"),
        )
    }
}

pub(crate) trait IsolatedRealRoot<T: PolynomialCoefficient + Integer> {
    fn root_polynomial(&self) -> &Polynomial<T>;
    fn multiplicity(&self) -> usize;
    fn lower_bound(&self) -> &Ratio<T>;
    fn upper_bound(&self) -> &Ratio<T>;
}

#[derive(Copy, Clone, Hash, Eq, PartialEq, Ord, PartialOrd, Debug)]
pub struct CharacteristicZero;

impl Add for CharacteristicZero {
    type Output = Self;
    fn add(self, _rhs: Self) -> Self {
        CharacteristicZero
    }
}

impl Zero for CharacteristicZero {
    fn zero() -> Self {
        CharacteristicZero
    }
    fn is_zero(&self) -> bool {
        true
    }
}

pub trait RingCharacteristic: Zero + One {
    type Type: Zero + fmt::Debug;
    fn characteristic(&self) -> Self::Type;
}

impl<T: RingCharacteristic<Type = CharacteristicZero> + Clone + Integer> RingCharacteristic
    for Ratio<T>
{
    type Type = CharacteristicZero;
    fn characteristic(&self) -> CharacteristicZero {
        CharacteristicZero
    }
}

macro_rules! impl_characteristic_zero {
    ($t:ty) => {
        impl RingCharacteristic for $t {
            type Type = CharacteristicZero;
            fn characteristic(&self) -> CharacteristicZero {
                CharacteristicZero
            }
        }
    };
}

impl_characteristic_zero!(u8);
impl_characteristic_zero!(i8);
impl_characteristic_zero!(u16);
impl_characteristic_zero!(i16);
impl_characteristic_zero!(u32);
impl_characteristic_zero!(i32);
impl_characteristic_zero!(u64);
impl_characteristic_zero!(i64);
impl_characteristic_zero!(u128);
impl_characteristic_zero!(i128);
impl_characteristic_zero!(usize);
impl_characteristic_zero!(isize);
impl_characteristic_zero!(BigUint);
impl_characteristic_zero!(BigInt);

pub trait ExactDiv<Rhs = Self>: Sized {
    type Output;
    #[must_use]
    fn exact_div(self, rhs: Rhs) -> Self::Output {
        self.checked_exact_div(rhs).expect("exact division failed")
    }
    #[must_use]
    fn checked_exact_div(self, rhs: Rhs) -> Option<Self::Output>;
}

pub trait ExactDivAssign<Rhs = Self>: ExactDiv<Rhs, Output = Self> {
    fn exact_div_assign(&mut self, rhs: Rhs) {
        if let Err(()) = self.checked_exact_div_assign(rhs) {
            panic!("exact division failed");
        }
    }
    fn checked_exact_div_assign(&mut self, rhs: Rhs) -> Result<(), ()>;
}

/// division always produces exact results except for division by zero, overflow, or similar
pub trait AlwaysExactDiv<Rhs = Self>:
    ExactDiv<Rhs> + Div<Rhs/*, Output = <Self as ExactDiv<Rhs>>::Output*/>
{
}

/// division always produces exact results except for division by zero, overflow, or similar
pub trait AlwaysExactDivAssign<Rhs = Self>:
    AlwaysExactDiv<Rhs>
    + ExactDivAssign<Rhs>
    + DivAssign<Rhs>
    + ExactDiv<Rhs, Output = Self>
    + Div<Rhs, Output = Self>
{
}

macro_rules! impl_exact_div_for_ratio {
    (($($lifetimes:tt),*), $t:ident, $lhs:ty, $rhs:ty) => {
        impl<$($lifetimes,)* $t> ExactDiv<$rhs> for $lhs
        where
            $t: Clone + Integer,
        {
            type Output = Ratio<$t>;
            fn exact_div(self, rhs: $rhs) -> Self::Output {
                self.div(rhs)
            }
            fn checked_exact_div(self, rhs: $rhs) -> Option<Self::Output> {
                if rhs.is_zero() {
                    None
                } else {
                    Some(self.div(rhs))
                }
            }
        }

        impl<$($lifetimes,)* $t> AlwaysExactDiv<$rhs> for $lhs
        where
            $t: Clone + Integer,
        {
        }
    };
    (assign ($($lifetimes:tt),*), $t:ident, $lhs:ty, $rhs:ty) => {
        impl_exact_div_for_ratio!(($($lifetimes),*), $t, $lhs, $rhs);

        impl<$($lifetimes,)* $t> ExactDivAssign<$rhs> for $lhs
        where
            $t: Clone + Integer + NumAssign,
        {
            fn exact_div_assign(&mut self, rhs: $rhs) {
                self.div_assign(rhs);
            }
            fn checked_exact_div_assign(&mut self, rhs: $rhs) -> Result<(), ()> {
                if rhs.is_zero() {
                    Err(())
                } else {
                    self.div_assign(rhs);
                    Ok(())
                }
            }
        }

        impl<$($lifetimes,)* $t> AlwaysExactDivAssign<$rhs> for $lhs
        where
            $t: Clone + Integer + NumAssign,
        {
        }
    };
}

impl_exact_div_for_ratio!(assign(), T, Ratio<T>, T);
impl_exact_div_for_ratio!(assign(), T, Ratio<T>, Ratio<T>);
impl_exact_div_for_ratio!(assign ('r), T, Ratio<T>, &'r T);
impl_exact_div_for_ratio!(assign ('r), T, Ratio<T>, &'r Ratio<T>);

impl_exact_div_for_ratio!(('l), T, &'l Ratio<T>, T);
impl_exact_div_for_ratio!(('l), T, &'l Ratio<T>, Ratio<T>);
impl_exact_div_for_ratio!(('l, 'r), T, &'l Ratio<T>, &'r T);
impl_exact_div_for_ratio!(('l, 'r), T, &'l Ratio<T>, &'r Ratio<T>);

fn checked_div_rem<T: CheckedDiv + CheckedRem>(lhs: &T, rhs: &T) -> Option<(T, T)> {
    Some((lhs.checked_div(rhs)?, lhs.checked_rem(rhs)?))
}

fn bigint_checked_div_rem<T: Integer>(lhs: &T, rhs: &T) -> Option<(T, T)> {
    if rhs.is_zero() {
        None
    } else {
        Some(lhs.div_rem(rhs))
    }
}

macro_rules! impl_exact_div_for_int {
    ($t:ident, $checked_div_rem:ident) => {
        impl<'l, 'r> ExactDiv<&'r $t> for &'l $t {
            type Output = $t;
            fn exact_div(self, rhs: &$t) -> $t {
                let (retval, remainder) = self.div_rem(rhs);
                assert!(remainder.is_zero(), "inexact division");
                retval
            }
            fn checked_exact_div(self, rhs: &$t) -> Option<$t> {
                let (retval, remainder) = $checked_div_rem(self, rhs)?;
                if remainder.is_zero() {
                    Some(retval)
                } else {
                    None
                }
            }
        }

        impl ExactDiv<&'_ $t> for $t {
            type Output = $t;
            fn exact_div(self, rhs: &$t) -> $t {
                (&self).exact_div(rhs)
            }
            fn checked_exact_div(self, rhs: &$t) -> Option<Self::Output> {
                (&self).checked_exact_div(rhs)
            }
        }

        impl ExactDiv<$t> for &'_ $t {
            type Output = $t;
            fn exact_div(self, rhs: $t) -> $t {
                self.exact_div(&rhs)
            }
            fn checked_exact_div(self, rhs: $t) -> Option<Self::Output> {
                self.checked_exact_div(&rhs)
            }
        }

        impl ExactDiv<$t> for $t {
            type Output = $t;
            fn exact_div(self, rhs: $t) -> $t {
                (&self).exact_div(&rhs)
            }
            fn checked_exact_div(self, rhs: $t) -> Option<Self::Output> {
                (&self).checked_exact_div(&rhs)
            }
        }

        impl ExactDivAssign<&'_ $t> for $t {
            fn exact_div_assign(&mut self, rhs: &$t) {
                *self = (&*self).exact_div(rhs);
            }
            fn checked_exact_div_assign(&mut self, rhs: &$t) -> Result<(), ()> {
                (&*self)
                    .checked_exact_div(rhs)
                    .map(|v| {
                        *self = v;
                    })
                    .ok_or(())
            }
        }

        impl ExactDivAssign<$t> for $t {
            fn exact_div_assign(&mut self, rhs: $t) {
                *self = (&*self).exact_div(rhs);
            }
            fn checked_exact_div_assign(&mut self, rhs: $t) -> Result<(), ()> {
                (&*self)
                    .checked_exact_div(rhs)
                    .map(|v| {
                        *self = v;
                    })
                    .ok_or(())
            }
        }
    };
}

impl_exact_div_for_int!(u8, checked_div_rem);
impl_exact_div_for_int!(i8, checked_div_rem);
impl_exact_div_for_int!(u16, checked_div_rem);
impl_exact_div_for_int!(i16, checked_div_rem);
impl_exact_div_for_int!(u32, checked_div_rem);
impl_exact_div_for_int!(i32, checked_div_rem);
impl_exact_div_for_int!(u64, checked_div_rem);
impl_exact_div_for_int!(i64, checked_div_rem);
impl_exact_div_for_int!(u128, checked_div_rem);
impl_exact_div_for_int!(i128, checked_div_rem);
impl_exact_div_for_int!(usize, checked_div_rem);
impl_exact_div_for_int!(isize, checked_div_rem);

impl_exact_div_for_int!(BigInt, bigint_checked_div_rem);
impl_exact_div_for_int!(BigUint, bigint_checked_div_rem);

pub trait IntervalUnion<Rhs> {
    type Output;
    fn interval_union(self, rhs: Rhs) -> Self::Output;
}

pub trait IntervalUnionAssign<Rhs> {
    fn interval_union_assign(&mut self, rhs: Rhs);
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;

    #[test]
    fn test_gcd_lcm() {
        let a = Ratio::new(12, 621_934i128);
        let b = Ratio::new(48, 12934);
        assert_eq!(a.gcd(&b), Ratio::new(6, 69_345_641));
        assert_eq!(a.lcm(&b), Ratio::new(24, 29));
    }

    #[test]
    fn test_trailing_zeros() {
        let one = BigUint::one();
        for i in 0..=256 {
            for j in 0..=i {
                let v = (&one << dbg!(i)) | (&one << dbg!(j));
                assert_eq!(v.trailing_zeros(), Some(j));
            }
        }
    }

    #[test]
    fn test_ceil_log2() {
        assert_eq!(BigUint::zero().ceil_log2(), None);
        assert_eq!(BigInt::zero().ceil_log2(), None);
        assert_eq!(0.ceil_log2(), None);
        let one = BigUint::one();
        assert_eq!(one.ceil_log2(), Some(0));
        assert_eq!(BigInt::one().ceil_log2(), Some(0));
        assert_eq!(1.ceil_log2(), Some(0));
        for i in 0..=256 {
            for j in 0..=i {
                let v = (&one << dbg!(i)) + (&one << dbg!(j));
                assert_eq!(v.ceil_log2(), Some(i + 1));
                assert_eq!(BigInt::from(v).ceil_log2(), Some(i + 1));
                if i < 32 {
                    if let Some(v) = (1u32 << i).checked_add(1 << j) {
                        assert_eq!(v.ceil_log2(), Some(i + 1));
                    }
                }
            }
        }
    }

    #[test]
    fn test_floor_log2() {
        assert_eq!(BigUint::zero().floor_log2(), None);
        assert_eq!(BigInt::zero().floor_log2(), None);
        assert_eq!(0.floor_log2(), None);
        let one = BigUint::one();
        assert_eq!(one.floor_log2(), Some(0));
        assert_eq!(BigInt::one().floor_log2(), Some(0));
        assert_eq!(1.floor_log2(), Some(0));
        for i in 0..=256 {
            for j in 0..=i {
                let v = (&one << dbg!(i)) | (&one << dbg!(j));
                assert_eq!(v.floor_log2(), Some(i));
                assert_eq!(BigInt::from(v).floor_log2(), Some(i));
                if i < 32 {
                    let v = (1u32 << i) | (1 << j);
                    assert_eq!(v.floor_log2(), Some(i), "{:#x}", v);
                }
            }
        }
    }
}
