// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use std::fmt::Debug;
use std::convert::TryInto;
use crate::polynomial::Polynomial;
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::Zero;
use std::ops::AddAssign;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Rem;
use std::ops::SubAssign;

pub trait GCD<Rhs = Self> {
    type Output;
    fn gcd(&self, rhs: &Rhs) -> Self::Output;
}

impl<T: Integer> GCD for T {
    type Output = T;
    fn gcd(&self, rhs: &T) -> T {
        Integer::gcd(self, rhs)
    }
}

pub trait PolynomialEval<T> {
    fn eval(self, x: &T) -> T;
}

pub trait Derivative {
    type Output;
    fn derivative(self) -> Self::Output;
}

pub trait DivIsRemainderless<Rhs = Self>: Div<Rhs> {}

impl<T: Integer + Clone> DivIsRemainderless for Ratio<T> {}
impl<T: Integer + Clone> DivIsRemainderless<&'_ Ratio<T>> for Ratio<T> {}
impl<T: Integer + Clone> DivIsRemainderless<Ratio<T>> for &'_ Ratio<T> {}
impl<T: Integer + Clone> DivIsRemainderless for &'_ Ratio<T> {}
impl<T: Integer + Clone> DivIsRemainderless<T> for Ratio<T> {}
impl<T: Integer + Clone> DivIsRemainderless<&'_ T> for Ratio<T> {}
impl<T: Integer + Clone> DivIsRemainderless<T> for &'_ Ratio<T> {}
impl<'a, T: Integer + Clone> DivIsRemainderless<&'a T> for &'a Ratio<T> {}

impl DivIsRemainderless for f32 {}
impl DivIsRemainderless<&'_ f32> for f32 {}
impl DivIsRemainderless<f32> for &'_ f32 {}
impl DivIsRemainderless for &'_ f32 {}

pub trait DivRem<Rhs = Self>: Div<Rhs> + Rem<Rhs> + Sized {
    fn checked_div_rem(
        self,
        rhs: Rhs,
    ) -> Option<(<Self as Div<Rhs>>::Output, <Self as Rem<Rhs>>::Output)>;
    fn div_rem(self, rhs: Rhs) -> (<Self as Div<Rhs>>::Output, <Self as Rem<Rhs>>::Output) {
        self.checked_div_rem(rhs).expect("division by zero")
    }
}

macro_rules! impl_div_rem_int {
    ($t:ty) => {
        impl DivRem for $t {
            fn checked_div_rem(self, rhs: $t) -> Option<($t, $t)> {
                if rhs.is_zero() {
                    None
                } else {
                    Some(Integer::div_rem(&self, &rhs))
                }
            }
        }
        impl DivRem<$t> for &'_ $t {
            fn checked_div_rem(self, rhs: $t) -> Option<($t, $t)> {
                if rhs.is_zero() {
                    None
                } else {
                    Some(Integer::div_rem(&self, &rhs))
                }
            }
        }
        impl DivRem<&'_ $t> for $t {
            fn checked_div_rem(self, rhs: &$t) -> Option<($t, $t)> {
                if rhs.is_zero() {
                    None
                } else {
                    Some(Integer::div_rem(&self, &rhs))
                }
            }
        }
        impl DivRem for &'_ $t {
            fn checked_div_rem(self, rhs: &$t) -> Option<($t, $t)> {
                if rhs.is_zero() {
                    None
                } else {
                    Some(Integer::div_rem(&self, &rhs))
                }
            }
        }
    };
}

impl_div_rem_int!(u8);
impl_div_rem_int!(u16);
impl_div_rem_int!(u32);
impl_div_rem_int!(u64);
impl_div_rem_int!(u128);
impl_div_rem_int!(i8);
impl_div_rem_int!(i16);
impl_div_rem_int!(i32);
impl_div_rem_int!(i64);
impl_div_rem_int!(i128);
impl_div_rem_int!(usize);
impl_div_rem_int!(isize);
impl_div_rem_int!(BigInt);
impl_div_rem_int!(BigUint);

pub trait PolynomialDivSupported:
    Clone
    + AddAssign
    + SubAssign
    + Zero
    + for<'a> Div<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> DivIsRemainderless<&'a Self>
{
}

impl<T> PolynomialDivSupported for T where
    Self: Clone
        + AddAssign
        + SubAssign
        + Zero
        + for<'a> Div<&'a Self, Output = Self>
        + for<'a> Mul<&'a Self, Output = Self>
        + for<'a> DivIsRemainderless<&'a Self>
{
}

pub trait IsolatedRealRoot<T: Clone + Integer> {
    fn root_polynomial(&self) -> &Polynomial<T>;
    fn multiplicity(&self) -> usize;
    fn lower_bound(&self) -> &Ratio<T>;
    fn upper_bound(&self)-> &Ratio<T>;
}

pub trait MakeCoefficient<T> {
    fn make_coefficient(v: T) -> Self;
}

impl<I: TryInto<T> + Integer, T: Clone + Integer> MakeCoefficient<I> for Ratio<T> where I::Error: Debug {
    fn make_coefficient(v: I) -> Self {
        Ratio::from_integer(v.try_into().unwrap())
    }
}

macro_rules! impl_make_coefficient {
    ($t:ty) => {
        impl<T: TryInto<$t> + Integer> MakeCoefficient<T> for $t where T::Error: Debug {
            fn make_coefficient(v: T) -> $t {
                v.try_into().unwrap()
            }
        }
    };
}

impl_make_coefficient!(u8);
impl_make_coefficient!(u16);
impl_make_coefficient!(u32);
impl_make_coefficient!(u64);
impl_make_coefficient!(u128);
impl_make_coefficient!(i8);
impl_make_coefficient!(i16);
impl_make_coefficient!(i32);
impl_make_coefficient!(i64);
impl_make_coefficient!(i128);
impl_make_coefficient!(usize);
impl_make_coefficient!(isize);
impl_make_coefficient!(BigInt);
impl_make_coefficient!(BigUint);
