// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::Zero;
use std::ops::Div;
use std::ops::Rem;

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

pub trait Derivative<Output = Self> {
    fn derivative(self) -> Output;
}

pub trait DivRem<Rhs = Self>: Div<Rhs> + Rem<Rhs> {
    fn div_rem(&self, rhs: &Rhs) -> (<Self as Div<Rhs>>::Output, <Self as Rem<Rhs>>::Output);
}

macro_rules! impl_div_rem {
    ($($t:ty),*) => {
        $(
            impl DivRem for $t {
                fn div_rem(&self, rhs: &Self) -> (Self, Self) {
                    Integer::div_rem(self, rhs)
                }
            }
        )*
    };
}

impl_div_rem!(u8, u16, u32, u64, u128, i8, i16, i32, i64, i128, usize, isize, BigInt, BigUint);

impl<T: Integer + Clone> DivRem for Ratio<T> {
    fn div_rem(&self, rhs: &Self) -> (Self, Self) {
        (self / rhs, Zero::zero())
    }
}
