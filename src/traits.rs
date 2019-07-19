// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use num_integer::Integer;

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
