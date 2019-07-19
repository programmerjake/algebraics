// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use num_traits::Zero;
use std::ops::{AddAssign, Mul, MulAssign};

impl<'a, T: Zero + AddAssign> Mul for &'a Polynomial<T>
where
    &'a T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: &'a Polynomial<T>) -> Polynomial<T> {
        if self.is_zero() || rhs.is_zero() {
            return Zero::zero();
        }
        let mut retval_coefficients = Vec::with_capacity(self.len() + rhs.len());
        for l_index in 0..self.len() {
            if self.coefficients[l_index].is_zero() {
                continue;
            }
            for r_index in 0..rhs.len() {
                let index = l_index + r_index;
                if index == retval_coefficients.len() {
                    retval_coefficients
                        .push(&self.coefficients[l_index] * &rhs.coefficients[r_index]);
                } else {
                    retval_coefficients[index] +=
                        &self.coefficients[l_index] * &rhs.coefficients[r_index];
                }
            }
        }
        retval_coefficients.into()
    }
}

impl<'a, T: Zero + AddAssign> Mul<Polynomial<T>> for &'a Polynomial<T>
where
    for<'b> &'b T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    fn mul(self, rhs: Polynomial<T>) -> Polynomial<T> {
        self * &rhs
    }
}

impl<'a, T: Zero + AddAssign> Mul<&'a Polynomial<T>> for Polynomial<T>
where
    for<'b> &'b T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    fn mul(self, rhs: &'a Polynomial<T>) -> Polynomial<T> {
        &self * rhs
    }
}

impl<T: Zero + AddAssign> Mul for Polynomial<T>
where
    for<'a> &'a T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    fn mul(self, rhs: Polynomial<T>) -> Polynomial<T> {
        &self * &rhs
    }
}

impl<T: Zero + AddAssign> MulAssign for Polynomial<T>
where
    for<'a> &'a T: Mul<Output = T>,
{
    fn mul_assign(&mut self, rhs: Polynomial<T>) {
        *self = &*self * rhs;
    }
}

impl<'a, T: Zero + AddAssign> MulAssign<&'a Polynomial<T>> for Polynomial<T>
where
    for<'b> &'b T: Mul<Output = T>,
{
    fn mul_assign(&mut self, rhs: &'a Polynomial<T>) {
        *self = &*self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::ops::util::tests::test_op_helper;
    #[test]
    fn test_mul() {
        let test = |l: Polynomial<i32>, r: Polynomial<i32>, expected: &Polynomial<i32>| {
            test_op_helper(
                l,
                r,
                expected,
                |l, r| *l *= r,
                |l, r| *l *= r,
                |l, r| l * r,
                |l, r| l * r,
                |l, r| l * r,
                |l, r| l * r,
            );
        };
        test(
            vec![10, 11, 12].into(),
            vec![10, -11, 3, 2, 1].into(),
            &vec![100, 0, 29, -79, 68, 35, 12].into(),
        );
    }
}
