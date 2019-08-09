// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use num_traits::{One, Zero};
use std::borrow::Cow;
use std::ops::{AddAssign, Mul, MulAssign};

impl<'a, T: PolynomialCoefficient> Mul for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: &Polynomial<T>) -> Polynomial<T> {
        if self.is_zero() || rhs.is_zero() {
            return Zero::zero();
        }
        let divisor = self.divisor.clone() * &rhs.divisor;
        let mut elements = Vec::with_capacity(self.len() + rhs.len());
        for l_index in 0..self.len() {
            if self.elements[l_index].is_zero() {
                continue;
            }
            for r_index in 0..rhs.len() {
                let index = l_index + r_index;
                if index == elements.len() {
                    elements.push(self.elements[l_index].clone() * &rhs.elements[r_index]);
                } else {
                    AddAssign::<T::Element>::add_assign(
                        &mut elements[index],
                        self.elements[l_index].clone() * &rhs.elements[r_index],
                    );
                }
            }
        }
        Polynomial { elements, divisor }.into_normalized()
    }
}

impl<'a, T: PolynomialCoefficient> Mul<Polynomial<T>> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: Polynomial<T>) -> Polynomial<T> {
        self * &rhs
    }
}

impl<'a, T: PolynomialCoefficient> Mul<&'a Polynomial<T>> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: &Polynomial<T>) -> Polynomial<T> {
        &self * rhs
    }
}

impl<T: PolynomialCoefficient> Mul for Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: Polynomial<T>) -> Polynomial<T> {
        &self * &rhs
    }
}

impl<T: PolynomialCoefficient> MulAssign for Polynomial<T> {
    fn mul_assign(&mut self, rhs: Polynomial<T>) {
        *self = &*self * rhs;
    }
}

impl<'a, T: PolynomialCoefficient> MulAssign<&'a Polynomial<T>> for Polynomial<T> {
    fn mul_assign(&mut self, rhs: &Polynomial<T>) {
        *self = &*self * rhs;
    }
}

pub(crate) fn mul_assign_by_element_nonnormalized<T: PolynomialCoefficient>(
    lhs: &mut Polynomial<T>,
    rhs: &T::Element,
) {
    lhs.elements.iter_mut().for_each(|v| *v *= rhs);
}

fn mul_single<T: PolynomialCoefficient>(lhs: Cow<Polynomial<T>>, rhs: Cow<T>) -> Polynomial<T> {
    let lhs = match lhs {
        Cow::Owned(mut lhs) => {
            mul_assign_single(&mut lhs, rhs);
            return lhs;
        }
        Cow::Borrowed(lhs) => lhs,
    };
    let (rhs_numerator, rhs_divisor) = T::coefficient_to_element(rhs);
    Polynomial {
        elements: lhs
            .elements
            .iter()
            .map(|l| l.clone() * &rhs_numerator)
            .collect(),
        divisor: rhs_divisor * &lhs.divisor,
    }
    .into_normalized()
}

fn mul_assign_single<T: PolynomialCoefficient>(lhs: &mut Polynomial<T>, rhs: Cow<T>) {
    let (rhs_numerator, rhs_divisor) = T::coefficient_to_element(rhs);
    mul_assign_by_element_nonnormalized(lhs, &rhs_numerator);
    MulAssign::<T::Divisor>::mul_assign(&mut lhs.divisor, rhs_divisor);
    lhs.normalize();
}

impl<'a, T: PolynomialCoefficient> Mul<&'a T> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: &T) -> Polynomial<T> {
        mul_single(Cow::Borrowed(self), Cow::Borrowed(rhs))
    }
}

impl<'a, T: PolynomialCoefficient> Mul<T> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: T) -> Polynomial<T> {
        mul_single(Cow::Borrowed(self), Cow::Owned(rhs))
    }
}

impl<'a, T: PolynomialCoefficient> Mul<&'a T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: &T) -> Polynomial<T> {
        mul_single(Cow::Owned(self), Cow::Borrowed(rhs))
    }
}

impl<T: PolynomialCoefficient> Mul<T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn mul(self, rhs: T) -> Polynomial<T> {
        mul_single(Cow::Owned(self), Cow::Owned(rhs))
    }
}

impl<T: PolynomialCoefficient> MulAssign<T> for Polynomial<T> {
    fn mul_assign(&mut self, rhs: T) {
        mul_assign_single(self, Cow::Owned(rhs));
    }
}

impl<'a, T: PolynomialCoefficient> MulAssign<&'a T> for Polynomial<T> {
    fn mul_assign(&mut self, rhs: &T) {
        mul_assign_single(self, Cow::Borrowed(rhs));
    }
}

impl<T: PolynomialCoefficient> One for Polynomial<T> {
    fn one() -> Self {
        Self {
            elements: vec![One::one()],
            divisor: One::one(),
        }
    }
    fn set_one(&mut self) {
        if self.elements.is_empty() {
            self.elements.push(One::one());
        } else {
            self.elements.drain(1..);
            self.elements[0].set_one();
        }
        self.divisor.set_one();
    }
    #[inline]
    fn is_one(&self) -> bool {
        match &*self.elements {
            [element] => element.is_one() && self.divisor.is_one(),
            _ => false,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::test_op_helper;
    use num_rational::Ratio;
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

    #[test]
    fn test_mul_rational() {
        let test = |l: Polynomial<Ratio<i64>>,
                    r: Polynomial<Ratio<i64>>,
                    expected: &Polynomial<Ratio<i64>>| {
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
        let r = |n: i64, d: i64| Ratio::new(n, d);
        test(
            vec![r(10, 7), r(11, 7), r(12, 7)].into(),
            vec![r(10, 29), r(-11, 29), r(3, 29), r(2, 29), r(1, 29)].into(),
            &vec![
                r(100, 203),
                r(0, 1),
                r(1, 7),
                r(-79, 203),
                r(68, 203),
                r(5, 29),
                r(12, 203),
            ]
            .into(),
        );
    }
}
