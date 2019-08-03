// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

// use super::util::{pairwise_op_eq_move, pairwise_op_eq_ref, pairwise_op_ref_ref};
use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use crate::traits::GCDAndLCM;
use crate::traits::GCD;
use num_traits::One;
use num_traits::Zero;
use std::borrow::Cow;
use std::mem;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;
use std::ops::{Add, AddAssign};

fn add_sub_assign<T: PolynomialCoefficient, AddSubAssign: Fn(&mut T::Element, T::Element)>(
    lhs: &mut Polynomial<T>,
    rhs: &Polynomial<T>,
    add_sub_assign: AddSubAssign,
) {
    let GCDAndLCM { gcd, lcm: divisor } = lhs.divisor.gcd_lcm(&rhs.divisor);
    let lhs_divisor = mem::replace(&mut lhs.divisor, divisor);
    let lhs_multiplier = T::divisor_to_element(Cow::Owned(lhs_divisor * &gcd));
    let rhs_multiplier = T::divisor_to_element(Cow::Owned(gcd * &rhs.divisor));
    while lhs.len() < rhs.len() {
        lhs.elements.push(Zero::zero());
    }
    for (index, lhs_element) in lhs.elements.iter_mut().enumerate() {
        *lhs_element *= &lhs_multiplier;
        if let Some(rhs_element) = rhs.elements.get(index) {
            add_sub_assign(lhs_element, rhs_element.clone() * &rhs_multiplier);
        }
    }
    lhs.normalize();
}

impl<T: PolynomialCoefficient> AddAssign for Polynomial<T> {
    fn add_assign(&mut self, rhs: Polynomial<T>) {
        add_sub_assign(self, &rhs, AddAssign::<T::Element>::add_assign);
    }
}

impl<'a, T: PolynomialCoefficient> AddAssign<&'a Polynomial<T>> for Polynomial<T> {
    fn add_assign(&mut self, rhs: &'a Polynomial<T>) {
        add_sub_assign(self, rhs, AddAssign::<T::Element>::add_assign);
    }
}

impl<T: PolynomialCoefficient> Add for Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(mut self, rhs: Polynomial<T>) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Add<&'a Polynomial<T>> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(mut self, rhs: &'a Polynomial<T>) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Add<Polynomial<T>> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(self, mut rhs: Polynomial<T>) -> Self::Output {
        rhs += self;
        rhs
    }
}

impl<'a, T: PolynomialCoefficient> Add for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(self, rhs: Self) -> Self::Output {
        let mut retval = self.clone();
        retval += rhs;
        retval
    }
}

impl<T: PolynomialCoefficient> Zero for Polynomial<T> {
    fn zero() -> Self {
        Default::default()
    }
    fn set_zero(&mut self) {
        self.elements.clear();
        self.divisor.set_one();
    }
    fn is_zero(&self) -> bool {
        self.is_empty()
    }
}

impl<T: PolynomialCoefficient> SubAssign for Polynomial<T> {
    fn sub_assign(&mut self, rhs: Polynomial<T>) {
        add_sub_assign(self, &rhs, SubAssign::<T::Element>::sub_assign);
    }
}

impl<'a, T: PolynomialCoefficient> SubAssign<&'a Polynomial<T>> for Polynomial<T> {
    fn sub_assign(&mut self, rhs: &'a Polynomial<T>) {
        add_sub_assign(self, rhs, SubAssign::<T::Element>::sub_assign);
    }
}

impl<T: PolynomialCoefficient> Sub for Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(mut self, rhs: Polynomial<T>) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Sub<&'a Polynomial<T>> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(mut self, rhs: &'a Polynomial<T>) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Sub<Polynomial<T>> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(self, rhs: Polynomial<T>) -> Self::Output {
        let mut lhs = self.clone();
        lhs -= rhs;
        lhs
    }
}

impl<'a, T: PolynomialCoefficient> Sub for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(self, rhs: Self) -> Self::Output {
        let mut lhs = self.clone();
        lhs -= rhs;
        lhs
    }
}

impl<T: PolynomialCoefficient> Neg for Polynomial<T> {
    type Output = Polynomial<T>;
    fn neg(self) -> Polynomial<T> {
        self.into_iter().map(Neg::neg).collect::<Vec<T>>().into()
    }
}

impl<T: PolynomialCoefficient> Neg for &'_ Polynomial<T> {
    type Output = Polynomial<T>;
    fn neg(self) -> Polynomial<T> {
        self.into_iter().map(Neg::neg).collect::<Vec<T>>().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::ops::util::tests::test_op_helper;
    #[test]
    fn test_add() {
        let test = |l: Polynomial<i32>, r: Polynomial<i32>, expected: &Polynomial<i32>| {
            test_op_helper(
                l,
                r,
                expected,
                |l, r| *l += r,
                |l, r| *l += r,
                |l, r| l + r,
                |l, r| l + r,
                |l, r| l + r,
                |l, r| l + r,
            );
        };
        test(
            vec![1, 2, 3, 4].into(),
            vec![5, 6, 7, 8].into(),
            &vec![6, 8, 10, 12].into(),
        );
        test(
            vec![1, 2, 3, 4, -1].into(),
            vec![5, 6, 7, 8, 1].into(),
            &vec![6, 8, 10, 12].into(),
        );
    }

    #[test]
    fn test_sub() {
        let test = |l: Polynomial<i32>, r: Polynomial<i32>, expected: &Polynomial<i32>| {
            test_op_helper(
                l,
                r,
                expected,
                |l, r| *l -= r,
                |l, r| *l -= r,
                |l, r| l - r,
                |l, r| l - r,
                |l, r| l - r,
                |l, r| l - r,
            );
        };
        test(
            vec![1, 2, 3, 4].into(),
            vec![8, 7, 6, 5].into(),
            &vec![-7, -5, -3, -1].into(),
        );
        test(
            vec![1, 2, 3, 4, 10].into(),
            vec![8, 7, 6, 5, 10].into(),
            &vec![-7, -5, -3, -1].into(),
        );
    }
}
