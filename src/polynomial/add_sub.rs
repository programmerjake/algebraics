// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

// use super::util::{pairwise_op_eq_move, pairwise_op_eq_ref, pairwise_op_ref_ref};
use crate::{
    polynomial::{Polynomial, PolynomialCoefficient},
    traits::{ExactDiv, GCDAndLCM, GCD},
};
use num_traits::{CheckedAdd, CheckedSub, One, Zero};
use std::{
    borrow::Cow,
    mem,
    ops::{Add, AddAssign, Neg, Sub, SubAssign},
};

fn add_sub_assign<T: PolynomialCoefficient, AddSubAssign: Fn(&mut T::Element, T::Element)>(
    lhs: &mut Polynomial<T>,
    rhs: &Polynomial<T>,
    add_sub_assign: AddSubAssign,
) {
    let source_element = match lhs.elements.first().or_else(|| rhs.elements.first()) {
        Some(v) => v,
        None => return,
    };
    let GCDAndLCM { gcd, lcm: divisor } = lhs.divisor.gcd_lcm(&rhs.divisor);
    let lhs_divisor = mem::replace(&mut lhs.divisor, divisor);
    let lhs_multiplier = T::divisor_to_element(
        Cow::Owned(rhs.divisor.clone().exact_div(&gcd)),
        Cow::Borrowed(source_element),
    );
    let rhs_multiplier = T::divisor_to_element(
        Cow::Owned(ExactDiv::<T::Divisor>::exact_div(lhs_divisor, gcd)),
        Cow::Borrowed(source_element),
    );
    while lhs.len() < rhs.len() {
        lhs.elements
            .push(T::make_zero_element(Cow::Borrowed(&rhs.elements[0])));
    }
    for (index, lhs_element) in lhs.elements.iter_mut().enumerate() {
        *lhs_element *= &lhs_multiplier;
        if let Some(rhs_element) = rhs.elements.get(index) {
            add_sub_assign(lhs_element, rhs_element.clone() * &rhs_multiplier);
        }
    }
    lhs.normalize();
}

fn add_sub_assign_single<
    T: PolynomialCoefficient,
    AddSubAssign: Fn(&mut T::Element, T::Element),
>(
    lhs: &mut Polynomial<T>,
    rhs: Cow<T>,
    add_sub_assign: AddSubAssign,
) {
    let (rhs_numerator, rhs_divisor) = T::coefficient_to_element(rhs);
    let GCDAndLCM { gcd, lcm: divisor } = lhs.divisor.gcd_lcm(&rhs_divisor);
    let lhs_divisor = mem::replace(&mut lhs.divisor, divisor);
    let lhs_multiplier = T::divisor_to_element(
        Cow::Owned(lhs_divisor * &gcd),
        Cow::Borrowed(&rhs_numerator),
    );
    let rhs_multiplier = T::divisor_to_element(
        Cow::Owned(gcd * &rhs_divisor),
        Cow::Borrowed(&rhs_numerator),
    );
    if lhs.is_empty() {
        lhs.elements
            .push(T::make_zero_element(Cow::Borrowed(&rhs_numerator)));
    }
    lhs.elements[0] *= &lhs_multiplier;
    add_sub_assign(&mut lhs.elements[0], rhs_numerator * &rhs_multiplier);
    lhs.normalize();
}

impl<T: PolynomialCoefficient> AddAssign for Polynomial<T> {
    fn add_assign(&mut self, rhs: Polynomial<T>) {
        add_sub_assign(self, &rhs, AddAssign::<T::Element>::add_assign);
    }
}

impl<'a, T: PolynomialCoefficient> AddAssign<&'a Polynomial<T>> for Polynomial<T> {
    fn add_assign(&mut self, rhs: &Polynomial<T>) {
        add_sub_assign(self, rhs, AddAssign::<T::Element>::add_assign);
    }
}

impl<T: PolynomialCoefficient> AddAssign<T> for Polynomial<T> {
    fn add_assign(&mut self, rhs: T) {
        add_sub_assign_single(self, Cow::Owned(rhs), AddAssign::<T::Element>::add_assign);
    }
}

impl<'a, T: PolynomialCoefficient> AddAssign<&'a T> for Polynomial<T> {
    fn add_assign(&mut self, rhs: &T) {
        add_sub_assign_single(
            self,
            Cow::Borrowed(rhs),
            AddAssign::<T::Element>::add_assign,
        );
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
    fn add(mut self, rhs: &Polynomial<T>) -> Self::Output {
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

impl<T: PolynomialCoefficient> Add<T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(mut self, rhs: T) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Add<&'a T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(mut self, rhs: &T) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Add<T> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(self, rhs: T) -> Self::Output {
        let mut retval = self.clone();
        retval += rhs;
        retval
    }
}

impl<'a, T: PolynomialCoefficient> Add<&'a T> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn add(self, rhs: &T) -> Self::Output {
        let mut retval = self.clone();
        retval += rhs;
        retval
    }
}

impl<T: PolynomialCoefficient> CheckedAdd for Polynomial<T> {
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        Some(self + rhs)
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
    fn sub_assign(&mut self, rhs: &Polynomial<T>) {
        add_sub_assign(self, rhs, SubAssign::<T::Element>::sub_assign);
    }
}

impl<T: PolynomialCoefficient> SubAssign<T> for Polynomial<T> {
    fn sub_assign(&mut self, rhs: T) {
        add_sub_assign_single(self, Cow::Owned(rhs), SubAssign::<T::Element>::sub_assign);
    }
}

impl<'a, T: PolynomialCoefficient> SubAssign<&'a T> for Polynomial<T> {
    fn sub_assign(&mut self, rhs: &T) {
        add_sub_assign_single(
            self,
            Cow::Borrowed(rhs),
            SubAssign::<T::Element>::sub_assign,
        );
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
    fn sub(mut self, rhs: &Polynomial<T>) -> Self::Output {
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

impl<T: PolynomialCoefficient> Sub<T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(mut self, rhs: T) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Sub<&'a T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(mut self, rhs: &T) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<'a, T: PolynomialCoefficient> Sub<T> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(self, rhs: T) -> Self::Output {
        let mut lhs = self.clone();
        lhs -= rhs;
        lhs
    }
}

impl<'a, T: PolynomialCoefficient> Sub<&'a T> for &'a Polynomial<T> {
    type Output = Polynomial<T>;
    fn sub(self, rhs: &T) -> Self::Output {
        let mut lhs = self.clone();
        lhs -= rhs;
        lhs
    }
}

impl<T: PolynomialCoefficient> CheckedSub for Polynomial<T> {
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        Some(self - rhs)
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
    use crate::util::tests::test_op_helper;
    use num_rational::Ratio;
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
    fn test_add_ratio() {
        let test = |l: Polynomial<Ratio<i64>>,
                    r: Polynomial<Ratio<i64>>,
                    expected: &Polynomial<Ratio<i64>>| {
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
        let r = |n: i64, d: i64| Ratio::new(n, d);
        test(
            vec![r(1, 3), r(2, 3), r(3, 3), r(4, 3)].into(),
            vec![r(8, 5), r(7, 5), r(6, 5), r(5, 5)].into(),
            &vec![r(29, 15), r(31, 15), r(11, 5), r(7, 3)].into(),
        );
        test(
            vec![r(1, 6), r(2, 6), r(3, 6), r(4, 6), r(10, 6)].into(),
            vec![r(8, 8), r(7, 8), r(6, 8), r(5, 8), r(10, 8)].into(),
            &vec![r(7, 6), r(29, 24), r(5, 4), r(31, 24), r(35, 12)].into(),
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

    #[test]
    fn test_sub_ratio() {
        let test = |l: Polynomial<Ratio<i64>>,
                    r: Polynomial<Ratio<i64>>,
                    expected: &Polynomial<Ratio<i64>>| {
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
        let r = |n: i64, d: i64| Ratio::new(n, d);
        test(
            vec![r(1, 3), r(2, 3), r(3, 3), r(4, 3)].into(),
            vec![r(8, 5), r(7, 5), r(6, 5), r(5, 5)].into(),
            &vec![r(-19, 15), r(-11, 15), r(-1, 5), r(1, 3)].into(),
        );
        test(
            vec![r(1, 6), r(2, 6), r(3, 6), r(4, 6), r(10, 6)].into(),
            vec![r(8, 8), r(7, 8), r(6, 8), r(5, 8), r(10, 8)].into(),
            &vec![r(-5, 6), r(-13, 24), r(-1, 4), r(1, 24), r(5, 12)].into(),
        );
    }
}
