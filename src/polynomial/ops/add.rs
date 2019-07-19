// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use super::util::{pairwise_op_eq_move, pairwise_op_eq_ref, pairwise_op_ref_ref};
use crate::polynomial::Polynomial;
use num_traits::Zero;
use std::ops::{Add, AddAssign};

impl<T> AddAssign for Polynomial<T>
where
    T: AddAssign<T> + Zero,
{
    fn add_assign(&mut self, rhs: Polynomial<T>) {
        pairwise_op_eq_move(self, rhs, AddAssign::add_assign, |_| {}, |r| r)
    }
}

impl<'a, T> AddAssign<&'a Polynomial<T>> for Polynomial<T>
where
    T: AddAssign<&'a T> + Zero + Clone,
{
    fn add_assign(&mut self, rhs: &'a Polynomial<T>) {
        pairwise_op_eq_ref(self, rhs, AddAssign::add_assign, |_| {}, Clone::clone)
    }
}

impl<T> Add for Polynomial<T>
where
    T: AddAssign<T> + Zero,
{
    type Output = Polynomial<T>;
    fn add(mut self, rhs: Polynomial<T>) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'a, T> Add<&'a Polynomial<T>> for Polynomial<T>
where
    T: AddAssign<&'a T> + Clone + Zero,
{
    type Output = Polynomial<T>;
    fn add(mut self, rhs: &'a Polynomial<T>) -> Self::Output {
        self += rhs;
        self
    }
}

impl<'a, T> Add<Polynomial<T>> for &'a Polynomial<T>
where
    T: AddAssign<&'a T> + Clone + Zero,
{
    type Output = Polynomial<T>;
    fn add(self, mut rhs: Polynomial<T>) -> Self::Output {
        rhs += self;
        rhs
    }
}

impl<'a, T> Add for &'a Polynomial<T>
where
    &'a T: Add<&'a T, Output = T>,
    T: Clone + Zero,
{
    type Output = Polynomial<T>;
    fn add(self, rhs: Self) -> Self::Output {
        pairwise_op_ref_ref(self, rhs, Add::add, Clone::clone, Clone::clone)
    }
}

impl<T: Zero + AddAssign> Zero for Polynomial<T> {
    fn zero() -> Self {
        Default::default()
    }
    fn set_zero(&mut self) {
        self.coefficients.clear()
    }
    fn is_zero(&self) -> bool {
        // test in reverse order since high coefficient is usually non-zero
        for coefficient in self.iter().rev() {
            if !coefficient.is_zero() {
                return false;
            }
        }
        true
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
}
