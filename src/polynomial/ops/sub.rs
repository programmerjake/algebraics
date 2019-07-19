// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use super::util::{pairwise_op_eq_move, pairwise_op_eq_ref, pairwise_op_ref_ref};
use crate::polynomial::Polynomial;
use num_traits::Zero;
use std::mem;
use std::ops::{Neg, Sub, SubAssign};

impl<T> SubAssign for Polynomial<T>
where
    T: SubAssign<T> + Zero + Neg<Output = T>,
{
    fn sub_assign(&mut self, rhs: Polynomial<T>) {
        pairwise_op_eq_move(self, rhs, SubAssign::sub_assign, |_| {}, Neg::neg)
    }
}

impl<'a, T> SubAssign<&'a Polynomial<T>> for Polynomial<T>
where
    T: SubAssign<&'a T> + Zero,
    &'a T: Neg<Output = T>,
{
    fn sub_assign(&mut self, rhs: &'a Polynomial<T>) {
        pairwise_op_eq_ref(self, rhs, SubAssign::sub_assign, |_| {}, Neg::neg)
    }
}

impl<T> Sub for Polynomial<T>
where
    T: SubAssign<T> + Zero + Neg<Output = T>,
{
    type Output = Polynomial<T>;
    fn sub(mut self, rhs: Polynomial<T>) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<'a, T> Sub<&'a Polynomial<T>> for Polynomial<T>
where
    T: SubAssign<&'a T> + Clone + Zero,
    &'a T: Neg<Output = T>,
{
    type Output = Polynomial<T>;
    fn sub(mut self, rhs: &'a Polynomial<T>) -> Self::Output {
        self -= rhs;
        self
    }
}

impl<'a, T> Sub<Polynomial<T>> for &'a Polynomial<T>
where
    T: Clone + Zero + Neg<Output = T>,
    &'a T: Sub<T, Output = T>,
{
    type Output = Polynomial<T>;
    fn sub(self, mut rhs: Polynomial<T>) -> Self::Output {
        let mut temp = None;
        let mut temp2 = None;
        pairwise_op_eq_ref(
            &mut rhs,
            self,
            |r, l| {
                let r_value = mem::replace(r, temp.take().unwrap_or_else(Zero::zero));
                temp = Some(mem::replace(r, l - r_value));
            },
            |r| {
                let r_value = mem::replace(r, temp2.take().unwrap_or_else(Zero::zero));
                temp2 = Some(mem::replace(r, -r_value));
            },
            Clone::clone,
        );
        rhs
    }
}

impl<'a, T> Sub for &'a Polynomial<T>
where
    &'a T: Sub<&'a T, Output = T> + Neg<Output = T>,
    T: Clone + Zero,
{
    type Output = Polynomial<T>;
    fn sub(self, rhs: Self) -> Self::Output {
        pairwise_op_ref_ref(self, rhs, Sub::sub, Clone::clone, Neg::neg)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polynomial::ops::util::tests::test_op_helper;
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
