// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::traits::{DivRemNearest, PolynomialDivSupported};
use num_traits::Zero;
use std::borrow::Borrow;
use std::mem;
use std::ops::{Div, DivAssign, Rem, RemAssign};

// FIXME: uncomment
// fn checked_div_rem<T: PolynomialDivSupported>(
//     dividend: &Polynomial<T>,
//     divisor: &Polynomial<T>,
// ) -> Option<(Polynomial<T>, Polynomial<T>)> {
//     let divisor = divisor.coefficients();
//     // if divisor is empty then divisor is zero, so return None
//     let divisor_last = divisor.last()?;
//     debug_assert!(!divisor_last.is_zero());
//     let divisor_last_index = divisor.len() - 1;
//     let mut remainder = dividend.coefficients().clone();
//     if remainder.len() < divisor.len() {
//         return Some((Zero::zero(), remainder.into()));
//     }
//     let quotient_len = remainder.len() - divisor.len() + 1;
//     let mut quotient: Vec<T> = (0..quotient_len).map(|_| Zero::zero()).collect();
//     for quotient_index in (0..quotient_len).rev() {
//         let quotient_value = remainder[quotient_index+divisor_last_index].div_rem_nearest(divisor_last).0;
//         if quotient_value.is_zero() {
//             continue;
//         }
//         for divisor_index in 0..divisor.len() {
//             remainder[quotient_index+divisor_index] -= quotient_value.clone() * &divisor[divisor_index];
//         }
//         quotient[quotient_index] = quotient_value;
//     }
//     Some((quotient.into(), remainder.into()))
// }
//
// impl<T: PolynomialDivSupported> DivRemNearest for Polynomial<T> {
//     type DivOutput = Polynomial<T>;
//     type RemOutput = Polynomial<T>;
//     fn checked_div_rem_nearest(&self, rhs: &Polynomial<T>) -> Option<(Polynomial<T>, Polynomial<T>)> {
//         checked_div_rem(self, rhs)
//     }
// }
//
// macro_rules! impl_div_rem {
//     ($l:ty, $r:ty) => {
//         impl<T: PolynomialDivSupported> Div<$r> for $l {
//             type Output = Polynomial<T>;
//             fn div(self, rhs: $r) -> Polynomial<T> {
//                 self.div_rem_nearest(rhs.borrow()).0
//             }
//         }
//
//         impl<T: PolynomialDivSupported> Rem<$r> for $l {
//             type Output = Polynomial<T>;
//             fn rem(self, rhs: $r) -> Polynomial<T> {
//                 self.div_rem_nearest(rhs.borrow()).1
//             }
//         }
//     };
// }
//
// impl_div_rem!(Polynomial<T>, Polynomial<T>);
// impl_div_rem!(Polynomial<T>, &'_ Polynomial<T>);
// impl_div_rem!(&'_ Polynomial<T>, Polynomial<T>);
//
// impl<'a, 'b, T: PolynomialDivSupported> Div<&'a Polynomial<T>> for &'b Polynomial<T> {
//     type Output = Polynomial<T>;
//     fn div(self, rhs: &Polynomial<T>) -> Polynomial<T> {
//         self.div_rem_nearest(rhs).0
//     }
// }
//
// impl<'a, 'b, T: PolynomialDivSupported> Rem<&'a Polynomial<T>> for &'b Polynomial<T> {
//     type Output = Polynomial<T>;
//     fn rem(self, rhs: &Polynomial<T>) -> Polynomial<T> {
//         self.div_rem_nearest(rhs).1
//     }
// }
//
// macro_rules! impl_div_rem_eq {
//     ($r:ty) => {
//         impl<T: PolynomialDivSupported> DivAssign<$r> for Polynomial<T> {
//             fn div_assign(&mut self, rhs: $r) {
//                 let lhs = mem::replace(self, Zero::zero());
//                 *self = lhs / rhs;
//             }
//         }
//
//         impl<T: PolynomialDivSupported> RemAssign<$r> for Polynomial<T> {
//             fn rem_assign(&mut self, rhs: $r) {
//                 let lhs = mem::replace(self, Zero::zero());
//                 *self = lhs % rhs;
//             }
//         }
//     };
// }
//
// impl_div_rem_eq!(Polynomial<T>);
// impl_div_rem_eq!(&'_ Polynomial<T>);
//
// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::polynomial::ops::util::tests::test_op_helper;
//     use num_rational::Ratio;
//     #[test]
//     #[should_panic(expected = "division by zero")]
//     fn test_div_by_zero() {
//         let _ = Polynomial::<Ratio<_>>::from(vec![1]) / Polynomial::zero();
//     }
//     fn test_div_rem<
//         TestFn: FnMut(Polynomial<Ratio<i128>>, Polynomial<Ratio<i128>>, &Polynomial<Ratio<i128>>),
//     >(
//         is_rem: bool,
//         mut test_fn: TestFn,
//     ) {
//         let dividend = vec![74, 2, 50, 45, 5, 6, 30, 36, 21, 93, 72].into();
//         let divisor = vec![51, 1, 45, 31, 53, 65].into();
//         let quotient = vec![
//             Ratio::new(-48_773_611_686, 75_418_890_625),
//             Ratio::new(392_989_032, 1_160_290_625),
//             Ratio::new(954_141, 17_850_625),
//             Ratio::new(-174_492, 274_625),
//             Ratio::new(2229, 4225),
//             Ratio::new(72, 65),
//         ]
//         .into();
//         let remainder = vec![
//             Ratio::new(8_068_452_102_236, 75_418_890_625),
//             Ratio::new(-1_103_147_248_144, 75_418_890_625),
//             Ratio::new(1_146_923_847_613, 15_083_778_125),
//             Ratio::new(6_196_221_016_566, 75_418_890_625),
//             Ratio::new(7_495_581_503, 75_418_890_625),
//         ]
//         .into();
//         if is_rem {
//             test_fn(dividend, divisor, &remainder)
//         } else {
//             test_fn(dividend, divisor, &quotient)
//         }
//     }
//     #[test]
//     fn test_div() {
//         let test = |l: Polynomial<Ratio<i128>>,
//                     r: Polynomial<Ratio<i128>>,
//                     expected: &Polynomial<Ratio<i128>>| {
//             test_op_helper(
//                 l,
//                 r,
//                 expected,
//                 |l, r| *l /= r,
//                 |l, r| *l /= r,
//                 |l, r| l / r,
//                 |l, r| l / r,
//                 |l, r| l / r,
//                 |l, r| l / r,
//             );
//         };
//         test(
//             vec![1].into(),
//             vec![3].into(),
//             &vec![Ratio::new(1, 3)].into(),
//         );
//         test(
//             vec![1, 0].into(),
//             vec![3].into(),
//             &vec![Ratio::new(1, 3), (0).into()].into(),
//         );
//         test(vec![1, 2, 3].into(), vec![4, 5, 6, 7].into(), &Zero::zero());
//         test_div_rem(false, test);
//     }
//     #[test]
//     fn test_rem() {
//         let test = |l: Polynomial<Ratio<i128>>,
//                     r: Polynomial<Ratio<i128>>,
//                     expected: &Polynomial<Ratio<i128>>| {
//             test_op_helper(
//                 l,
//                 r,
//                 expected,
//                 |l, r| *l %= r,
//                 |l, r| *l %= r,
//                 |l, r| l % r,
//                 |l, r| l % r,
//                 |l, r| l % r,
//                 |l, r| l % r,
//             );
//         };
//         test(vec![1].into(), vec![3].into(), &Zero::zero());
//         test(vec![1, 0].into(), vec![3].into(), &Zero::zero());
//         test(
//             vec![1, 2, 3].into(),
//             vec![4, 5, 6, 7].into(),
//             &vec![1, 2, 3].into(),
//         );
//         test_div_rem(true, test);
//     }
// }
//
