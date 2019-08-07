// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use crate::polynomial::PolynomialCoefficientElement;
use crate::polynomial::PolynomialDivSupported;
use crate::polynomial::PseudoDivRem;
use num_traits::CheckedDiv;
use num_traits::CheckedRem;
use num_traits::One;
use num_traits::Zero;
use std::borrow::Borrow;
use std::borrow::Cow;
use std::convert::identity;
use std::mem;
use std::ops::{Div, DivAssign, Rem, RemAssign, SubAssign};

fn quotient_len(numerator_len: usize, denominator_len: usize) -> Option<usize> {
    debug_assert_ne!(denominator_len, 0);
    if numerator_len < denominator_len {
        None
    } else {
        Some(1 + numerator_len - denominator_len)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct ElementPseudoDivRem<T: PolynomialCoefficientElement> {
    quotient: Vec<T>,
    remainder: Vec<T>,
    factor: T,
}

fn element_pseudo_div_rem<T: PolynomialCoefficient>(
    numerator: Vec<T::Element>,
    denominator: &[T::Element],
    quotient_len: usize,
) -> ElementPseudoDivRem<T::Element> {
    let mut remainder = numerator;
    let divisor_last = denominator.last().expect("divisor length already checked");
    let mut reverse_quotient = Vec::with_capacity(quotient_len);
    for quotient_index in (0..quotient_len).rev() {
        let remainder_last = remainder.pop().expect("remainder length already checked");
        let quotient_coefficient = remainder_last;
        for element in &mut remainder {
            *element *= divisor_last;
        }
        for denominator_index in 0..(denominator.len() - 1) {
            <T::Element as SubAssign>::sub_assign(
                &mut remainder[quotient_index + denominator_index],
                quotient_coefficient.clone() * &denominator[denominator_index],
            );
        }
        reverse_quotient.push(quotient_coefficient);
    }
    reverse_quotient.reverse();
    let mut quotient = reverse_quotient;
    let mut factor = divisor_last.clone();
    for quotient_element in &mut quotient[1..] {
        *quotient_element *= &factor;
        factor *= divisor_last;
    }
    ElementPseudoDivRem {
        quotient,
        remainder,
        factor,
    }
}

impl<T: PolynomialCoefficient> Polynomial<T> {
    pub fn checked_pseudo_div_rem(self, rhs: &Self) -> Option<PseudoDivRem<T>> {
        if rhs.is_zero() {
            return None;
        }
        let quotient_len = match quotient_len(self.len(), rhs.len()) {
            None => {
                return Some(PseudoDivRem {
                    quotient: Zero::zero(),
                    remainder: self,
                    factor: One::one(),
                })
            }
            Some(quotient_len) => quotient_len,
        };
        let ElementPseudoDivRem {
            quotient: quotient_numerator,
            remainder: remainder_numerator,
            factor: factor_numerator,
        } = element_pseudo_div_rem::<T>(self.elements, &rhs.elements, quotient_len);
        let rhs_divisor_pow_quotient_len_minus_one =
            T::divisor_pow_usize(rhs.divisor.clone(), quotient_len - 1);
        let rhs_divisor_pow_quotient_len =
            rhs_divisor_pow_quotient_len_minus_one.clone() * &rhs.divisor;
        let factor = T::make_coefficient(
            Cow::Owned(factor_numerator),
            Cow::Borrowed(&rhs_divisor_pow_quotient_len),
        );
        let quotient =
            Polynomial::<T>::from((quotient_numerator, rhs_divisor_pow_quotient_len_minus_one));
        let remainder = Polynomial::<T>::from((remainder_numerator, rhs_divisor_pow_quotient_len));
        Some(PseudoDivRem {
            quotient,
            remainder,
            factor,
        })
    }
    pub fn pseudo_div_rem(self, rhs: &Self) -> PseudoDivRem<T> {
        self.checked_pseudo_div_rem(rhs)
            .expect("polynomial division by zero")
    }
}

impl<T: PolynomialDivSupported> Polynomial<T> {
    fn div_by_coefficient(self, divisor: &T) -> Self {
        self.into_iter()
            .map(|coefficient| coefficient / divisor)
            .collect::<Vec<_>>()
            .into()
    }
    pub fn checked_div_rem(self, rhs: &Self) -> Option<(Self, Self)> {
        let PseudoDivRem {
            quotient,
            remainder,
            factor,
        } = self.checked_pseudo_div_rem(rhs)?;
        Some((
            quotient.div_by_coefficient(&factor),
            remainder.div_by_coefficient(&factor),
        ))
    }
    pub fn div_rem(self, rhs: &Self) -> (Self, Self) {
        let PseudoDivRem {
            quotient,
            remainder,
            factor,
        } = self.pseudo_div_rem(rhs);
        (
            quotient.div_by_coefficient(&factor),
            remainder.div_by_coefficient(&factor),
        )
    }
}

impl<T: PolynomialDivSupported> CheckedDiv for Polynomial<T> {
    fn checked_div(&self, rhs: &Self) -> Option<Self> {
        let PseudoDivRem {
            quotient, factor, ..
        } = self.clone().checked_pseudo_div_rem(rhs)?;
        Some(quotient.div_by_coefficient(&factor))
    }
}

impl<T: PolynomialDivSupported> CheckedRem for Polynomial<T> {
    fn checked_rem(&self, rhs: &Self) -> Option<Self> {
        let PseudoDivRem {
            remainder, factor, ..
        } = self.clone().checked_pseudo_div_rem(rhs)?;
        Some(remainder.div_by_coefficient(&factor))
    }
}

macro_rules! impl_div_rem {
    ($l:ty, $l_to_owned:expr, $r:ty) => {
        impl<T: PolynomialDivSupported> Div<$r> for $l {
            type Output = Polynomial<T>;
            fn div(self, rhs: $r) -> Polynomial<T> {
                let PseudoDivRem {
                    quotient, factor, ..
                } = $l_to_owned(self).pseudo_div_rem(rhs.borrow());
                quotient.div_by_coefficient(&factor)
            }
        }

        impl<T: PolynomialDivSupported> Rem<$r> for $l {
            type Output = Polynomial<T>;
            fn rem(self, rhs: $r) -> Polynomial<T> {
                let PseudoDivRem {
                    remainder, factor, ..
                } = $l_to_owned(self).pseudo_div_rem(rhs.borrow());
                remainder.div_by_coefficient(&factor)
            }
        }
    };
}

impl_div_rem!(Polynomial<T>, identity, Polynomial<T>);
impl_div_rem!(Polynomial<T>, identity, &'_ Polynomial<T>);
impl_div_rem!(&'_ Polynomial<T>, Clone::clone, Polynomial<T>);

impl<'a, 'b, T: PolynomialDivSupported> Div<&'a Polynomial<T>> for &'b Polynomial<T> {
    type Output = Polynomial<T>;
    fn div(self, rhs: &Polynomial<T>) -> Polynomial<T> {
        let PseudoDivRem {
            quotient, factor, ..
        } = self.clone().pseudo_div_rem(rhs);
        quotient.div_by_coefficient(&factor)
    }
}

impl<'a, 'b, T: PolynomialDivSupported> Rem<&'a Polynomial<T>> for &'b Polynomial<T> {
    type Output = Polynomial<T>;
    fn rem(self, rhs: &Polynomial<T>) -> Polynomial<T> {
        let PseudoDivRem {
            remainder, factor, ..
        } = self.clone().pseudo_div_rem(rhs);
        remainder.div_by_coefficient(&factor)
    }
}

macro_rules! impl_div_rem_eq {
    ($r:ty) => {
        impl<T: PolynomialDivSupported> DivAssign<$r> for Polynomial<T> {
            fn div_assign(&mut self, rhs: $r) {
                let lhs = mem::replace(self, Zero::zero());
                *self = lhs / rhs;
            }
        }

        impl<T: PolynomialDivSupported> RemAssign<$r> for Polynomial<T> {
            fn rem_assign(&mut self, rhs: $r) {
                let lhs = mem::replace(self, Zero::zero());
                *self = lhs % rhs;
            }
        }
    };
}

impl_div_rem_eq!(Polynomial<T>);
impl_div_rem_eq!(&'_ Polynomial<T>);

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::test_op_helper;
    use num_integer::Integer;
    use num_rational::Ratio;

    fn r<T: Clone + Integer>(n: T, d: T) -> Ratio<T> {
        Ratio::new(n, d)
    }

    fn ri<T: Clone + Integer>(n: T) -> Ratio<T> {
        Ratio::from(n)
    }

    #[test]
    #[should_panic(expected = "polynomial division by zero")]
    fn test_div_by_zero() {
        let _ = Polynomial::from(ri(1)) / Polynomial::zero();
    }

    fn test_div_rem<
        TestFn: FnMut(Polynomial<Ratio<i128>>, Polynomial<Ratio<i128>>, &Polynomial<Ratio<i128>>),
    >(
        is_rem: bool,
        mut test_fn: TestFn,
    ) {
        let dividend = vec![
            ri(74),
            ri(2),
            ri(50),
            ri(45),
            ri(5),
            ri(6),
            ri(30),
            ri(36),
            ri(21),
            ri(93),
            ri(72),
        ]
        .into();
        let divisor = vec![ri(51), ri(1), ri(45), ri(31), ri(53), ri(65)].into();
        let quotient = vec![
            r(-48_773_611_686, 75_418_890_625),
            r(392_989_032, 1_160_290_625),
            r(954_141, 17_850_625),
            r(-174_492, 274_625),
            r(2229, 4225),
            r(72, 65),
        ]
        .into();
        let remainder = vec![
            r(8_068_452_102_236, 75_418_890_625),
            r(-1_103_147_248_144, 75_418_890_625),
            r(1_146_923_847_613, 15_083_778_125),
            r(6_196_221_016_566, 75_418_890_625),
            r(7_495_581_503, 75_418_890_625),
        ]
        .into();
        if is_rem {
            test_fn(dividend, divisor, &remainder)
        } else {
            test_fn(dividend, divisor, &quotient)
        }
    }

    #[test]
    fn test_div() {
        let test = |l: Polynomial<Ratio<i128>>,
                    r: Polynomial<Ratio<i128>>,
                    expected: &Polynomial<Ratio<i128>>| {
            test_op_helper(
                l,
                r,
                expected,
                |l, r| *l /= r,
                |l, r| *l /= r,
                |l, r| l / r,
                |l, r| l / r,
                |l, r| l / r,
                |l, r| l / r,
            );
        };
        test(ri(1).into(), ri(3).into(), &vec![r(1, 3)].into());
        test(
            vec![ri(1), ri(0)].into(),
            ri(3).into(),
            &vec![r(1, 3), ri(0)].into(),
        );
        test(
            vec![ri(1), ri(2), ri(3)].into(),
            vec![ri(4), ri(5), ri(6), ri(7)].into(),
            &Zero::zero(),
        );
        test_div_rem(false, test);
    }

    #[test]
    fn test_rem() {
        let test = |l: Polynomial<Ratio<i128>>,
                    r: Polynomial<Ratio<i128>>,
                    expected: &Polynomial<Ratio<i128>>| {
            test_op_helper(
                l,
                r,
                expected,
                |l, r| *l %= r,
                |l, r| *l %= r,
                |l, r| l % r,
                |l, r| l % r,
                |l, r| l % r,
                |l, r| l % r,
            );
        };
        test(ri(1).into(), ri(3).into(), &Zero::zero());
        test(vec![ri(1), ri(0)].into(), ri(3).into(), &Zero::zero());
        test(
            vec![ri(1), ri(2), ri(3)].into(),
            vec![ri(4), ri(5), ri(6), ri(7)].into(),
            &vec![ri(1), ri(2), ri(3)].into(),
        );
        test_div_rem(true, test);
    }
}
