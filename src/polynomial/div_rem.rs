// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::{
    polynomial::{
        Polynomial, PolynomialCoefficient, PolynomialCoefficientElement, PolynomialDivSupported,
        PseudoDivRem,
    },
    traits::{ExactDiv, ExactDivAssign},
};
use num_integer::Integer;
use num_traits::{CheckedDiv, CheckedRem, Zero};
use std::{
    borrow::{Borrow, Cow},
    convert::identity,
    mem,
    ops::{Div, DivAssign, Mul, Rem, RemAssign, SubAssign},
};

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
                    factor: T::make_one_coefficient_from_element(Cow::Borrowed(&rhs.elements[0])),
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
        let quotient = Polynomial::<T>::from((
            quotient_numerator,
            rhs_divisor_pow_quotient_len_minus_one * &self.divisor,
        ));
        let remainder = Polynomial::<T>::from((
            remainder_numerator,
            Mul::<T::Divisor>::mul(rhs_divisor_pow_quotient_len, self.divisor),
        ));
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
    pub fn exact_pseudo_div(self, rhs: &Self) -> (Polynomial<T>, T) {
        let PseudoDivRem {
            quotient,
            remainder,
            factor,
        } = self.pseudo_div_rem(rhs);
        assert!(remainder.is_zero(), "inexact division");
        (quotient, factor)
    }
    pub fn checked_exact_pseudo_div(self, rhs: &Self) -> Option<(Polynomial<T>, T)> {
        let PseudoDivRem {
            quotient,
            remainder,
            factor,
        } = self.checked_pseudo_div_rem(rhs)?;
        if remainder.is_zero() {
            Some((quotient, factor))
        } else {
            None
        }
    }
}

impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> Polynomial<T> {
    pub fn checked_div_rem(self, rhs: &Self) -> Option<(Self, Self)> {
        let PseudoDivRem {
            quotient,
            remainder,
            factor,
        } = self.checked_pseudo_div_rem(rhs)?;
        Some((
            quotient.checked_exact_div(&factor)?,
            remainder.checked_exact_div(factor)?,
        ))
    }
    pub fn div_rem(self, rhs: &Self) -> (Self, Self) {
        let PseudoDivRem {
            quotient,
            remainder,
            factor,
        } = self.pseudo_div_rem(rhs);
        (quotient.exact_div(&factor), remainder.exact_div(factor))
    }
}

impl<T: PolynomialDivSupported> CheckedDiv for Polynomial<T> {
    fn checked_div(&self, rhs: &Self) -> Option<Self> {
        let PseudoDivRem {
            quotient, factor, ..
        } = self.clone().checked_pseudo_div_rem(rhs)?;
        Some(quotient.checked_exact_div(factor)?)
    }
}

impl<T: PolynomialDivSupported> CheckedRem for Polynomial<T> {
    fn checked_rem(&self, rhs: &Self) -> Option<Self> {
        let PseudoDivRem {
            remainder, factor, ..
        } = self.clone().checked_pseudo_div_rem(rhs)?;
        Some(remainder.checked_exact_div(factor)?)
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
                quotient.exact_div(factor)
            }
        }

        impl<T: PolynomialDivSupported> Rem<$r> for $l {
            type Output = Polynomial<T>;
            fn rem(self, rhs: $r) -> Polynomial<T> {
                let PseudoDivRem {
                    remainder, factor, ..
                } = $l_to_owned(self).pseudo_div_rem(rhs.borrow());
                remainder.exact_div(factor)
            }
        }

        impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> ExactDiv<$r> for $l {
            type Output = Polynomial<T>;
            fn exact_div(self, rhs: $r) -> Polynomial<T> {
                let (quotient, factor) = $l_to_owned(self).exact_pseudo_div(rhs.borrow());
                quotient.exact_div(factor)
            }
            fn checked_exact_div(self, rhs: $r) -> Option<Polynomial<T>> {
                let (quotient, factor) =
                    $l_to_owned(self).checked_exact_pseudo_div(rhs.borrow())?;
                quotient.checked_exact_div(factor)
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
        quotient.exact_div(factor)
    }
}

impl<'a, 'b, T: PolynomialDivSupported> Rem<&'a Polynomial<T>> for &'b Polynomial<T> {
    type Output = Polynomial<T>;
    fn rem(self, rhs: &Polynomial<T>) -> Polynomial<T> {
        let PseudoDivRem {
            remainder, factor, ..
        } = self.clone().pseudo_div_rem(rhs);
        remainder.exact_div(factor)
    }
}

impl<'l, 'r, T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>
    ExactDiv<&'r Polynomial<T>> for &'l Polynomial<T>
{
    type Output = Polynomial<T>;
    fn exact_div(self, rhs: &Polynomial<T>) -> Polynomial<T> {
        let (quotient, factor) = self.clone().exact_pseudo_div(rhs.borrow());
        quotient.exact_div(factor)
    }
    fn checked_exact_div(self, rhs: &Polynomial<T>) -> Option<Polynomial<T>> {
        let (quotient, factor) = self.clone().checked_exact_pseudo_div(rhs.borrow())?;
        quotient.checked_exact_div(factor)
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

        impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> ExactDivAssign<$r>
            for Polynomial<T>
        {
            fn exact_div_assign(&mut self, rhs: $r) {
                let lhs = mem::replace(self, Zero::zero());
                *self = lhs.exact_div(rhs);
            }
            fn checked_exact_div_assign(&mut self, rhs: $r) -> Result<(), ()> {
                (&*self)
                    .checked_exact_div(rhs)
                    .map(|v| {
                        *self = v;
                    })
                    .ok_or(())
            }
        }
    };
}

impl_div_rem_eq!(Polynomial<T>);
impl_div_rem_eq!(&'_ Polynomial<T>);

fn div_single<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>(
    lhs: Cow<Polynomial<T>>,
    rhs: &T,
) -> Polynomial<T> {
    fn do_div<
        T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>,
        I: Iterator<Item = T>,
    >(
        coefficients: I,
        rhs: &T,
    ) -> Polynomial<T> {
        coefficients
            .map(|coefficient| coefficient.exact_div(rhs))
            .collect::<Vec<_>>()
            .into()
    }
    match lhs {
        Cow::Borrowed(lhs) => do_div(lhs.iter(), rhs),
        Cow::Owned(lhs) => do_div(lhs.into_iter(), rhs),
    }
}

fn div_assign_single<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>(
    lhs: &mut Polynomial<T>,
    rhs: &T,
) {
    *lhs = div_single(Cow::Owned(mem::replace(lhs, Zero::zero())), rhs);
}

fn checked_div_single<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>(
    lhs: Cow<Polynomial<T>>,
    rhs: &T,
) -> Option<Polynomial<T>> {
    fn do_div<
        T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>,
        I: Iterator<Item = T>,
    >(
        coefficients: I,
        rhs: &T,
    ) -> Option<Polynomial<T>> {
        coefficients
            .map(|coefficient| coefficient.checked_exact_div(rhs))
            .collect::<Option<Vec<_>>>()
            .map(Into::into)
    }
    match lhs {
        Cow::Borrowed(lhs) => do_div(lhs.iter(), rhs),
        Cow::Owned(lhs) => do_div(lhs.into_iter(), rhs),
    }
}

fn checked_div_assign_single<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>(
    lhs: &mut Polynomial<T>,
    rhs: &T,
) -> Result<(), ()> {
    *lhs = checked_div_single(Cow::Owned(mem::replace(lhs, Zero::zero())), rhs).ok_or(())?;
    Ok(())
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> Div<&'a T>
    for &'a Polynomial<T>
{
    type Output = Polynomial<T>;
    fn div(self, rhs: &T) -> Polynomial<T> {
        div_single(Cow::Borrowed(self), rhs)
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> Div<T>
    for &'a Polynomial<T>
{
    type Output = Polynomial<T>;
    fn div(self, rhs: T) -> Polynomial<T> {
        div_single(Cow::Borrowed(self), &rhs)
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> Div<&'a T>
    for Polynomial<T>
{
    type Output = Polynomial<T>;
    fn div(self, rhs: &T) -> Polynomial<T> {
        div_single(Cow::Owned(self), rhs)
    }
}

impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> Div<T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn div(self, rhs: T) -> Polynomial<T> {
        div_single(Cow::Owned(self), &rhs)
    }
}

impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> DivAssign<T>
    for Polynomial<T>
{
    fn div_assign(&mut self, rhs: T) {
        div_assign_single(self, &rhs);
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> DivAssign<&'a T>
    for Polynomial<T>
{
    fn div_assign(&mut self, rhs: &T) {
        div_assign_single(self, rhs);
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> ExactDiv<&'a T>
    for &'a Polynomial<T>
{
    type Output = Polynomial<T>;
    fn exact_div(self, rhs: &T) -> Polynomial<T> {
        div_single(Cow::Borrowed(self), rhs)
    }
    fn checked_exact_div(self, rhs: &T) -> Option<Polynomial<T>> {
        checked_div_single(Cow::Borrowed(self), rhs)
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> ExactDiv<T>
    for &'a Polynomial<T>
{
    type Output = Polynomial<T>;
    fn exact_div(self, rhs: T) -> Polynomial<T> {
        div_single(Cow::Borrowed(self), &rhs)
    }
    fn checked_exact_div(self, rhs: T) -> Option<Polynomial<T>> {
        checked_div_single(Cow::Borrowed(self), &rhs)
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> ExactDiv<&'a T>
    for Polynomial<T>
{
    type Output = Polynomial<T>;
    fn exact_div(self, rhs: &T) -> Polynomial<T> {
        div_single(Cow::Owned(self), rhs)
    }
    fn checked_exact_div(self, rhs: &T) -> Option<Polynomial<T>> {
        checked_div_single(Cow::Owned(self), rhs)
    }
}

impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> ExactDiv<T> for Polynomial<T> {
    type Output = Polynomial<T>;
    fn exact_div(self, rhs: T) -> Polynomial<T> {
        div_single(Cow::Owned(self), &rhs)
    }
    fn checked_exact_div(self, rhs: T) -> Option<Polynomial<T>> {
        checked_div_single(Cow::Owned(self), &rhs)
    }
}

impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> ExactDivAssign<T>
    for Polynomial<T>
{
    fn exact_div_assign(&mut self, rhs: T) {
        div_assign_single(self, &rhs);
    }
    fn checked_exact_div_assign(&mut self, rhs: T) -> Result<(), ()> {
        checked_div_assign_single(self, &rhs)
    }
}

impl<'a, T: PolynomialCoefficient + for<'b> ExactDiv<&'b T, Output = T>> ExactDivAssign<&'a T>
    for Polynomial<T>
{
    fn exact_div_assign(&mut self, rhs: &T) {
        div_assign_single(self, rhs);
    }
    fn checked_exact_div_assign(&mut self, rhs: &T) -> Result<(), ()> {
        checked_div_assign_single(self, rhs)
    }
}

impl<T: PolynomialDivSupported> Polynomial<T> {
    pub fn checked_powmod<E: Clone + Integer>(
        &self,
        mut exponent: E,
        modulus: &Self,
    ) -> Option<Self> {
        if exponent < Zero::zero() {
            return None;
        }
        if exponent.is_zero() {
            return self.to_one_if_nonzero();
        }
        let mut base = self.checked_rem(modulus)?;
        if exponent.is_one() {
            return Some(base);
        }
        let mut retval: Option<Self> = None;
        loop {
            if exponent.is_odd() {
                retval = Some(match retval.take() {
                    None => base.clone(),
                    Some(retval) => (retval * &base).checked_rem(modulus)?,
                });
            }
            let two = E::one() + E::one();
            exponent = exponent / two;
            if exponent.is_zero() {
                break;
            }
            base = (&base * &base).checked_rem(modulus)?;
        }
        retval
    }
    pub fn powmod<E: Clone + Integer>(&self, exponent: E, modulus: &Self) -> Self {
        self.checked_powmod(exponent, modulus)
            .expect("checked_powmod failed")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::{tests::test_op_helper, DebugAsDisplay};
    use num_bigint::BigInt;
    use num_integer::Integer;
    use num_rational::Ratio;
    use num_traits::One;

    fn r<T: Clone + Integer>(n: i128, d: i128) -> Ratio<T>
    where
        i128: Into<T>,
    {
        Ratio::new(n.into(), d.into())
    }

    fn rs(v: &str) -> Ratio<BigInt> {
        v.parse().expect("invalid value")
    }

    fn ri<T: Clone + Integer>(n: i128) -> Ratio<T>
    where
        i128: Into<T>,
    {
        Ratio::from(n.into())
    }

    #[test]
    #[should_panic(expected = "polynomial division by zero")]
    fn test_div_by_zero() {
        let _ = Polynomial::<Ratio<i128>>::from(ri(1)) / Polynomial::zero();
    }

    #[test]
    fn test_pseudo_div_rem() {
        let test = |dividend: Polynomial<Ratio<i128>>,
                    divisor: Polynomial<Ratio<i128>>,
                    expected_quotient: Polynomial<Ratio<i128>>,
                    expected_remainder: Polynomial<Ratio<i128>>,
                    expected_factor: Ratio<i128>| {
            println!("dividend=({})", dividend);
            println!("divisor=({})", divisor);
            println!("expected_quotient=({})", expected_quotient);
            println!("expected_remainder=({})", expected_remainder);
            println!("expected_factor=({})", expected_factor);
            let (expected_exact_quotient, expected_exact_factor) = if expected_remainder.is_zero() {
                (Some(expected_quotient.clone()), Some(expected_factor))
            } else {
                (None, None)
            };
            fn format_opt<T: std::fmt::Display>(v: &Option<T>) -> String {
                format!("{:?}", v.as_ref().map(DebugAsDisplay))
            }
            println!(
                "expected_exact_quotient={}",
                format_opt(&expected_exact_quotient)
            );
            println!(
                "expected_exact_factor={}",
                format_opt(&expected_exact_factor)
            );
            let PseudoDivRem {
                quotient,
                remainder,
                factor,
            } = dividend.clone().pseudo_div_rem(&divisor);
            let (exact_quotient, exact_factor) = match dividend.checked_exact_pseudo_div(&divisor) {
                None => (None, None),
                Some((a, b)) => (Some(a), Some(b)),
            };
            println!("quotient=({})", quotient);
            println!("remainder=({})", remainder);
            println!("factor=({})", factor);
            println!("exact_quotient={}", format_opt(&exact_quotient));
            println!("exact_factor={}", format_opt(&exact_factor));
            assert_eq!(factor, expected_factor);
            assert_eq!(quotient, expected_quotient);
            assert_eq!(remainder, expected_remainder);
            assert_eq!(exact_quotient, expected_exact_quotient);
            assert_eq!(exact_factor, expected_exact_factor);
        };
        test(
            vec![r(1, 2), r(5, 2), r(5, 2)].into(),
            vec![r(1, 3), r(5, 3)].into(),
            vec![r(20, 6), r(25, 6)].into(),
            r(5, 18).into(),
            r(25, 9),
        );
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
        let dividend = vec![r(1, 2), r(5, 2), r(5, 2)].into();
        let divisor = vec![r(1, 3), r(5, 3)].into();
        let quotient = vec![r(6, 5), r(3, 2)].into();
        let remainder = r(1, 10).into();
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

    #[test]
    fn test_powmod() {
        fn test(
            base: Polynomial<Ratio<BigInt>>,
            exponent: usize,
            modulus: Polynomial<Ratio<BigInt>>,
            expected: Option<Polynomial<Ratio<BigInt>>>,
        ) {
            fn display_opt(value: &Option<Polynomial<Ratio<BigInt>>>) -> String {
                match value {
                    None => "None".into(),
                    Some(value) => format!("Some({})", value),
                }
            }
            println!("base: {}", base);
            println!("exponent: {}", exponent);
            println!("modulus: {}", modulus);
            println!("expected: {}", display_opt(&expected));
            let result = base.checked_powmod(exponent, &modulus);
            println!("result: {}", display_opt(&result));
            assert!(expected == result);
        }
        test(
            vec![ri(15), ri(6), ri(4), ri(12), ri(9), ri(1)].into(),
            1,
            Zero::zero(),
            None,
        );
        test(
            vec![ri(15), ri(6), ri(4), ri(12), ri(9), ri(1)].into(),
            0,
            vec![ri(3), ri(18), ri(3), ri(8), ri(7), ri(15)].into(),
            Some(One::one()),
        );
        test(
            vec![ri(15), ri(6), ri(4), ri(12), ri(9), ri(1)].into(),
            11,
            vec![ri(3), ri(18), ri(3), ri(8), ri(7), ri(15)].into(),
            Some(
                vec![
                    rs("1_585_666_675_291_483_314_365_180_767_318_922\
                        _920_620_691_036_140_503_147_761_986_750_761_665_151\
                        /318_810_750_107_024_793_451\
                        _703_903_457_428_168_621_845_543_384_552_001_953_125"),
                    rs("156_334_839_226_073_571_425_698_092_108_539\
                        _261_126_854_767_672_993_005_422_136_814_276_793_379\
                        /35_423_416_678_558_310_383\
                        _522_655_939_714_240_957_982_838_153_839_111_328_125"),
                    rs("-172_340_775_978_090_405_112_252_064_451_109\
                        _288_434_967_387_072_256_759_303_520_205_766_571_544\
                        /318_810_750_107_024_793_451\
                        _703_903_457_428_168_621_845_543_384_552_001_953_125"),
                    rs("2_787_107_236_885_882_031_573_490_362_701_892\
                        _707_788_973_888_023_206_985_381_071_985_610_466_173\
                        /956_432_250_321_074_380_355\
                        _111_710_372_284_505_865_536_630_153_656_005_859_375"),
                    rs("5_852_716_315_396_487_808_074_188_396_490_905\
                        _383_295_316_325_141_770_897_943_309_970_559_308_172\
                        /956_432_250_321_074_380_355\
                        _111_710_372_284_505_865_536_630_153_656_005_859_375"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(8), ri(18), ri(11), ri(7), ri(18), ri(15)].into(),
            18,
            vec![ri(8), ri(6), ri(1), ri(17), ri(7), ri(13)].into(),
            Some(
                vec![
                    rs("-176_934_088\
                        _732_185_183_209_017_506_043_037_333_592_182_450_247\
                        _261_748_353_427_344_290_741_992_156_137_225_728_381\
                        _947_145_156_922_156_172_535_909_561_352_479_597_616\
                        /629_692_177_758_524_276\
                        _875_423_024_025_407_579_923_571_677_214_132_180_361\
                        _719_678_758_420_782_116_484_972_480_686_781_743_609"),
                    rs("-170_130_547\
                        _026_901_599_219_683_476_193_503_890_273_980_568_427\
                        _207_219_797_733_202_203_242_056_149_037_316_980_536\
                        _815_474_428_773_224_920_016_436_539_607_268_912_004\
                        /629_692_177_758_524_276\
                        _875_423_024_025_407_579_923_571_677_214_132_180_361\
                        _719_678_758_420_782_116_484_972_480_686_781_743_609"),
                    rs("92_138_356\
                        _521_324_676_956_886_931_737_343_567_518_786_256_271\
                        _926_132_369_782_889_842_378_277_049_192_231_519_054\
                        _223_498_575_759_377_743_432_751_273_334_862_942_442\
                        /629_692_177_758_524_276\
                        _875_423_024_025_407_579_923_571_677_214_132_180_361\
                        _719_678_758_420_782_116_484_972_480_686_781_743_609"),
                    rs("-328_223_497\
                        _750_156_261_045_154_092_611_230_843_909_764_934_169\
                        _323_282_247_228_356_186_498_678_131_026_422_818_526\
                        _111_999_221_650_296_023_134_164_900_371_966_607_760\
                        /629_692_177_758_524_276\
                        _875_423_024_025_407_579_923_571_677_214_132_180_361\
                        _719_678_758_420_782_116_484_972_480_686_781_743_609"),
                    rs("-324_356_266\
                        _394_714_169_790_895_933_949_934_329_636_789_600_813\
                        _119_413_443_994_631_773_616_509_915_774_104_186_814\
                        _724_040_739_634_646_450_911_872_608_994_669_680_269\
                        /629_692_177_758_524_276\
                        _875_423_024_025_407_579_923_571_677_214_132_180_361\
                        _719_678_758_420_782_116_484_972_480_686_781_743_609"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(9), ri(18), ri(3), ri(9), ri(1), ri(3)].into(),
            13,
            vec![ri(17), ri(19), ri(15), ri(4), ri(14), ri(16)].into(),
            Some(
                vec![
                    rs("-25_431_449_682_385_724_510_773_146_682_619_326\
                        _783_652_986_319_988_726_673_555_468_291_267_902_203\
                        /24_519_928_653_854_221\
                        _733_733_552_434_404_946_937_899_825_954_937_634_816"),
                    rs("-6_709_860_689_123_122_741_008_254_030_118_045\
                        _013_490_245_149_715_867_111_869_598_418_203_861_673\
                        /24_519_928_653_854_221\
                        _733_733_552_434_404_946_937_899_825_954_937_634_816"),
                    rs("-16_353_429_435_946_708_587_658_554_579_756_119\
                        _643_511_912_932_621_301_026_012_552_334_378_102_637\
                        /24_519_928_653_854_221\
                        _733_733_552_434_404_946_937_899_825_954_937_634_816"),
                    rs("2_196_204_622_177_526_641_857_617_935_939_207\
                        _831_791_093_298_646_795_611_689_311_194_558_594_603\
                        /6_129_982_163_463_555\
                        _433_433_388_108_601_236_734_474_956_488_734_408_704"),
                    rs("-13_766_147_221_892_664_948_954_842_035_958_965\
                        _163_645_541_330_631_755_559_669_629_412_857_744_093\
                        /12_259_964_326_927_110\
                        _866_866_776_217_202_473_468_949_912_977_468_817_408"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(16), ri(3), ri(12), ri(4), ri(17), ri(5)].into(),
            15,
            vec![ri(5), ri(13), ri(4), ri(15), ri(14), ri(15)].into(),
            Some(
                vec![
                    rs("3_968_223_038_798\
                        _449_894_830_372_703_477_665_499_057_589_974_212_620\
                        _193_863_307_001_145_273_120_261_780_934_930_597_107\
                        /2_084_295_656_895_530_869_364_340_220_211_569\
                        _698_616_216_328_446_171_246_469_020_843_505_859_375"),
                    rs("-740_973_733_763\
                        _261_959_161_886_828_742_042_695_760_278_719_940_079\
                        _166_705_887_577_151_999_143_366_754_401_627_466_084\
                        /10_421_478_284_477_654_346_821_701_101_057_848\
                        _493_081_081_642_230_856_232_345_104_217_529_296_875"),
                    rs("17_827_373_460_032\
                        _228_159_645_265_829_354_599_476_004_974_022_450_878\
                        _148_577_265_309_921_154_932_795_892_935_635_544_768\
                        /10_421_478_284_477_654_346_821_701_101_057_848\
                        _493_081_081_642_230_856_232_345_104_217_529_296_875"),
                    rs("166_754_643_861\
                        _776_199_753_789_120_854_049_262_177_635_820_261_037\
                        _151_236_272_698_519_600_752_774_569_100_984_529_239\
                        /138_953_043_793_035_391_290_956_014_680_771\
                        _313_241_081_088_563_078_083_097_934_722_900_390_625"),
                    rs("22_569_816_666_522\
                        _300_699_970_849_275_022_027_270_383_347_897_978_102\
                        _544_747_794_727_037_074_618_254_706_712_550_470_873\
                        /10_421_478_284_477_654_346_821_701_101_057_848\
                        _493_081_081_642_230_856_232_345_104_217_529_296_875"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(11), ri(12), ri(4), ri(17), ri(5), ri(16)].into(),
            10,
            vec![ri(4), ri(12), ri(7), ri(14), ri(13), ri(18)].into(),
            Some(
                vec![
                    rs("173_349_809_741_634_790_517_629_302\
                        _198_255_738_924_771_020_629_186_295_252_256_712_801\
                        /1_349_507_451_082_182\
                        _988_631_629_529_595_217_504_269_135_410_620_268_544"),
                    rs("136_649_542_414_109_956_312_150_033\
                        _254_209_623_783_071_903_092_005_304_444_675_167_651\
                        /449_835_817_027_394\
                        _329_543_876_509_865_072_501_423_045_136_873_422_848"),
                    rs("-320_573_236_405_438_042_516_576_040\
                        _775_102_420_570_832_290_554_265_484_730_594_953_601\
                        /5_398_029_804_328_731\
                        _954_526_518_118_380_870_017_076_541_642_481_074_176"),
                    rs("227_616_824_975_837_842_336_884_869\
                        _577_831_180_217_241_229_764_404_246_759_090_312_921\
                        /674_753_725_541_091\
                        _494_315_814_764_797_608_752_134_567_705_310_134_272"),
                    rs("1_928_326_403_423_473_856_204_629_547\
                        _911_072_055_518_300_348_036_879_887_352_005_976_477\
                        /5_398_029_804_328_731\
                        _954_526_518_118_380_870_017_076_541_642_481_074_176"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(2), ri(7), ri(18), ri(18), ri(2), ri(19)].into(),
            14,
            vec![ri(10), ri(11), ri(1), ri(0), ri(2)].into(),
            Some(
                vec![
                    rs("17_116_354\
                        _565_656_279_542_765_816_219_704_897_093_314_962_153\
                        /8_589_934_592"),
                    rs("75_378_530\
                        _787_471_742_604_887_950_480_532_576_499_934_645_279\
                        /17_179_869_184"),
                    rs("57_152_339\
                        _047_803_800_599_955_527_334_898_082_225_786_405_389\
                        /17_179_869_184"),
                    rs("7_141_511\
                        _099_204_685_801_116_225_688_161_375_046_284_531_013\
                        /8_589_934_592"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(16), ri(13), ri(11), ri(15), ri(7), ri(12)].into(),
            11,
            vec![ri(9), ri(2), ri(15), ri(17), ri(13), ri(14)].into(),
            Some(
                vec![
                    rs("53_786_086_107_227_954_066_084_569_912\
                        _816_780_927_426_802_734_233_575_954_044_326_317_725\
                        /13_842_032_585_776_425\
                        _728_350_931_699_632_307_649_677_459_403_537_645_568"),
                    rs("-545_162_994_758_509_133_753_875_690\
                        _075_043_207_536_846_677_106_116_608_529_845_598_625\
                        /865_127_036_611_026\
                        _608_021_933_231_227_019_228_104_841_212_721_102_848"),
                    rs("-44_095_009_930_321_773_402_363_556_998\
                        _849_059_172_283_208_141_185_864_176_319_532_930_949\
                        /13_842_032_585_776_425\
                        _728_350_931_699_632_307_649_677_459_403_537_645_568"),
                    rs("-59_241_596_534_156_450_909_340_853_798\
                        _843_689_834_059_346_960_589_871_532_448_282_085_873\
                        /13_842_032_585_776_425\
                        _728_350_931_699_632_307_649_677_459_403_537_645_568"),
                    rs("-73_038_919_819_282_009_293_066_462_605\
                        _880_773_834_796_373_418_091_698_358_848_369_402_861\
                        /13_842_032_585_776_425\
                        _728_350_931_699_632_307_649_677_459_403_537_645_568"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(9), ri(17), ri(10), ri(3), ri(9), ri(12)].into(),
            17,
            vec![ri(6), ri(12), ri(16), ri(5), ri(4), ri(9)].into(),
            Some(
                vec![
                    rs("107_310_052_774_975\
                        _374_976_809_295_936_414_801_346_072_497_888_193_998\
                        _909_668_247_798_715_229_856_393_722_822_920_217_445\
                        /507_528_786_056_415_600_719_754_159_741\
                        _696_356_908_742_250_191_663_887_263_627_442_114_881"),
                    rs("211_556_575_376_652\
                        _462_370_255_539_615_239_423_105_107_017_367_777_525\
                        _345_353_133_113_071_717_517_518_174_764_088_606_933\
                        /507_528_786_056_415_600_719_754_159_741\
                        _696_356_908_742_250_191_663_887_263_627_442_114_881"),
                    rs("636_111_589_535_705\
                        _890_882_422_462_104_016_053_812_793_353_307_599_636\
                        _338_686_989_896_335_769_026_552_709_790_515_741_290\
                        /1_522_586_358_169_246_802_159_262_479_225\
                        _089_070_726_226_750_574_991_661_790_882_326_344_643"),
                    rs("-318_508_059_623_322\
                        _990_014_292_261_929_772_320_270_934_012_499_577_131\
                        _185_807_220_429_064_694_110_685_680_328_950_350_853\
                        /1_522_586_358_169_246_802_159_262_479_225\
                        _089_070_726_226_750_574_991_661_790_882_326_344_643"),
                    rs("-641_880_081_354_023\
                        _776_550_830_683_627_107_415_264_750_813_916_352_012\
                        _916_892_354_135_862_458_283_395_572_859_600_104_991\
                        /1_522_586_358_169_246_802_159_262_479_225\
                        _089_070_726_226_750_574_991_661_790_882_326_344_643"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(19), ri(3), ri(1), ri(8), ri(1), ri(15)].into(),
            9,
            vec![ri(14), ri(18), ri(19), ri(15), ri(2)].into(),
            Some(
                vec![
                    rs("183_864_245_907_369_396\
                        _262_818_683_259_858_562_011_239_970_198_416_224_361\
                        /2_199_023_255_552"),
                    rs("206_578_753_026_939_275\
                        _158_675_634_013_269_458_740_854_505_482_604_898_869\
                        /2_199_023_255_552"),
                    rs("432_056_388_746_881_938\
                        _212_218_906_859_738_649_474_466_080_817_341_258_057\
                        /4_398_046_511_104"),
                    rs("323_926_184_159_679_212\
                        _351_079_102_728_868_384_591_198_813_019_353_589_967\
                        /4_398_046_511_104"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(17), ri(10), ri(0), ri(4), ri(2), ri(7)].into(),
            3,
            vec![ri(19), ri(6), ri(16), ri(12), ri(4), ri(17)].into(),
            Some(
                vec![
                    r(-29_564_202_049_895_488, 34_271_896_307_633),
                    r(48_153_401_378_366_400, 34_271_896_307_633),
                    r(-41_388_846_548_268_584, 34_271_896_307_633),
                    r(-119_630_113_747_428_368, 34_271_896_307_633),
                    r(-12_216_433_291_469_664, 34_271_896_307_633),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(19), ri(18), ri(3), ri(8), ri(0), ri(13)].into(),
            17,
            vec![ri(0), ri(12), ri(17), ri(6), ri(0), ri(5)].into(),
            Some(
                vec![
                    ri(5_480_386_857_784_802_185_939),
                    rs("-199_181_510_200_419_956_944_406_163\
                        _900_186_065_760_784_614_171_896_741_299_325_912_226\
                        /45_474_735_088_646_411_895_751_953_125"),
                    rs("-360_855_964_928_129_145_144_700_016\
                        _411_567_649_299_329_458_811_289_334_205_946_200_526\
                        /45_474_735_088_646_411_895_751_953_125"),
                    rs("-186_124_086_992_514_304_492_086_605\
                        _885_305_421_818_548_544_034_196_320_342_212_070_118\
                        /45_474_735_088_646_411_895_751_953_125"),
                    rs("1_451_253_926_277_767_155_409_934\
                        _391_355_886_760_090_559_538_073_136_306_944_189_664\
                        /1_818_989_403_545_856_475_830_078_125"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(18), ri(3), ri(13), ri(10), ri(0), ri(4)].into(),
            15,
            vec![ri(4), ri(0), ri(2), ri(1), ri(19), ri(7)].into(),
            Some(
                vec![
                    rs("-11_659_710_255_519_802_866_695\
                        _898_334_575_123_267_771_756_924_089_785_612_612_717\
                        _976_528_922_402_404_763_064_886_961_283_834_373_444\
                        /1_004_525_211_269_079_039_999\
                        _221_534_496_697_502_180_541_686_174_722_466_474_743"),
                    rs("614_402_871_067_711_768_528\
                        _075_324_175_928_718_122_489_404_282_259_319_678_850\
                        _825_075_019_438_093_303_934_792_347_388_726_575_772\
                        /143_503_601_609_868_434_285\
                        _603_076_356_671_071_740_077_383_739_246_066_639_249"),
                    rs("-7_416_262_774_732_042_771_074\
                        _685_961_115_985_350_350_946_449_633_005_224_197_826\
                        _351_671_515_760_808_465_984_259_780_168_851_436_346\
                        /1_004_525_211_269_079_039_999\
                        _221_534_496_697_502_180_541_686_174_722_466_474_743"),
                    rs("-179_352_554_662_556_447_390\
                        _522_090_631_607_314_900_395_210_412_908_661_790_731\
                        _090_698_982_436_945_926_815_605_787_752_116_611_819\
                        /1_004_525_211_269_079_039_999\
                        _221_534_496_697_502_180_541_686_174_722_466_474_743"),
                    rs("-55_317_467_432_411_742_610_115\
                        _409_682_063_081_165_315_593_190_711_374_042_111_985\
                        _979_123_390_672_262_689_808_620_918_111_975_012_002\
                        /1_004_525_211_269_079_039_999\
                        _221_534_496_697_502_180_541_686_174_722_466_474_743"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(17), ri(4), ri(9), ri(13), ri(7)].into(),
            14,
            vec![ri(6), ri(16), ri(10), ri(8), ri(19), ri(5)].into(),
            Some(
                vec![
                    rs("1_658_576_216_060_625_927_424_495_888_882_593\
                        _070_876_010_790_000_557_338_684_203_198_509_426_341\
                        /2_220_446_049_250_313_080_847_263_336_181_640_625"),
                    rs("3_939_771_150_052_516_678_430_938_047_507_786\
                        _350_063_176_888_689_964_917_098_252_965_692_489_456\
                        /2_220_446_049_250_313_080_847_263_336_181_640_625"),
                    rs("323_348_808_826_878_438_489_548_215_154_638\
                        _655_320_647_817_371_193_357_502_061_263_063_808_888\
                        /444_089_209_850_062_616_169_452_667_236_328_125"),
                    rs("1_740_520_784_814_171_647_746_739_675_349_429\
                        _472_852_425_583_487_004_274_019_072_744_999_843_488\
                        /2_220_446_049_250_313_080_847_263_336_181_640_625"),
                    rs("4_745_191_003_416_840_637_610_402_202_757_026\
                        _412_479_924_455_694_027_706_709_720_816_291_990_899\
                        /2_220_446_049_250_313_080_847_263_336_181_640_625"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(14), ri(13), ri(1), ri(4), ri(5), ri(6)].into(),
            9,
            vec![ri(5), ri(19), ri(13), ri(6), ri(16), ri(2)].into(),
            Some(
                vec![
                    rs("-382_920\
                        _878_617_857_119_099_260_975_936_511_435_223_809_273\
                        /128"),
                    rs("-22_485_901\
                        _407_013_610_579_957_985_074_637_270_584_445_202_109\
                        /2048"),
                    rs("-13_009_231\
                        _280_273_529_135_224_470_876_129_436_700_263_261_949\
                        /2048"),
                    rs("-5_662_552\
                        _763_683_229_700_019_916_839_920_323_118_539_031_529\
                        /2048"),
                    rs("-2_358_768\
                        _110_430_007_164_332_017_062_130_636_819_640_631_241\
                        /256"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(7), ri(12), ri(3), ri(7), ri(19), ri(6)].into(),
            11,
            vec![ri(13), ri(15), ri(16), ri(3), ri(11), ri(5)].into(),
            Some(
                vec![
                    rs("22_752_247_755_277\
                        _538_997_707_495_297_327_392_111_003_638_158_183_387\
                        /444_089_209_850_062_616_169_452_667_236_328_125"),
                    rs("-733_940_325_151\
                        _897_434_394_130_395_242_811_794_063_264_377_833_748\
                        /3_552_713_678_800_500_929_355_621_337_890_625"),
                    rs("-84_810_889_149_159\
                        _019_771_112_545_298_336_067_913_002_777_931_249_341\
                        /444_089_209_850_062_616_169_452_667_236_328_125"),
                    rs("-74_539_559_704_585\
                        _890_609_937_306_779_895_161_442_574_758_737_655_248\
                        /444_089_209_850_062_616_169_452_667_236_328_125"),
                    rs("102_789_180_706_884\
                        _053_261_700_152_422_811_323_140_853_455_397_603_979\
                        /444_089_209_850_062_616_169_452_667_236_328_125"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(4), ri(19), ri(19), ri(12), ri(0), ri(5)].into(),
            18,
            vec![ri(10), ri(1), ri(0), ri(14), ri(3), ri(19)].into(),
            Some(
                vec![
                    rs("-2_364_027_447_920_040_483\
                        _558_170_899_680_841_147_253_334_862_133_661_950_470\
                        _294_306_349_500_397_445_060_747_086_071_248_342_845\
                        _046_495_819_755_810_577_833_846_890_367_689_045_344\
                        /93_931_159_192_635_254_915_820_471_057_358\
                        _992_010_808_400_674_497_210_917_407_177_698_488_916\
                        _879_344_705_049_022_303_605_110_796_637_313_140_281"),
                    rs("-3_812_396_385_964_512_812\
                        _050_368_825_254_461_542_621_783_190_875_160_619_418\
                        _534_476_927_696_279_683_046_456_030_039_715_558_897\
                        _554_572_655_006_572_053_071_773_941_842_915_329_128\
                        /93_931_159_192_635_254_915_820_471_057_358\
                        _992_010_808_400_674_497_210_917_407_177_698_488_916\
                        _879_344_705_049_022_303_605_110_796_637_313_140_281"),
                    rs("-147_348_947_733_136_287\
                        _828_033_078_051_205_913_542_662_008_515_448_696_098\
                        _645_594_136_143_579_474_944_274_069_836_870_085_610\
                        _414_452_386_441_898_907_965_014_020_611_318_843_218\
                        /4_943_745_220_665_013_416_622_130_055_650\
                        _473_263_726_757_930_236_695_311_442_483_036_762_574\
                        _572_597_089_739_422_226_505_532_147_191_437_533_699"),
                    rs("-2_175_945_530_518_382_417\
                        _710_604_352_936_440_137_198_454_349_166_062_523_986\
                        _361_078_069_727_263_659_940_243_402_271_841_613_182\
                        _099_377_444_542_459_770_717_460_322_951_952_128_629\
                        /93_931_159_192_635_254_915_820_471_057_358\
                        _992_010_808_400_674_497_210_917_407_177_698_488_916\
                        _879_344_705_049_022_303_605_110_796_637_313_140_281"),
                    rs("569_202_465_047_429_791\
                        _858_444_668_180_966_992_188_338_810_890_217_323_018\
                        _521_631_507_025_706_006_084_470_204_092_539_538_446\
                        _466_846_820_499_263_163_992_839_999_747_784_044_406\
                        /93_931_159_192_635_254_915_820_471_057_358\
                        _992_010_808_400_674_497_210_917_407_177_698_488_916\
                        _879_344_705_049_022_303_605_110_796_637_313_140_281"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(3), ri(18), ri(1), ri(19), ri(14), ri(9)].into(),
            15,
            vec![ri(5), ri(17), ri(10), ri(18), ri(16), ri(13)].into(),
            Some(
                vec![
                    rs("-9_030_256_198_923_778_738\
                        _792_551_656_220_010_998_656_383_359_725_043_968_030\
                        _991_677_342_942_958_176_064_317_482_609_363_474_326\
                        /12\
                        _302_064_898_724_710_532_827_150_598_154_059_319_480\
                        _431_430_194_019_567_533_837_617_701_744_247_540_837"),
                    rs("-106_017_687_103_287_863_924\
                        _627_265_731_596_197_311_263_591_870_778_821_408_379\
                        _206_053_143_672_619_946_570_415_310_252_729_476_609\
                        /12\
                        _302_064_898_724_710_532_827_150_598_154_059_319_480\
                        _431_430_194_019_567_533_837_617_701_744_247_540_837"),
                    rs("-178_963_907_034_841_735_192\
                        _725_016_237_377_022_008_248_269_739_374_463_063_399\
                        _062_728_714_683_439_471_100_528_967_752_348_048_013\
                        /12\
                        _302_064_898_724_710_532_827_150_598_154_059_319_480\
                        _431_430_194_019_567_533_837_617_701_744_247_540_837"),
                    rs("83_556_028_519_886_957_469\
                        _372_818_161_824_872_515_285_474_360_419_566_344_932\
                        _117_181_957_888_483_899_389_397_289_981_648_870_907\
                        /12\
                        _302_064_898_724_710_532_827_150_598_154_059_319_480\
                        _431_430_194_019_567_533_837_617_701_744_247_540_837"),
                    rs("-305_731_948_863_639_689_946\
                        _719_702_498_750_428_465_125_646_882_961_775_256_387\
                        _643_974_893_832_898_719_369_976_704_423_259_809_104\
                        /12\
                        _302_064_898_724_710_532_827_150_598_154_059_319_480\
                        _431_430_194_019_567_533_837_617_701_744_247_540_837"),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(17), ri(2), ri(10), ri(9), ri(9), ri(6)].into(),
            3,
            vec![ri(18), ri(12), ri(9), ri(0), ri(12), ri(15)].into(),
            Some(
                vec![
                    r(88_051_434_769, 48_828_125),
                    r(-61_852_202_584, 48_828_125),
                    r(54_119_428_802, 48_828_125),
                    r(-3_176_831_488, 9_765_625),
                    r(-32_512_922_104, 48_828_125),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(5), ri(9), ri(10), ri(16), ri(13), ri(15)].into(),
            4,
            vec![ri(19), ri(8), ri(14), ri(15), ri(18), ri(9)].into(),
            Some(
                vec![
                    r(318_286_343_720, 6561),
                    r(-19_744_400_801, 2187),
                    r(270_518_763_892, 6561),
                    r(87_138_110_534, 6561),
                    r(248_477_756_134, 6561),
                ]
                .into(),
            ),
        );
        test(
            vec![ri(15), ri(18), ri(6), ri(17), ri(13), ri(4)].into(),
            1,
            vec![ri(17), ri(18), ri(1), ri(16), ri(2), ri(11)].into(),
            Some(vec![r(97, 11), r(126, 11), r(62, 11), r(123, 11), r(135, 11)].into()),
        );
    }
}
