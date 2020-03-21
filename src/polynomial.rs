// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::traits::{
    AlwaysExactDivAssign, CharacteristicZero, ExactDiv, ExactDivAssign, GCDAndLCM,
    RingCharacteristic, GCD,
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{FromPrimitive, NumAssign, One, Pow, Signed, ToPrimitive, Zero};
use std::{
    borrow::Cow,
    error::Error,
    fmt, hash,
    iter::FromIterator,
    mem,
    ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    slice, vec,
};

mod add_sub;
mod distinct_degree_factorization;
mod div_rem;
mod factorization_over_integers;
mod gcd;
mod mul;
mod same_degree_factorization;

pub trait PolynomialCoefficientElement:
    PolynomialCoefficient<Divisor = DivisorIsOne>
    + Add<Output = Self>
    + Sub<Output = Self>
    + Mul<Output = Self>
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + Neg<Output = Self>
    + AddAssign
    + SubAssign
    + MulAssign
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> MulAssign<&'a Self>
{
}

impl<
        T: PolynomialCoefficient<Divisor = DivisorIsOne>
            + Add<Output = Self>
            + Sub<Output = Self>
            + Mul<Output = Self>
            + for<'a> Add<&'a Self, Output = Self>
            + for<'a> Sub<&'a Self, Output = Self>
            + for<'a> Mul<&'a Self, Output = Self>
            + Neg<Output = Self>
            + AddAssign
            + SubAssign
            + MulAssign
            + for<'a> AddAssign<&'a Self>
            + for<'a> SubAssign<&'a Self>
            + for<'a> MulAssign<&'a Self>,
    > PolynomialCoefficientElement for T
{
}

pub trait PolynomialCoefficient:
    Clone
    + Eq
    + fmt::Debug
    + hash::Hash
    + Add<Output = Self>
    + Mul<Output = Self>
    + Sub<Output = Self>
    + Neg<Output = Self>
    + AddAssign
    + MulAssign
    + SubAssign
    + for<'a> Add<&'a Self, Output = Self>
    + for<'a> Sub<&'a Self, Output = Self>
    + for<'a> Mul<&'a Self, Output = Self>
    + for<'a> AddAssign<&'a Self>
    + for<'a> SubAssign<&'a Self>
    + for<'a> MulAssign<&'a Self>
{
    type Element: PolynomialCoefficientElement;
    type Divisor: Clone
        + Eq
        + fmt::Debug
        + hash::Hash
        + Mul<Output = Self::Divisor>
        + MulAssign
        + for<'a> Mul<&'a Self::Divisor, Output = Self::Divisor>
        + for<'a> MulAssign<&'a Self::Divisor>
        + ExactDiv<Output = Self::Divisor>
        + ExactDivAssign
        + for<'a> ExactDiv<&'a Self::Divisor, Output = Self::Divisor>
        + for<'a> ExactDivAssign<&'a Self::Divisor>
        + GCD<Output = Self::Divisor>
        + One;
    const NESTING_DEPTH: usize;
    fn is_element_zero(element: &Self::Element) -> bool;
    fn is_element_one(element: &Self::Element) -> bool;
    fn is_coefficient_zero(coefficient: &Self) -> bool;
    fn is_coefficient_one(coefficient: &Self) -> bool;
    fn set_element_zero(element: &mut Self::Element);
    fn set_element_one(element: &mut Self::Element);
    fn set_coefficient_zero(coefficient: &mut Self);
    fn set_coefficient_one(coefficient: &mut Self);
    fn make_zero_element(element: Cow<Self::Element>) -> Self::Element {
        let mut element = element.into_owned();
        Self::set_element_zero(&mut element);
        element
    }
    fn make_one_element(element: Cow<Self::Element>) -> Self::Element {
        let mut element = element.into_owned();
        Self::set_element_one(&mut element);
        element
    }
    fn make_zero_coefficient_from_element(element: Cow<Self::Element>) -> Self {
        Self::make_coefficient(
            Cow::Owned(Self::make_zero_element(element)),
            Cow::Owned(One::one()),
        )
    }
    fn make_one_coefficient_from_element(element: Cow<Self::Element>) -> Self {
        Self::make_coefficient(
            Cow::Owned(Self::make_one_element(element)),
            Cow::Owned(One::one()),
        )
    }
    fn make_zero_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
        let mut coefficient = coefficient.into_owned();
        Self::set_coefficient_zero(&mut coefficient);
        coefficient
    }
    fn make_one_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
        let mut coefficient = coefficient.into_owned();
        Self::set_coefficient_one(&mut coefficient);
        coefficient
    }
    fn negate_element(element: &mut Self::Element) {
        let zero = Self::make_zero_element(Cow::Borrowed(&element));
        *element = -mem::replace(element, zero);
    }
    fn mul_element_by_usize(element: Cow<Self::Element>, multiplier: usize) -> Self::Element;
    fn mul_assign_element_by_usize(element: &mut Self::Element, multiplier: usize);
    fn divisor_to_element(
        v: Cow<Self::Divisor>,
        other_element: Cow<Self::Element>,
    ) -> Self::Element;
    fn coefficients_to_elements(coefficients: Cow<[Self]>) -> (Vec<Self::Element>, Self::Divisor);
    fn make_coefficient(element: Cow<Self::Element>, divisor: Cow<Self::Divisor>) -> Self;
    fn reduce_divisor(elements: &mut [Self::Element], divisor: &mut Self::Divisor);
    fn get_reduced_divisor(
        elements: &[Self::Element],
        divisor: &Self::Divisor,
    ) -> (Vec<Self::Element>, Self::Divisor) {
        let mut elements = elements.to_vec();
        let mut divisor = divisor.clone();
        Self::reduce_divisor(&mut elements, &mut divisor);
        (elements, divisor)
    }
    fn coefficient_to_element(coefficient: Cow<Self>) -> (Self::Element, Self::Divisor);
    fn divisor_pow_usize(mut base: Self::Divisor, mut exponent: usize) -> Self::Divisor {
        if exponent == 0 {
            return One::one();
        }
        let mut retval = None;
        loop {
            if exponent % 2 != 0 {
                match &mut retval {
                    None => retval = Some(base.clone()),
                    Some(retval) => *retval *= &base,
                }
            }
            exponent /= 2;
            if exponent == 0 {
                break;
            }
            base *= base.clone();
        }
        retval.unwrap_or_else(|| unreachable!())
    }
    fn element_pow_usize(mut base: Self::Element, mut exponent: usize) -> Self::Element {
        if exponent == 0 {
            return Self::make_one_element(Cow::Owned(base));
        }
        let mut retval = None;
        loop {
            if exponent % 2 != 0 {
                match &mut retval {
                    None => retval = Some(base.clone()),
                    Some(retval) => *retval *= &base,
                }
            }
            exponent /= 2;
            if exponent == 0 {
                break;
            }
            base *= base.clone();
        }
        retval.unwrap_or_else(|| unreachable!())
    }
    fn coefficient_pow_usize(mut base: Self, mut exponent: usize) -> Self {
        if exponent == 0 {
            return Self::make_one_coefficient_from_coefficient(Cow::Owned(base));
        }
        let mut retval = None;
        loop {
            if exponent % 2 != 0 {
                match &mut retval {
                    None => retval = Some(base.clone()),
                    Some(retval) => *retval *= &base,
                }
            }
            exponent /= 2;
            if exponent == 0 {
                break;
            }
            base *= base.clone();
        }
        retval.unwrap_or_else(|| unreachable!())
    }
    fn from_iterator<I: Iterator<Item = Self>>(iter: I) -> Polynomial<Self> {
        Self::coefficients_to_elements(Cow::Owned(iter.collect())).into()
    }
}

pub trait PolynomialCoefficientAbsSupported: PolynomialCoefficient {
    fn coefficient_abs(coefficient: Self) -> Self;
}

impl<
        T: PolynomialCoefficientElement
            + Integer
            + NumAssign
            + FromPrimitive
            + GCD<Output = T>
            + ExactDivAssign
            + for<'a> ExactDivAssign<&'a T>
            + PolynomialCoefficientAbsSupported,
    > PolynomialCoefficientAbsSupported for Ratio<T>
{
    fn coefficient_abs(coefficient: Self) -> Self {
        let (numer, denom) = coefficient.into();
        Ratio::new(T::coefficient_abs(numer), denom)
    }
}

pub trait PolynomialReducingFactorSupported: PolynomialCoefficient {
    /// returns the factor `f` of the passed in polynomial `p` where `p / f` is content-free (for integer polynomials) or monic (for polynomials over fields).
    fn get_nonzero_reducing_factor(
        elements: &[Self::Element],
        divisor: &Self::Divisor,
    ) -> Option<Self>;
}

impl<
        T: PolynomialCoefficientElement
            + Integer
            + NumAssign
            + FromPrimitive
            + GCD<Output = T>
            + ExactDivAssign
            + for<'a> ExactDivAssign<&'a T>,
    > PolynomialReducingFactorSupported for Ratio<T>
{
    fn get_nonzero_reducing_factor(
        elements: &[Self::Element],
        divisor: &Self::Divisor,
    ) -> Option<Self> {
        Some(Ratio::new(elements.last()?.clone(), divisor.clone()))
    }
}

impl<
        T: PolynomialCoefficientElement
            + Integer
            + for<'a> ExactDivAssign<&'a T>
            + ExactDivAssign
            + NumAssign
            + FromPrimitive
            + GCD<Output = T>,
    > PolynomialCoefficient for Ratio<T>
{
    type Element = T;
    type Divisor = T;
    const NESTING_DEPTH: usize = 0;
    fn is_element_zero(element: &Self::Element) -> bool {
        element.is_zero()
    }
    fn is_element_one(element: &Self::Element) -> bool {
        element.is_one()
    }
    fn is_coefficient_zero(coefficient: &Self) -> bool {
        coefficient.is_zero()
    }
    fn is_coefficient_one(coefficient: &Self) -> bool {
        coefficient.is_one()
    }
    fn set_element_zero(element: &mut Self::Element) {
        element.set_zero();
    }
    fn set_element_one(element: &mut Self::Element) {
        element.set_one();
    }
    fn set_coefficient_zero(coefficient: &mut Self) {
        coefficient.set_zero();
    }
    fn set_coefficient_one(coefficient: &mut Self) {
        coefficient.set_one();
    }
    fn make_zero_element(element: Cow<Self::Element>) -> Self::Element {
        match element {
            Cow::Borrowed(_) => Zero::zero(),
            Cow::Owned(mut element) => {
                element.set_zero();
                element
            }
        }
    }
    fn make_one_element(element: Cow<Self::Element>) -> Self::Element {
        match element {
            Cow::Borrowed(_) => One::one(),
            Cow::Owned(mut element) => {
                element.set_one();
                element
            }
        }
    }
    fn make_zero_coefficient_from_element(element: Cow<Self::Element>) -> Self {
        match element {
            Cow::Borrowed(_) => Zero::zero(),
            Cow::Owned(element) => {
                let mut coefficient = Ratio::from(element);
                coefficient.set_zero();
                coefficient
            }
        }
    }
    fn make_one_coefficient_from_element(element: Cow<Self::Element>) -> Self {
        match element {
            Cow::Borrowed(_) => One::one(),
            Cow::Owned(element) => {
                let mut coefficient = Ratio::from(element);
                coefficient.set_one();
                coefficient
            }
        }
    }
    fn make_zero_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
        match coefficient {
            Cow::Borrowed(_) => Zero::zero(),
            Cow::Owned(mut coefficient) => {
                coefficient.set_zero();
                coefficient
            }
        }
    }
    fn make_one_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
        match coefficient {
            Cow::Borrowed(_) => One::one(),
            Cow::Owned(mut coefficient) => {
                coefficient.set_one();
                coefficient
            }
        }
    }
    fn negate_element(element: &mut Self::Element) {
        *element = -mem::replace(element, Zero::zero());
    }
    fn mul_element_by_usize(element: Cow<Self::Element>, multiplier: usize) -> Self::Element {
        let multiplier =
            Self::Element::from_usize(multiplier).expect("can't convert multiplier to element");
        element.into_owned() * multiplier
    }
    fn mul_assign_element_by_usize(element: &mut Self::Element, multiplier: usize) {
        *element *=
            Self::Element::from_usize(multiplier).expect("can't convert multiplier to element");
    }
    fn divisor_to_element(v: Cow<Self::Divisor>, _: Cow<Self::Element>) -> Self::Element {
        v.into_owned()
    }
    fn coefficients_to_elements(coefficients: Cow<[Self]>) -> (Vec<Self::Element>, Self::Divisor) {
        let mut coefficients_iter = coefficients.iter();
        let divisor = match coefficients_iter.next() {
            None => return (Vec::new(), One::one()),
            Some(divisor) => divisor.denom(),
        };
        let divisor = match coefficients_iter.next() {
            None => {
                let coefficient = match coefficients {
                    Cow::Owned(mut coefficients) => {
                        coefficients.pop().expect("coefficients should be size 1")
                    }
                    Cow::Borrowed(coefficients) => coefficients[0].clone(),
                };
                let (numer, denom) = coefficient.into();
                return (vec![numer], denom);
            }
            Some(v) => GCD::lcm(divisor, v.denom()),
        };
        let divisor: T =
            coefficients_iter.fold(divisor, |divisor, v| GCD::lcm(&divisor, v.denom()));
        let get_element = |coefficient: Self| {
            let (numer, denom) = coefficient.into();
            numer * (divisor.clone() / denom)
        };
        let elements = match coefficients {
            Cow::Owned(coefficients) => coefficients.into_iter().map(get_element).collect(),
            Cow::Borrowed(coefficients) => coefficients.iter().cloned().map(get_element).collect(),
        };
        (elements, divisor)
    }
    fn make_coefficient(element: Cow<Self::Element>, divisor: Cow<Self::Divisor>) -> Self {
        Self::new(element.into_owned(), divisor.into_owned())
    }
    fn reduce_divisor(elements: &mut [Self::Element], divisor: &mut Self::Divisor) {
        if elements.is_empty() {
            divisor.set_one();
            return;
        }
        let mut elements_iter = elements.iter();
        let gcd = elements_iter
            .next()
            .expect("not empty since already checked");
        let gcd = elements_iter.fold(GCD::gcd(gcd, divisor), |gcd, element| {
            GCD::gcd(&gcd, element)
        });
        if gcd.is_one() {
            return;
        }
        elements
            .iter_mut()
            .for_each(|element| element.exact_div_assign(&gcd));
        *divisor /= gcd;
    }
    fn get_reduced_divisor(
        elements: &[Self::Element],
        divisor: &Self::Divisor,
    ) -> (Vec<Self::Element>, Self::Divisor) {
        if elements.is_empty() {
            return (Vec::new(), One::one());
        }
        let mut elements_iter = elements.iter();
        let gcd = elements_iter
            .next()
            .expect("not empty since already checked");
        let gcd = elements_iter.fold(GCD::gcd(gcd, divisor), |gcd, element| {
            GCD::gcd(&gcd, element)
        });
        let elements = elements
            .iter()
            .map(|element| element.clone().exact_div(&gcd))
            .collect();
        let mut divisor = divisor.clone();
        divisor /= gcd;
        (elements, divisor)
    }
    fn coefficient_to_element(coefficient: Cow<Self>) -> (Self::Element, Self::Divisor) {
        coefficient.into_owned().into()
    }
}

#[derive(Copy, Clone, Hash, Debug, Eq, PartialEq)]
pub struct DivisorIsOne;

impl MulAssign for DivisorIsOne {
    fn mul_assign(&mut self, _rhs: DivisorIsOne) {}
}

impl MulAssign<&DivisorIsOne> for DivisorIsOne {
    fn mul_assign(&mut self, _rhs: &DivisorIsOne) {}
}

impl Mul for DivisorIsOne {
    type Output = DivisorIsOne;
    fn mul(self, _rhs: DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl Mul<&DivisorIsOne> for DivisorIsOne {
    type Output = DivisorIsOne;
    fn mul(self, _rhs: &DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl Mul<DivisorIsOne> for &DivisorIsOne {
    type Output = DivisorIsOne;
    fn mul(self, _rhs: DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl<'a, 'b> Mul<&'a DivisorIsOne> for &'b DivisorIsOne {
    type Output = DivisorIsOne;
    fn mul(self, _rhs: &DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl ExactDivAssign for DivisorIsOne {
    fn checked_exact_div_assign(&mut self, _rhs: DivisorIsOne) -> Result<(), ()> {
        Ok(())
    }
    fn exact_div_assign(&mut self, _rhs: DivisorIsOne) {}
}

impl ExactDivAssign<&DivisorIsOne> for DivisorIsOne {
    fn checked_exact_div_assign(&mut self, _rhs: &DivisorIsOne) -> Result<(), ()> {
        Ok(())
    }
    fn exact_div_assign(&mut self, _rhs: &DivisorIsOne) {}
}

impl ExactDiv for DivisorIsOne {
    type Output = DivisorIsOne;
    fn checked_exact_div(self, _rhs: DivisorIsOne) -> Option<DivisorIsOne> {
        Some(DivisorIsOne)
    }
    fn exact_div(self, _rhs: DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl ExactDiv<&DivisorIsOne> for DivisorIsOne {
    type Output = DivisorIsOne;
    fn checked_exact_div(self, _rhs: &DivisorIsOne) -> Option<DivisorIsOne> {
        Some(DivisorIsOne)
    }
    fn exact_div(self, _rhs: &DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl ExactDiv<DivisorIsOne> for &DivisorIsOne {
    type Output = DivisorIsOne;
    fn checked_exact_div(self, _rhs: DivisorIsOne) -> Option<DivisorIsOne> {
        Some(DivisorIsOne)
    }
    fn exact_div(self, _rhs: DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl<'a, 'b> ExactDiv<&'a DivisorIsOne> for &'b DivisorIsOne {
    type Output = DivisorIsOne;
    fn checked_exact_div(self, _rhs: &DivisorIsOne) -> Option<DivisorIsOne> {
        Some(DivisorIsOne)
    }
    fn exact_div(self, _rhs: &DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl GCD for DivisorIsOne {
    type Output = DivisorIsOne;
    fn gcd_lcm(&self, _rhs: &DivisorIsOne) -> GCDAndLCM<DivisorIsOne> {
        GCDAndLCM {
            gcd: DivisorIsOne,
            lcm: DivisorIsOne,
        }
    }
}

impl One for DivisorIsOne {
    fn one() -> Self {
        DivisorIsOne
    }
    fn is_one(&self) -> bool {
        true
    }
}

macro_rules! impl_polynomial_coefficient_for_int {
    ($t:ty) => {
        impl PolynomialCoefficient for $t {
            type Element = $t;
            type Divisor = DivisorIsOne;
            const NESTING_DEPTH: usize = 0;
            fn is_element_zero(element:&Self::Element) -> bool {
                element.is_zero()
            }
            fn is_element_one(element:&Self::Element) -> bool {
                element.is_one()
            }
            fn is_coefficient_zero(coefficient:&Self) -> bool {
                coefficient.is_zero()
            }
            fn is_coefficient_one(coefficient:&Self) -> bool {
                coefficient.is_one()
            }
            fn set_element_zero(element: &mut Self::Element) {
                element.set_zero();
            }
            fn set_element_one(element: &mut Self::Element) {
                element.set_one();
            }
            fn set_coefficient_zero(coefficient: &mut Self) {
                coefficient.set_zero();
            }
            fn set_coefficient_one(coefficient: &mut Self) {
                coefficient.set_one();
            }
            fn make_zero_element(element: Cow<Self::Element>) -> Self::Element {
                match element {
                    Cow::Borrowed(_) => Zero::zero(),
                    Cow::Owned(mut element) => {element.set_zero(); element}
                }
            }
            fn make_one_element(element: Cow<Self::Element>) -> Self::Element {
                match element {
                    Cow::Borrowed(_) => One::one(),
                    Cow::Owned(mut element) => {element.set_one(); element}
                }
            }
            fn make_zero_coefficient_from_element(element: Cow<Self::Element>) -> Self {
                Self::make_zero_element(element)
            }
            fn make_one_coefficient_from_element(element: Cow<Self::Element>) -> Self {
                Self::make_one_element(element)
            }
            fn make_zero_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
                Self::make_zero_element(coefficient)
            }
            fn make_one_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
                Self::make_one_element(coefficient)
            }
            fn negate_element(element: &mut Self::Element) {
                *element = -mem::replace(element, Zero::zero());
            }
            fn mul_element_by_usize(element: Cow<Self::Element>, multiplier: usize) -> Self::Element {
                let multiplier = Self::Element::from_usize(multiplier).expect("can't convert multiplier to element");
                match element {
                    Cow::Borrowed(element)=>element * multiplier,
                    Cow::Owned(element)=>element * multiplier,
                }
            }
            fn mul_assign_element_by_usize(element: &mut Self::Element, multiplier: usize) {
                *element *= Self::Element::from_usize(multiplier).expect("can't convert multiplier to element");
            }
            fn divisor_to_element(_v: Cow<Self::Divisor>, _: Cow<Self::Element>) -> Self::Element {
                One::one()
            }
            fn coefficients_to_elements(coefficients: Cow<[Self]>) -> (Vec<Self::Element>, Self::Divisor) {
                (coefficients.into_owned(), DivisorIsOne)
            }
            fn make_coefficient(element: Cow<Self::Element>, _divisor: Cow<Self::Divisor>) -> Self {
                element.into_owned()
            }
            fn reduce_divisor(_elements: &mut [Self::Element], _divisor: &mut Self::Divisor) {
            }
            fn coefficient_to_element(coefficient: Cow<Self>) -> (Self::Element, Self::Divisor) {
                (coefficient.into_owned(), DivisorIsOne)
            }
        }

        impl PolynomialReducingFactorSupported for $t {
            fn get_nonzero_reducing_factor(elements: &[Self::Element], _divisor: &Self::Divisor) -> Option<Self> {
                if let Some(mut retval) = elements.iter().fold(None, |lhs: Option<Self>, rhs| match lhs {
                    None => Some(rhs.clone()),
                    Some(lhs) => Some(GCD::gcd(&lhs, &rhs)),
                }) {
                    let c = elements
                        .last()
                        .expect("known to be nonzero");
                    let zero = Self::zero();
                    if (*c < zero) != (retval < zero) {
                        retval = zero - retval;
                    }
                    Some(retval)
                } else {
                    None
                }
            }
        }

        impl PolynomialCoefficientAbsSupported for $t {
            fn coefficient_abs(coefficient: Self) -> Self {
                coefficient.abs()
            }
        }
    };
    {$($t:ty;)+} => {
        $(
            impl_polynomial_coefficient_for_int!($t);
        )+
    };
}

impl_polynomial_coefficient_for_int! {
    i8;
    i16;
    i32;
    i64;
    i128;
    isize;
    BigInt;
}

impl<T: PolynomialCoefficient<Divisor = DivisorIsOne, Element = T> + One> PolynomialCoefficient
    for Polynomial<T>
where
    T::Element: Zero + One,
{
    type Element = Polynomial<T>;
    type Divisor = DivisorIsOne;
    const NESTING_DEPTH: usize = T::NESTING_DEPTH + 1;
    fn is_element_zero(element: &Self::Element) -> bool {
        element.is_zero()
    }
    fn is_element_one(element: &Self::Element) -> bool {
        element.is_one()
    }
    fn is_coefficient_zero(coefficient: &Self) -> bool {
        coefficient.is_zero()
    }
    fn is_coefficient_one(coefficient: &Self) -> bool {
        coefficient.is_one()
    }
    fn set_element_zero(element: &mut Self::Element) {
        element.set_zero();
    }
    fn set_element_one(element: &mut Self::Element) {
        element.set_one();
    }
    fn set_coefficient_zero(coefficient: &mut Self) {
        coefficient.set_zero();
    }
    fn set_coefficient_one(coefficient: &mut Self) {
        coefficient.set_one();
    }
    fn make_zero_element(_element: Cow<Self::Element>) -> Self::Element {
        Zero::zero()
    }
    fn make_one_element(element: Cow<Self::Element>) -> Self::Element {
        if let Cow::Owned(mut element) = element {
            element.set_one();
            element
        } else {
            One::one()
        }
    }
    fn make_zero_coefficient_from_element(_element: Cow<Self::Element>) -> Self {
        Zero::zero()
    }
    fn make_one_coefficient_from_element(element: Cow<Self::Element>) -> Self {
        Self::make_one_element(element)
    }
    fn make_zero_coefficient_from_coefficient(_coefficient: Cow<Self>) -> Self {
        Zero::zero()
    }
    fn make_one_coefficient_from_coefficient(coefficient: Cow<Self>) -> Self {
        Self::make_one_element(coefficient)
    }
    fn negate_element(element: &mut Self::Element) {
        *element = -mem::replace(element, Zero::zero());
    }
    fn mul_element_by_usize(element: Cow<Self::Element>, multiplier: usize) -> Self::Element {
        let mut element = element.into_owned();
        Self::mul_assign_element_by_usize(&mut element, multiplier);
        element
    }
    fn mul_assign_element_by_usize(element: &mut Self::Element, multiplier: usize) {
        for sub_element in &mut element.elements {
            T::mul_assign_element_by_usize(sub_element, multiplier);
        }
    }
    fn divisor_to_element(
        _v: Cow<Self::Divisor>,
        other_element: Cow<Self::Element>,
    ) -> Self::Element {
        Self::make_one_element(other_element)
    }
    fn coefficients_to_elements(coefficients: Cow<[Self]>) -> (Vec<Self::Element>, Self::Divisor) {
        (coefficients.into_owned(), DivisorIsOne)
    }
    fn make_coefficient(element: Cow<Self::Element>, _divisor: Cow<Self::Divisor>) -> Self {
        element.into_owned()
    }
    fn reduce_divisor(_elements: &mut [Self::Element], _divisor: &mut Self::Divisor) {}
    fn get_reduced_divisor(
        elements: &[Self::Element],
        _divisor: &Self::Divisor,
    ) -> (Vec<Self::Element>, Self::Divisor) {
        (elements.to_vec(), DivisorIsOne)
    }
    fn coefficient_to_element(coefficient: Cow<Self>) -> (Self::Element, Self::Divisor) {
        (coefficient.into_owned(), DivisorIsOne)
    }
    fn divisor_pow_usize(_base: Self::Divisor, _exponent: usize) -> Self::Divisor {
        DivisorIsOne
    }
    fn element_pow_usize(base: Self::Element, exponent: usize) -> Self::Element {
        base.pow(exponent)
    }
    fn coefficient_pow_usize(base: Self, exponent: usize) -> Self {
        base.pow(exponent)
    }
}

pub trait PolynomialDivSupported:
    PolynomialCoefficient + for<'a> AlwaysExactDivAssign<&'a Self> + AlwaysExactDivAssign
{
}

impl<T: PolynomialCoefficient> PolynomialDivSupported for T where
    T: AlwaysExactDivAssign + for<'a> AlwaysExactDivAssign<&'a T>
{
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PseudoDivRem<T: PolynomialCoefficient> {
    pub quotient: Polynomial<T>,
    pub remainder: Polynomial<T>,
    pub factor: T,
}

/// A single-variable polynomial.
///
/// the term at index `n` is `self.coefficients()[n] * pow(x, n)`
///
/// # Invariants
///
/// `self.coefficients().last()` is either `None` or `Some(v)` where `!v.is_zero()`
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Polynomial<T: PolynomialCoefficient> {
    elements: Vec<T::Element>,
    divisor: T::Divisor,
}

impl<T: PolynomialCoefficient> FromIterator<T> for Polynomial<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        T::from_iterator(iter.into_iter())
    }
}

impl<T: PolynomialCoefficient> Default for Polynomial<T> {
    fn default() -> Self {
        Polynomial {
            elements: Vec::new(),
            divisor: One::one(),
        }
    }
}

impl<'a, T: PolynomialCoefficient> From<Cow<'a, [T]>> for Polynomial<T> {
    fn from(mut coefficients: Cow<'a, [T]>) -> Self {
        match &mut coefficients {
            Cow::Borrowed(coefficients) => {
                while let Some((last, rest)) = coefficients.split_last() {
                    if !T::is_coefficient_zero(last) {
                        break;
                    }
                    *coefficients = rest;
                }
            }
            Cow::Owned(coefficients) => {
                while let Some(last) = coefficients.last() {
                    if !T::is_coefficient_zero(last) {
                        break;
                    }
                    coefficients.pop();
                }
            }
        }
        let (elements, divisor) = T::coefficients_to_elements(coefficients);
        Self { elements, divisor }
    }
}

impl<T: PolynomialCoefficient> From<Vec<T>> for Polynomial<T> {
    fn from(coefficients: Vec<T>) -> Self {
        Self::from(Cow::Owned(coefficients))
    }
}

macro_rules! from_array {
    ($n:expr, [$($v:ident),*]) => {
        impl<T: PolynomialCoefficient> From<[T; $n]> for Polynomial<T> {
            fn from(coefficients: [T; $n]) -> Self {
                let [$($v),*] = coefficients;
                Self::from(Cow::Owned(vec![$($v),*]))
            }
        }
    };
}

from_array!(0, []);
from_array!(1, [c0]);
from_array!(2, [c0, c1]);
from_array!(3, [c0, c1, c2]);
from_array!(4, [c0, c1, c2, c3]);
from_array!(5, [c0, c1, c2, c3, c4]);
from_array!(6, [c0, c1, c2, c3, c4, c5]);
from_array!(7, [c0, c1, c2, c3, c4, c5, c6]);
from_array!(8, [c0, c1, c2, c3, c4, c5, c6, c7]);
from_array!(9, [c0, c1, c2, c3, c4, c5, c6, c7, c8]);
from_array!(10, [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9]);
from_array!(11, [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10]);
from_array!(12, [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11]);
from_array!(13, [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12]);
from_array!(
    14,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13]
);
from_array!(
    15,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14]
);
from_array!(
    16,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15]
);
from_array!(
    17,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16]
);
from_array!(
    18,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17]
);
from_array!(
    19,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18]
);
from_array!(
    20,
    [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19]
);
from_array!(
    21,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20
    ]
);
from_array!(
    22,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21
    ]
);
from_array!(
    23,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22
    ]
);
from_array!(
    24,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23
    ]
);
from_array!(
    25,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24
    ]
);
from_array!(
    26,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25
    ]
);
from_array!(
    27,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26
    ]
);
from_array!(
    28,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27
    ]
);
from_array!(
    29,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27, c28
    ]
);
from_array!(
    30,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27, c28, c29
    ]
);
from_array!(
    31,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30
    ]
);
from_array!(
    32,
    [
        c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19,
        c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31
    ]
);

impl<T: PolynomialCoefficient> From<&'_ [T]> for Polynomial<T> {
    fn from(coefficients: &[T]) -> Self {
        Self::from(Cow::Borrowed(coefficients))
    }
}

impl<T: PolynomialCoefficient> From<T> for Polynomial<T> {
    fn from(coefficient: T) -> Self {
        let (element, divisor) = T::coefficient_to_element(Cow::Owned(coefficient));
        if T::is_element_zero(&element) {
            Zero::zero()
        } else {
            Self {
                elements: vec![element],
                divisor,
            }
        }
    }
}

impl<T: PolynomialCoefficient> From<&T> for Polynomial<T> {
    fn from(coefficient: &T) -> Self {
        let (element, divisor) = T::coefficient_to_element(Cow::Borrowed(coefficient));
        if T::is_element_zero(&element) {
            Zero::zero()
        } else {
            Self {
                elements: vec![element],
                divisor,
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct Iter<'a, T: PolynomialCoefficient> {
    elements: slice::Iter<'a, T::Element>,
    divisor: &'a T::Divisor,
}

impl<T: PolynomialCoefficient> Iterator for Iter<'_, T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        Some(T::make_coefficient(
            Cow::Borrowed(self.elements.next()?),
            Cow::Borrowed(self.divisor),
        ))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.elements.size_hint()
    }
}

impl<T: PolynomialCoefficient> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<T> {
        Some(T::make_coefficient(
            Cow::Borrowed(self.elements.next_back()?),
            Cow::Borrowed(self.divisor),
        ))
    }
}

impl<T: PolynomialCoefficient> ExactSizeIterator for Iter<'_, T> {}

#[derive(Clone, Debug)]
pub struct IntoIter<T: PolynomialCoefficient> {
    elements: vec::IntoIter<T::Element>,
    divisor: Option<T::Divisor>,
}

impl<T: PolynomialCoefficient> Iterator for IntoIter<T> {
    type Item = T;
    fn next(&mut self) -> Option<T> {
        let divisor = if self.elements.as_slice().len() == 1 {
            Cow::Owned(self.divisor.take()?)
        } else {
            Cow::Borrowed(self.divisor.as_ref()?)
        };
        Some(T::make_coefficient(
            Cow::Owned(self.elements.next()?),
            divisor,
        ))
    }
    fn size_hint(&self) -> (usize, Option<usize>) {
        self.elements.size_hint()
    }
}

impl<T: PolynomialCoefficient> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<T> {
        let divisor = if self.elements.as_slice().len() == 1 {
            Cow::Owned(self.divisor.take()?)
        } else {
            Cow::Borrowed(self.divisor.as_ref()?)
        };
        Some(T::make_coefficient(
            Cow::Owned(self.elements.next_back()?),
            divisor,
        ))
    }
}

impl<T: PolynomialCoefficient> ExactSizeIterator for IntoIter<T> {}

impl<T: PolynomialCoefficient> IntoIterator for Polynomial<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    fn into_iter(self) -> IntoIter<T> {
        IntoIter {
            elements: self.elements.into_iter(),
            divisor: Some(self.divisor),
        }
    }
}

impl<T: PolynomialCoefficient> From<(Vec<T::Element>, T::Divisor)> for Polynomial<T> {
    fn from((elements, divisor): (Vec<T::Element>, T::Divisor)) -> Self {
        Self { elements, divisor }.into_normalized()
    }
}

impl<T: PolynomialCoefficient> Into<(Vec<T::Element>, T::Divisor)> for Polynomial<T> {
    fn into(self) -> (Vec<T::Element>, T::Divisor) {
        (self.elements, self.divisor)
    }
}

impl<T: PolynomialCoefficient> Polynomial<T> {
    pub fn make_monomial(coefficient: T, variable_exponent: usize) -> Self {
        if T::is_coefficient_zero(&coefficient) {
            return Self::zero();
        }
        let (element, divisor) = T::coefficient_to_element(Cow::Owned(coefficient));
        let mut elements = Vec::with_capacity(variable_exponent + 1);
        elements
            .extend((0..variable_exponent).map(|_| T::make_zero_element(Cow::Borrowed(&element))));
        elements.push(element);
        Self { elements, divisor }
    }
    pub fn nonzero_coefficient(&self, index: usize) -> Option<T> {
        Some(T::make_coefficient(
            Cow::Borrowed(self.elements.get(index)?),
            Cow::Borrowed(&self.divisor),
        ))
    }
    pub fn coefficient(&self, index: usize) -> T
    where
        T: Zero,
    {
        self.nonzero_coefficient(index).unwrap_or_else(T::zero)
    }
    pub fn nonzero_highest_power_coefficient(&self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            self.nonzero_coefficient(self.len() - 1)
        }
    }
    pub fn highest_power_coefficient(&self) -> T
    where
        T: Zero,
    {
        self.nonzero_highest_power_coefficient()
            .unwrap_or_else(Zero::zero)
    }
    pub fn into_coefficients(self) -> Vec<T> {
        let divisor = &self.divisor;
        self.elements
            .into_iter()
            .map(|element| T::make_coefficient(Cow::Owned(element), Cow::Borrowed(divisor)))
            .collect()
    }
    pub fn split_out_divisor(self) -> (Vec<T::Element>, T::Divisor) {
        self.into()
    }
    pub fn iter(&self) -> Iter<T> {
        Iter {
            elements: self.elements.iter(),
            divisor: &self.divisor,
        }
    }
    pub fn len(&self) -> usize {
        self.elements.len()
    }
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }
    pub fn degree(&self) -> Option<usize> {
        self.len().checked_sub(1)
    }
    fn normalize(&mut self) {
        while let Some(last) = self.elements.last() {
            if !T::is_element_zero(last) {
                break;
            }
            self.elements.pop();
        }
        T::reduce_divisor(&mut self.elements, &mut self.divisor);
    }
    fn into_normalized(mut self) -> Self {
        self.normalize();
        self
    }
    pub fn negate(&mut self) {
        self.elements.iter_mut().for_each(T::negate_element);
    }
    /// returns greatest common divisor of all coefficients
    pub fn nonzero_content(&self) -> Option<T>
    where
        T: GCD<Output = T> + PartialOrd,
    {
        if let Some(mut retval) = self.iter().fold(None, |lhs: Option<T>, rhs| match lhs {
            None => Some(rhs),
            Some(lhs) => Some(lhs.gcd(&rhs)),
        }) {
            let c = self
                .nonzero_highest_power_coefficient()
                .expect("known to be nonzero");
            let zero = T::make_zero_coefficient_from_coefficient(Cow::Borrowed(&c));
            if (c < zero) != (retval < zero) {
                retval = zero - retval;
            }
            Some(retval)
        } else {
            None
        }
    }
    /// returns greatest common divisor of all coefficients
    pub fn content(&self) -> T
    where
        T: GCD<Output = T> + PartialOrd + Zero,
    {
        self.nonzero_content().unwrap_or_else(Zero::zero)
    }
    pub fn primitive_part_assign(&mut self)
    where
        T: GCD<Output = T> + PartialOrd + for<'a> ExactDiv<&'a T, Output = T>,
    {
        let content = match self.nonzero_content() {
            Some(v) => v,
            None => return,
        };
        self.exact_div_assign(content);
        debug_assert!(self
            .nonzero_highest_power_coefficient()
            .map(|v| v >= T::make_zero_coefficient_from_coefficient(Cow::Borrowed(&v)))
            .unwrap_or(true));
    }
    pub fn into_primitive_part(mut self) -> Self
    where
        T: GCD<Output = T> + PartialOrd + for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.primitive_part_assign();
        self
    }
    pub fn primitive_part(&self) -> Self
    where
        T: GCD<Output = T> + PartialOrd + for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.clone().into_primitive_part()
    }
    pub fn monic_assign(&mut self)
    where
        T: for<'a> ExactDiv<&'a T, Output = T>,
    {
        if let Some(v) = self.nonzero_highest_power_coefficient() {
            *self /= v;
        }
    }
    pub fn into_monic(mut self) -> Self
    where
        T: for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.monic_assign();
        self
    }
    /// returns the factor `f` of the passed in polynomial `p` where `p / f` is content-free (for integer polynomials) or monic (for polynomials over fields).
    pub fn nonzero_reducing_factor(&self) -> Option<T>
    where
        T: PolynomialReducingFactorSupported,
    {
        T::get_nonzero_reducing_factor(&self.elements, &self.divisor)
    }
    /// returns the factor `f` of the passed in polynomial `p` where `p / f` is content-free (for integer polynomials) or monic (for polynomials over fields).
    /// returns zero when `p` is zero.
    pub fn reducing_factor(&self) -> T
    where
        T: PolynomialReducingFactorSupported + Zero,
    {
        self.nonzero_reducing_factor().unwrap_or_else(T::zero)
    }
    /// converts `self` to be content-free (for integer polynomials) or monic (for polynomials over fields).
    pub fn reduce_assign(&mut self)
    where
        T: PolynomialReducingFactorSupported + for<'a> ExactDiv<&'a T, Output = T>,
    {
        if let Some(d) = self.nonzero_reducing_factor() {
            self.exact_div_assign(d);
        }
    }
    /// returns `self` converted to be content-free (for integer polynomials) or monic (for polynomials over fields).
    pub fn into_reduced(mut self) -> Self
    where
        T: PolynomialReducingFactorSupported + for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.reduce_assign();
        self
    }
    /// returns `self` converted to be content-free (for integer polynomials) or monic (for polynomials over fields).
    pub fn to_reduced(&self) -> Self
    where
        T: PolynomialReducingFactorSupported + for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.clone().into_reduced()
    }
    fn into_generic_sturm_sequence<R: Fn(&Self, &Self) -> Self, D: Fn(&Self) -> Self>(
        self,
        derivative: D,
        remainder: R,
    ) -> Vec<Polynomial<T>> {
        let self_len = self.len();
        match self_len {
            0 => return vec![],
            1 => return vec![self],
            _ => {}
        }
        let mut sturm_sequence = Vec::with_capacity(self_len);
        sturm_sequence.push(self);
        sturm_sequence.push(derivative(&sturm_sequence[0]));
        for _ in 2..self_len {
            match sturm_sequence.rchunks_exact(2).next() {
                Some([next_to_last, last]) => {
                    if last.is_zero() {
                        break;
                    } else {
                        let next = -remainder(next_to_last, last);
                        sturm_sequence.push(next);
                    }
                }
                _ => unreachable!(),
            }
        }
        sturm_sequence
    }
    pub fn to_sturm_sequence(&self) -> Vec<Polynomial<T>>
    where
        T: PolynomialDivSupported,
    {
        self.clone().into_sturm_sequence()
    }
    pub fn into_sturm_sequence(self) -> Vec<Polynomial<T>>
    where
        T: PolynomialDivSupported,
    {
        self.into_generic_sturm_sequence(Self::derivative, |a, b| a % b)
    }
    pub fn to_primitive_sturm_sequence(&self) -> Vec<Polynomial<T>>
    where
        T: GCD<Output = T> + PartialOrd + for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.clone().into_primitive_sturm_sequence()
    }
    pub fn into_primitive_sturm_sequence(self) -> Vec<Polynomial<T>>
    where
        T: GCD<Output = T> + PartialOrd + for<'a> ExactDiv<&'a T, Output = T>,
    {
        self.into_generic_sturm_sequence(
            |v| {
                let result = v.derivative();
                if let Some(content) = result.nonzero_content() {
                    if content < T::make_zero_coefficient_from_coefficient(Cow::Borrowed(&content))
                    {
                        result.exact_div(-content)
                    } else {
                        result.exact_div(content)
                    }
                } else {
                    result
                }
            },
            |a, b| {
                let PseudoDivRem {
                    remainder, factor, ..
                } = a.clone().pseudo_div_rem(b);
                if let Some(content) = remainder.nonzero_content() {
                    let zero = T::make_zero_coefficient_from_coefficient(Cow::Borrowed(&factor));
                    let content_is_negative = content < zero;
                    let mut result = remainder.exact_div(content);
                    if (factor < zero) != content_is_negative {
                        result = -result;
                    }
                    result
                } else {
                    // remainder is zero
                    remainder
                }
            },
        )
    }
    fn convert_to_derivative(&mut self) {
        if self.is_empty() {
            return;
        }
        self.elements.remove(0);
        for (index, element) in self.elements.iter_mut().enumerate() {
            T::mul_assign_element_by_usize(element, index + 1);
        }
        self.normalize();
    }
    pub fn into_derivative(mut self) -> Self {
        self.convert_to_derivative();
        self
    }
    pub fn derivative(&self) -> Self {
        if self.is_empty() {
            return self.clone();
        }
        let elements = self
            .elements
            .iter()
            .skip(1)
            .enumerate()
            .map(|(index, element)| T::mul_element_by_usize(Cow::Borrowed(element), index + 1))
            .collect();
        Self {
            elements,
            divisor: self.divisor.clone(),
        }
        .into_normalized()
    }
    fn eval_helper<
        V: for<'a> Mul<&'a V, Output = V> + Add<T, Output = V>,
        I: DoubleEndedIterator + Iterator<Item = T>,
    >(
        iter: I,
        at: &V,
        zero: V,
    ) -> V {
        let mut retval = zero;
        for coefficient in iter.rev() {
            retval = retval * at;
            retval = retval + coefficient;
        }
        retval
    }
    pub fn eval_generic<V: for<'a> Mul<&'a V, Output = V> + Add<T, Output = V>>(
        &self,
        at: &V,
        zero: V,
    ) -> V {
        Self::eval_helper(self.iter(), at, zero)
    }
    pub fn into_eval_generic<V: for<'a> Mul<&'a V, Output = V> + Add<T, Output = V>>(
        self,
        at: &V,
        zero: V,
    ) -> V {
        Self::eval_helper(self.into_iter(), at, zero)
    }
    pub fn eval(&self, at: &T) -> T {
        self.eval_generic(
            at,
            T::make_zero_coefficient_from_coefficient(Cow::Borrowed(at)),
        )
    }
    pub fn into_eval(self, at: &T) -> T {
        self.into_eval_generic(
            at,
            T::make_zero_coefficient_from_coefficient(Cow::Borrowed(at)),
        )
    }
    pub fn set_one_if_nonzero(&mut self) -> Result<(), ()> {
        if self.elements.is_empty() {
            Err(())
        } else {
            self.elements.drain(1..);
            self.divisor = One::one();
            T::set_element_one(&mut self.elements[0]);
            Ok(())
        }
    }
    pub fn into_one_if_nonzero(mut self) -> Result<Self, Self> {
        match self.set_one_if_nonzero() {
            Ok(()) => Ok(self),
            Err(()) => Err(self),
        }
    }
    #[must_use]
    pub fn to_one_if_nonzero(&self) -> Option<Self> {
        let first_element = self.elements.first()?;
        Some(Self {
            elements: vec![T::make_one_element(Cow::Borrowed(first_element))],
            divisor: One::one(),
        })
    }
    #[must_use]
    pub fn nonzero_max_norm(&self) -> Option<T>
    where
        T: Ord + PolynomialCoefficientAbsSupported,
    {
        self.iter().map(T::coefficient_abs).max()
    }
    #[must_use]
    pub fn max_norm(&self) -> T
    where
        T: Ord + PolynomialCoefficientAbsSupported + Zero,
    {
        self.nonzero_max_norm().unwrap_or_else(T::zero)
    }
    #[must_use]
    pub fn nonzero_manhattan_norm(&self) -> Option<T>
    where
        T: PolynomialCoefficientAbsSupported,
    {
        self.iter().fold(None, |sum, coefficient| match sum {
            None => Some(T::coefficient_abs(coefficient)),
            Some(sum) => Some(sum + T::coefficient_abs(coefficient)),
        })
    }
    #[must_use]
    pub fn manhattan_norm(&self) -> T
    where
        T: PolynomialCoefficientAbsSupported + Zero,
    {
        self.nonzero_manhattan_norm().unwrap_or_else(T::zero)
    }
}

#[derive(Clone, Eq, Hash, PartialEq, Debug)]
pub struct PolynomialFactor<T: PolynomialCoefficient> {
    pub polynomial: Polynomial<T>,
    pub power: usize,
}

impl<T: fmt::Display + PolynomialCoefficient> fmt::Display for PolynomialFactor<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})^{}", self.polynomial, self.power)
    }
}

#[derive(Clone, Eq, Hash, PartialEq, Debug)]
pub struct PolynomialFactors<T: PolynomialCoefficient> {
    pub constant_factor: T,
    // irreducible polynomials
    pub polynomial_factors: Vec<PolynomialFactor<T>>,
}

#[derive(Clone, Eq, Hash, PartialEq, Debug)]
pub struct SquareFreePolynomialFactors<T: PolynomialCoefficient> {
    pub constant_factor: T,
    // `polynomial_factors[n]` is raised to the power `n + 1` in the polynomial that was factored
    pub polynomial_factors: Vec<Polynomial<T>>,
}

impl<T> Polynomial<T>
where
    T: PolynomialDivSupported
        + RingCharacteristic<Type = CharacteristicZero>
        + PolynomialReducingFactorSupported
        + GCD<Output = T>
        + PartialOrd,
{
    /// splits `self` into square-free factors using Yun's algorithm
    ///
    /// Note that the returned factors are not necessarily irreducible.
    pub fn square_free_factorization_using_yuns_algorithm(&self) -> SquareFreePolynomialFactors<T> {
        #![allow(clippy::many_single_char_names)]
        if self.degree().unwrap_or(0) == 0 {
            return SquareFreePolynomialFactors {
                constant_factor: self
                    .nonzero_highest_power_coefficient()
                    .unwrap_or_else(Zero::zero),
                polynomial_factors: Vec::new(),
            };
        }
        // algorithm derived from https://en.wikipedia.org/wiki/Square-free_polynomial#Yun's_algorithm
        let content = self.content();
        let f = self / &content;
        let f_prime = f.derivative();
        let a0 = f.gcd(&f_prime).into_primitive_part();
        let mut b = f / &a0;
        let mut c = f_prime / &a0;
        let mut d = c - b.derivative();
        let mut a = Vec::new();
        loop {
            let a_i = b.gcd(&d).into_primitive_part();
            b /= &a_i;
            c = d / &a_i;
            d = c - b.derivative();
            a.push(a_i);
            debug_assert!(!b.is_zero());
            if b.len() == 1 {
                // b is just a constant; equivalent to 1
                break;
            }
        }
        SquareFreePolynomialFactors {
            constant_factor: content,
            polynomial_factors: a,
        }
    }
}

impl<T: PolynomialDivSupported + PolynomialReducingFactorSupported> Polynomial<T> {
    pub fn is_square_free(&self) -> bool {
        GCD::gcd(self, &self.derivative()).degree().unwrap_or(0) == 0
    }
}

impl<'a, T: PolynomialCoefficient> IntoIterator for &'a Polynomial<T> {
    type Item = T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub fn get_variable_name(nesting_depth: usize) -> Cow<'static, str> {
    const VARIABLE_CHARS: [&str; 26] = [
        "X", "Y", "Z", "A", "B", "C", "D", "E", "F", "G", "H", "I", "J", "K", "L", "M", "N", "O",
        "P", "Q", "R", "S", "T", "U", "V", "W",
    ];
    if nesting_depth < VARIABLE_CHARS.len() {
        Cow::Borrowed(VARIABLE_CHARS[nesting_depth])
    } else {
        Cow::Owned(
            get_variable_name(nesting_depth / VARIABLE_CHARS.len()).into_owned()
                + VARIABLE_CHARS[nesting_depth % VARIABLE_CHARS.len()],
        )
    }
}

impl<T: fmt::Display + PolynomialCoefficient> fmt::Display for Polynomial<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_empty() {
            write!(f, "0")
        } else {
            let variable_name = get_variable_name(T::NESTING_DEPTH);
            let left_paren = if T::NESTING_DEPTH != 0 { "(" } else { "" };
            let right_paren = if T::NESTING_DEPTH != 0 { ")" } else { "" };
            for (power, coefficient) in self.iter().enumerate() {
                match power {
                    0 => write!(f, "{}", coefficient)?,
                    1 => write!(
                        f,
                        " + {}{}{}*{}",
                        left_paren, coefficient, right_paren, variable_name
                    )?,
                    _ => write!(
                        f,
                        " + {}{}{}*{}^{}",
                        left_paren, coefficient, right_paren, variable_name, power
                    )?,
                }
            }
            Ok(())
        }
    }
}

macro_rules! impl_from_primitive_fn {
    ($f:ident, $t:ident) => {
        fn $f(v: $t) -> Option<Self> {
            Some(T::$f(v)?.into())
        }
    };
}

impl<T: PolynomialCoefficient + FromPrimitive> FromPrimitive for Polynomial<T> {
    impl_from_primitive_fn!(from_i8, i8);
    impl_from_primitive_fn!(from_u8, u8);
    impl_from_primitive_fn!(from_i16, i16);
    impl_from_primitive_fn!(from_u16, u16);
    impl_from_primitive_fn!(from_i32, i32);
    impl_from_primitive_fn!(from_u32, u32);
    impl_from_primitive_fn!(from_i64, i64);
    impl_from_primitive_fn!(from_u64, u64);
    impl_from_primitive_fn!(from_i128, i128);
    impl_from_primitive_fn!(from_u128, u128);
    impl_from_primitive_fn!(from_isize, isize);
    impl_from_primitive_fn!(from_usize, usize);
    impl_from_primitive_fn!(from_f32, f32);
    impl_from_primitive_fn!(from_f64, f64);
}

macro_rules! impl_to_primitive_fn {
    ($f:ident, $t:ident) => {
        fn $f(&self) -> Option<$t> {
            if self.len() > 1 {
                None
            } else if let Some(coefficient) = self.nonzero_coefficient(0) {
                Some(coefficient.$f()?)
            } else {
                Some($t::zero())
            }
        }
    };
}

impl<T: PolynomialCoefficient + ToPrimitive> ToPrimitive for Polynomial<T> {
    impl_to_primitive_fn!(to_i8, i8);
    impl_to_primitive_fn!(to_u8, u8);
    impl_to_primitive_fn!(to_i16, i16);
    impl_to_primitive_fn!(to_u16, u16);
    impl_to_primitive_fn!(to_i32, i32);
    impl_to_primitive_fn!(to_u32, u32);
    impl_to_primitive_fn!(to_i64, i64);
    impl_to_primitive_fn!(to_u64, u64);
    impl_to_primitive_fn!(to_i128, i128);
    impl_to_primitive_fn!(to_u128, u128);
    impl_to_primitive_fn!(to_isize, isize);
    impl_to_primitive_fn!(to_usize, usize);
    impl_to_primitive_fn!(to_f32, f32);
    impl_to_primitive_fn!(to_f64, f64);
}

#[derive(Copy, Clone, Debug)]
pub struct PolynomialIsZero;

impl fmt::Display for PolynomialIsZero {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "polynomial is zero")
    }
}

impl Error for PolynomialIsZero {}

impl From<PolynomialIsZero> for std::io::Error {
    fn from(err: PolynomialIsZero) -> Self {
        Self::new(std::io::ErrorKind::InvalidInput, err)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_eval() {
        let poly = Polynomial::from(vec![]);
        assert_eq!(poly.eval(&10), 0);
        let poly = Polynomial::from(vec![1]);
        assert_eq!(poly.eval(&10), 1);
        let poly = Polynomial::from(vec![1, 2]);
        assert_eq!(poly.eval(&10), 21);
        let poly = Polynomial::from(vec![1, 2, 3]);
        assert_eq!(poly.eval(&10), 321);
        let poly = Polynomial::from(vec![1, 2, 3, 4]);
        assert_eq!(poly.eval(&10), 4321);
    }

    #[test]
    fn test_display() {
        let mut poly = Polynomial::<i32>::from(vec![]);
        assert_eq!(format!("{}", poly), "0");
        poly = Polynomial::from(vec![1]);
        assert_eq!(format!("{}", poly), "1");
        poly = Polynomial::from(vec![1, 2]);
        assert_eq!(format!("{}", poly), "1 + 2*X");
        poly = Polynomial::from(vec![1, 2, 3]);
        assert_eq!(format!("{}", poly), "1 + 2*X + 3*X^2");
        poly = Polynomial::from(vec![1, 2, 3, 4]);
        assert_eq!(format!("{}", poly), "1 + 2*X + 3*X^2 + 4*X^3");
        let poly =
            Polynomial::<Polynomial<i32>>::from(vec![vec![1, 2, 3].into(), vec![4, 5, 6].into()]);
        assert_eq!(format!("{}", poly), "1 + 2*X + 3*X^2 + (4 + 5*X + 6*X^2)*Y");
        let poly: Polynomial<Polynomial<Polynomial<Polynomial<Polynomial<i32>>>>> = vec![
            Zero::zero(),
            Zero::zero(),
            vec![
                Zero::zero(),
                Zero::zero(),
                Zero::zero(),
                vec![
                    Zero::zero(),
                    Zero::zero(),
                    Zero::zero(),
                    Zero::zero(),
                    vec![
                        Zero::zero(),
                        Zero::zero(),
                        Zero::zero(),
                        Zero::zero(),
                        Zero::zero(),
                        vec![0, 0, 0, 0, 0, 0, 1].into(),
                    ]
                    .into(),
                ]
                .into(),
            ]
            .into(),
        ]
        .into();
        assert_eq!(format!("{}", poly), "0 + (0)*B + (0 + (0)*A + (0)*A^2 + (0 + (0)*Z + (0)*Z^2 + (0)*Z^3 + (0 + (0)*Y + (0)*Y^2 + (0)*Y^3 + (0)*Y^4 + (0 + 0*X + 0*X^2 + 0*X^3 + 0*X^4 + 0*X^5 + 1*X^6)*Y^5)*Z^4)*A^3)*B^2");
    }

    #[test]
    fn test_split_out_divisor() {
        let mut poly: Polynomial<Ratio<i32>> = (&[] as &[_]).into();
        assert_eq!(poly.split_out_divisor(), (vec![], 1));
        poly = From::<Vec<Ratio<_>>>::from(vec![
            (46, 205).into(),
            (43, 410).into(),
            (71, 410).into(),
            (62, 615).into(),
        ]);
        assert_eq!(poly.split_out_divisor(), (vec![276, 129, 213, 124], 1230));
        poly = From::<Vec<Ratio<_>>>::from(vec![(1, 2).into()]);
        assert_eq!(poly.split_out_divisor(), (vec![1], 2));
    }

    #[test]
    fn test_sturm_sequence() {
        let mut poly: Polynomial<Ratio<i64>> = Zero::zero();
        assert_eq!(Vec::<Polynomial<_>>::new(), poly.to_sturm_sequence());
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into()]);
        assert_eq!(vec![poly.clone()], poly.to_sturm_sequence());
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into(), 2.into()]);
        assert_eq!(
            vec![poly.clone(), From::<Vec<Ratio<_>>>::from(vec![2.into()])],
            poly.to_sturm_sequence()
        );
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(
            vec![
                poly.clone(),
                From::<Vec<Ratio<_>>>::from(vec![2.into(), 6.into()]),
                From::<Vec<Ratio<_>>>::from(vec![(-2, 3).into()]),
            ],
            poly.to_sturm_sequence()
        );
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into(), 2.into(), 3.into(), 4.into()]);
        assert_eq!(
            vec![
                poly.clone(),
                From::<Vec<Ratio<_>>>::from(vec![2.into(), 6.into(), 12.into()]),
                From::<Vec<Ratio<_>>>::from(vec![(-5, 6).into(), (-5, 6).into()]),
                From::<Vec<Ratio<_>>>::from(vec![(-8).into()]),
            ],
            poly.to_sturm_sequence()
        );
    }

    #[test]
    fn test_primitive_sturm_sequence() {
        let mut poly: Polynomial<i64> = Zero::zero();
        assert_eq!(
            Vec::<Polynomial<_>>::new(),
            poly.to_primitive_sturm_sequence()
        );
        poly = vec![1].into();
        assert_eq!(vec![poly.clone()], poly.to_primitive_sturm_sequence());
        poly = vec![1, 2].into();
        assert_eq!(
            vec![poly.clone(), vec![1].into()],
            poly.to_primitive_sturm_sequence()
        );
        poly = vec![1, 2, 3].into();
        assert_eq!(
            vec![poly.clone(), vec![1, 3].into(), vec![-1].into()],
            poly.to_primitive_sturm_sequence()
        );
        poly = vec![1, 2, 3, 4].into();
        assert_eq!(
            vec![
                poly.clone(),
                vec![1, 3, 6].into(),
                vec![-1, -1].into(),
                vec![-1].into(),
            ],
            poly.to_primitive_sturm_sequence()
        );
        poly = vec![-1].into();
        assert_eq!(vec![poly.clone()], poly.to_primitive_sturm_sequence());
        poly = vec![-1, -2].into();
        assert_eq!(
            vec![poly.clone(), vec![-1].into()],
            poly.to_primitive_sturm_sequence()
        );
        poly = vec![-1, -2, -3].into();
        assert_eq!(
            vec![poly.clone(), vec![-1, -3].into(), vec![1].into()],
            poly.to_primitive_sturm_sequence()
        );
        poly = vec![-1, -2, -3, -4].into();
        assert_eq!(
            vec![
                poly.clone(),
                vec![-1, -3, -6].into(),
                vec![1, 1].into(),
                vec![1].into(),
            ],
            poly.to_primitive_sturm_sequence()
        );
    }

    #[test]
    fn test_primitive_part() {
        assert_eq!(
            Polynomial::from(vec![0, 1, 2, 3, 4]).into_primitive_part(),
            Polynomial::from(vec![0, 1, 2, 3, 4])
        );
        assert_eq!(
            Polynomial::from(vec![2, 4, 6, 8]).into_primitive_part(),
            Polynomial::from(vec![1, 2, 3, 4])
        );
        assert_eq!(
            Polynomial::<i32>::zero().into_primitive_part(),
            Polynomial::zero()
        );
    }

    #[test]
    fn test_square_free_factorization_using_yuns_algorithm() {
        fn test(
            poly: Polynomial<Ratio<BigInt>>,
            expected_factorization: SquareFreePolynomialFactors<Ratio<BigInt>>,
        ) {
            println!("poly=({})", poly);
            let square_free_factorization = poly.square_free_factorization_using_yuns_algorithm();
            println!("square_free_factorization:");
            println!("    {}", square_free_factorization.constant_factor);
            for i in &square_free_factorization.polynomial_factors {
                println!("    {}", i);
            }
            println!("expected_factorization:");
            println!("    {}", expected_factorization.constant_factor);
            for i in &expected_factorization.polynomial_factors {
                println!("    {}", i);
            }
            assert!(expected_factorization == square_free_factorization);
        }
        fn ri(v: i128) -> Ratio<BigInt> {
            BigInt::from(v).into()
        }
        fn r(n: i128, d: i128) -> Ratio<BigInt> {
            Ratio::new(n.into(), d.into())
        }
        test(
            vec![
                ri(34560),
                ri(300_672),
                ri(1_195_632),
                ri(2_881_136),
                ri(4_703_032),
                ri(5_506_936),
                ri(4_777_591),
                ri(3_126_949),
                ri(1_556_776),
                ri(589_632),
                ri(168_542),
                ri(35714),
                ri(5432),
                ri(560),
                ri(35),
                ri(1),
            ]
            .into(),
            SquareFreePolynomialFactors {
                constant_factor: ri(1),
                polynomial_factors: vec![
                    vec![ri(5), ri(1)].into(),
                    vec![ri(4), ri(1)].into(),
                    vec![ri(3), ri(1)].into(),
                    vec![ri(2), ri(1)].into(),
                    vec![ri(1), ri(1)].into(),
                ],
            },
        );
        test(
            Zero::zero(),
            SquareFreePolynomialFactors {
                constant_factor: Zero::zero(),
                polynomial_factors: vec![],
            },
        );
        test(
            ri(123).into(),
            SquareFreePolynomialFactors {
                constant_factor: ri(123),
                polynomial_factors: vec![],
            },
        );
        test(
            vec![ri(64), ri(16), ri(1)].into(),
            SquareFreePolynomialFactors {
                constant_factor: One::one(),
                polynomial_factors: vec![One::one(), vec![ri(8), ri(1)].into()],
            },
        );
        test(
            vec![ri(18), ri(9), ri(1)].into(),
            SquareFreePolynomialFactors {
                constant_factor: One::one(),
                polynomial_factors: vec![vec![ri(18), ri(9), ri(1)].into()],
            },
        );
        test(
            vec![
                ri(944_784),
                ri(2_519_424),
                ri(2_991_816),
                ri(2_082_024),
                ri(939_681),
                ri(287_226),
                ri(60183),
                ri(8532),
                ri(783),
                ri(42),
                ri(1),
            ]
            .into(),
            SquareFreePolynomialFactors {
                constant_factor: One::one(),
                polynomial_factors: vec![
                    One::one(),
                    One::one(),
                    One::one(),
                    vec![ri(6), ri(1)].into(),
                    One::one(),
                    vec![ri(3), ri(1)].into(),
                ],
            },
        );
        test(
            vec![
                ri(10_850_253_750),
                ri(124_622_914_500),
                ri(629_487_927_900),
                ri(1_843_199_313_480),
                ri(3_475_162_941_066),
                ri(4_436_852_440_860),
                ri(3_932_734_882_824),
                ri(2_444_066_523_504),
                ri(1_063_358_633_322),
                ri(319_712_686_524),
                ri(64_563_363_036),
                ri(8_291_896_776),
                ri(606_905_622),
                ri(19_131_876),
            ]
            .into(),
            SquareFreePolynomialFactors {
                constant_factor: ri(1458),
                polynomial_factors: vec![
                    vec![ri(3), ri(2)].into(),
                    vec![ri(7), ri(8), ri(1)].into(),
                    One::one(),
                    vec![ri(15), ri(32), ri(9)].into(),
                ],
            },
        );
        test(
            vec![r(16, 5), r(16, 5), r(4, 5)].into(),
            SquareFreePolynomialFactors {
                constant_factor: r(4, 5),
                polynomial_factors: vec![ri(1).into(), vec![ri(2), ri(1)].into()],
            },
        );
        test(
            vec![
                ri(-81920),
                ri(-1_363_968),
                ri(-9_546_752),
                ri(-36_935_424),
                ri(-87_467_264),
                ri(-132_423_552),
                ri(-129_747_904),
                ri(-81_302_256),
                ri(-31_291_792),
                ri(-6_717_312),
                ri(-614_656),
            ]
            .into(),
            SquareFreePolynomialFactors {
                constant_factor: ri(-16),
                polynomial_factors: vec![
                    vec![ri(5), ri(7)].into(),
                    vec![ri(1), ri(4)].into(),
                    vec![ri(4), ri(7)].into(),
                    vec![ri(2), ri(1)].into(),
                ],
            },
        );
    }

    #[test]
    fn test_make_monomial() {
        assert_eq!(
            Polynomial::from(vec![0, 0, 123]),
            Polynomial::make_monomial(123, 2)
        );
        assert_eq!(
            Polynomial::from(vec![123]),
            Polynomial::make_monomial(123, 0)
        );
        assert_eq!(Polynomial::zero(), Polynomial::make_monomial(0, 5));
    }
}
