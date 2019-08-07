// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::traits::ExtendedGCD;
use crate::traits::ExtendedGCDAndLCM;
use crate::traits::GCDAndLCM;
use crate::traits::GCD;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::One;
use num_traits::{zero, Zero};
use num_traits::{FromPrimitive, ToPrimitive};
use std::borrow::Cow;
use std::error::Error;
use std::fmt;
use std::hash;
use std::mem;
use std::ops::Deref;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Neg;
use std::ops::RemAssign;
use std::ops::{Add, AddAssign, Mul, MulAssign, Sub, SubAssign};
use std::slice;
use std::vec;

mod ops;

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
    + One
    + FromPrimitive
    + GCD<Self, Output = Self>
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
            + for<'a> MulAssign<&'a Self>
            + One
            + FromPrimitive
            + GCD<Self, Output = Self>,
    > PolynomialCoefficientElement for T
{
}

pub trait PolynomialCoefficient:
    Clone
    + Eq
    + fmt::Debug
    + hash::Hash
    + Zero
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
    + One
    + FromPrimitive
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
        + Div<Output = Self::Divisor>
        + DivAssign
        + for<'a> Div<&'a Self::Divisor, Output = Self::Divisor>
        + for<'a> DivAssign<&'a Self::Divisor>
        + GCD<Output = Self::Divisor>
        + One;
    fn divisor_to_element(v: Cow<Self::Divisor>) -> Self::Element;
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
}

impl<
        T: PolynomialCoefficientElement
            + Integer
            + for<'a> DivAssign<&'a T>
            + for<'a> Div<&'a T, Output = T>
            + DivAssign
            + RemAssign,
    > PolynomialCoefficient for Ratio<T>
where
    Ratio<T>: FromPrimitive,
{
    type Element = T;
    type Divisor = T;
    fn divisor_to_element(v: Cow<Self::Divisor>) -> Self::Element {
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
        elements.iter_mut().for_each(|element| *element /= &gcd);
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
            .map(|element| {
                let mut element = element.clone();
                element /= &gcd;
                element
            })
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

impl DivAssign for DivisorIsOne {
    fn div_assign(&mut self, _rhs: DivisorIsOne) {}
}

impl DivAssign<&DivisorIsOne> for DivisorIsOne {
    fn div_assign(&mut self, _rhs: &DivisorIsOne) {}
}

impl Div for DivisorIsOne {
    type Output = DivisorIsOne;
    fn div(self, _rhs: DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl Div<&DivisorIsOne> for DivisorIsOne {
    type Output = DivisorIsOne;
    fn div(self, _rhs: &DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl Div<DivisorIsOne> for &DivisorIsOne {
    type Output = DivisorIsOne;
    fn div(self, _rhs: DivisorIsOne) -> DivisorIsOne {
        DivisorIsOne
    }
}

impl<'a, 'b> Div<&'a DivisorIsOne> for &'b DivisorIsOne {
    type Output = DivisorIsOne;
    fn div(self, _rhs: &DivisorIsOne) -> DivisorIsOne {
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
            fn divisor_to_element(_v: Cow<Self::Divisor>) -> Self::Element {
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

pub trait PolynomialDivSupported:
    PolynomialCoefficient<Divisor = <Self as PolynomialCoefficient>::Element>
    + for<'a> DivAssign<&'a Self>
    + DivAssign
    + for<'a> Div<&'a Self, Output = Self>
    + Div<Output = Self>
where
    Self::Element: Div<Output = Self::Element> + DivAssign,
    for<'a> Self::Element:
        Div<&'a Self::Element, Output = Self::Element> + DivAssign<&'a Self::Element>,
{
}

impl<
        T: PolynomialCoefficientElement
            + Integer
            + for<'a> Div<&'a T, Output = T>
            + for<'a> DivAssign<&'a T>
            + DivAssign
            + RemAssign,
    > PolynomialDivSupported for Ratio<T>
where
    Ratio<T>: FromPrimitive,
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

impl<T: PolynomialCoefficient + GCD<Output = T> + PolynomialDivSupported> GCD for Polynomial<T>
where
    for<'a> T::Element: DivAssign<&'a T::Element> + Div<&'a T::Element, Output = T::Element>,
    T::Element: DivAssign + Div<Output = T::Element>,
{
    type Output = Self;
    fn gcd_lcm(&self, rhs: &Self) -> GCDAndLCM<Self> {
        let ExtendedGCDAndLCM { gcd, lcm, .. } = self.extended_gcd_lcm(rhs);
        GCDAndLCM { gcd, lcm }
    }
}

impl<T: PolynomialCoefficient + GCD<Output = T> + PolynomialDivSupported> ExtendedGCD
    for Polynomial<T>
where
    for<'a> T::Element: DivAssign<&'a T::Element> + Div<&'a T::Element, Output = T::Element>,
    T::Element: DivAssign + Div<Output = T::Element>,
{
    fn extended_gcd_lcm(&self, _rhs: &Self) -> ExtendedGCDAndLCM<Self> {
        // FIXME: finish
        unimplemented!()
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
                    if !last.is_zero() {
                        break;
                    }
                    *coefficients = rest;
                }
            }
            Cow::Owned(coefficients) => {
                while let Some(last) = coefficients.last() {
                    if !last.is_zero() {
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

impl<T: PolynomialCoefficient> From<&'_ [T]> for Polynomial<T> {
    fn from(coefficients: &[T]) -> Self {
        Self::from(Cow::Borrowed(coefficients))
    }
}

impl<T: PolynomialCoefficient> From<T> for Polynomial<T> {
    fn from(coefficient: T) -> Self {
        if coefficient.is_zero() {
            Zero::zero()
        } else {
            let (element, divisor) = T::coefficient_to_element(Cow::Owned(coefficient));
            Self {
                elements: vec![element],
                divisor,
            }
        }
    }
}

impl<T: PolynomialCoefficient> From<&T> for Polynomial<T> {
    fn from(coefficient: &T) -> Self {
        if coefficient.is_zero() {
            Zero::zero()
        } else {
            let (element, divisor) = T::coefficient_to_element(Cow::Borrowed(coefficient));
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
}

impl<T: PolynomialCoefficient> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<T> {
        Some(T::make_coefficient(
            Cow::Borrowed(self.elements.next_back()?),
            Cow::Borrowed(self.divisor),
        ))
    }
}

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
    pub fn coefficient(&self, index: usize) -> T {
        T::make_coefficient(
            Cow::Borrowed(&self.elements[index]),
            Cow::Borrowed(&self.divisor),
        )
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
    fn normalize(&mut self) {
        while let Some(last) = self.elements.last() {
            if !last.is_zero() {
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
        for element in &mut self.elements {
            *element = -mem::replace(element, Zero::zero());
        }
    }
    /// returns greatest common divisor of all coefficients
    pub fn content(&self) -> T
    where
        T: GCD<Output = T>,
    {
        self.iter()
            .fold(None, |lhs: Option<T>, rhs| match lhs {
                None => Some(rhs.clone()),
                Some(lhs) => Some(lhs.gcd(&rhs)),
            })
            .unwrap_or_else(zero)
    }
    pub fn to_sturm_sequence(&self) -> SturmSequence<T>
    where
        T: PolynomialDivSupported,
        for<'a> T::Element: DivAssign<&'a T::Element> + Div<&'a T::Element, Output = T::Element>,
        T::Element: DivAssign + Div<Output = T::Element>,
    {
        self.clone().into_sturm_sequence()
    }
    pub fn into_sturm_sequence(self) -> SturmSequence<T>
    where
        T: PolynomialDivSupported,
        for<'a> T::Element: DivAssign<&'a T::Element> + Div<&'a T::Element, Output = T::Element>,
        T::Element: DivAssign + Div<Output = T::Element>,
    {
        let self_len = self.len();
        match self_len {
            0 => return SturmSequence(vec![]),
            1 => return SturmSequence(vec![self.clone()]),
            _ => {}
        }
        let mut sturm_sequence = Vec::with_capacity(self_len);
        sturm_sequence.push(self);
        sturm_sequence.push(sturm_sequence[0].derivative());
        for _ in 2..self_len {
            match sturm_sequence.rchunks_exact(2).next() {
                Some([next_to_last, last]) => {
                    if last.is_zero() {
                        break;
                    } else {
                        let next = -(next_to_last % last);
                        sturm_sequence.push(next);
                    }
                }
                _ => unreachable!(),
            }
        }
        SturmSequence(sturm_sequence)
    }
    pub fn reduce_multiple_roots(&mut self)
    where
        T: PolynomialDivSupported + GCD<Output = T>,
        for<'a> T::Element: DivAssign<&'a T::Element> + Div<&'a T::Element, Output = T::Element>,
        T::Element: DivAssign + Div<Output = T::Element>,
    {
        let derivative = self.derivative();
        *self /= self.gcd(&derivative);
    }
    fn convert_to_derivative(&mut self) {
        if self.is_empty() {
            return;
        }
        self.elements.remove(0);
        for (index, element) in self.elements.iter_mut().enumerate() {
            let index = T::Element::from_usize(index + 1).expect("converting from usize failed");
            MulAssign::<T::Element>::mul_assign(element, index);
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
            .map(|(index, element)| {
                T::Element::from_usize(index + 1).expect("converting from usize failed") * element
            })
            .collect();
        Self {
            elements,
            divisor: self.divisor.clone(),
        }
        .into_normalized()
    }
    fn eval_helper<I: DoubleEndedIterator + Iterator<Item = T>>(iter: I, at: &T) -> T {
        let mut iter = iter.rev();
        if let Some(last) = iter.next() {
            let mut retval = last;
            for coefficient in iter {
                retval *= at;
                retval += coefficient;
            }
            retval
        } else {
            Zero::zero()
        }
    }
    pub fn eval(&self, at: &T) -> T {
        Self::eval_helper(self.iter(), at)
    }
    pub fn into_eval(self, at: &T) -> T {
        Self::eval_helper(self.into_iter(), at)
    }
}

impl<'a, T: PolynomialCoefficient> IntoIterator for &'a Polynomial<T> {
    type Item = T;
    type IntoIter = Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: fmt::Display + PolynomialCoefficient> fmt::Display for Polynomial<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_empty() {
            write!(f, "0")
        } else {
            for (power, coefficient) in self.iter().enumerate() {
                match power {
                    0 => write!(f, "{}", coefficient)?,
                    1 => write!(f, " + {}*x", coefficient)?,
                    _ => write!(f, " + {}*x^{}", coefficient, power)?,
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

impl<T: PolynomialCoefficient> FromPrimitive for Polynomial<T> {
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
            if self.is_zero() {
                Some(Zero::zero())
            } else if self.len() == 1 {
                Some(self.coefficient(0).$f()?)
            } else {
                None
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

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct SturmSequence<T: PolynomialCoefficient>(Vec<Polynomial<T>>);

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

impl<T: PolynomialDivSupported> SturmSequence<T>
where
    for<'a> T::Element: DivAssign<&'a T::Element> + Div<&'a T::Element, Output = T::Element>,
    T::Element: DivAssign + Div<Output = T::Element>,
{
    pub fn new(polynomial: Polynomial<T>) -> Self {
        polynomial.into_sturm_sequence()
    }
}

impl<T: PolynomialCoefficient> Deref for SturmSequence<T> {
    type Target = [Polynomial<T>];
    fn deref(&self) -> &[Polynomial<T>] {
        &self.0
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
        assert_eq!(format!("{}", poly), "1 + 2*x");
        poly = Polynomial::from(vec![1, 2, 3]);
        assert_eq!(format!("{}", poly), "1 + 2*x + 3*x^2");
        poly = Polynomial::from(vec![1, 2, 3, 4]);
        assert_eq!(format!("{}", poly), "1 + 2*x + 3*x^2 + 4*x^3");
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
        assert_eq!(*Vec::<Polynomial<_>>::new(), *poly.to_sturm_sequence());
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into()]);
        assert_eq!([poly.clone()], *poly.to_sturm_sequence());
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into(), 2.into()]);
        assert_eq!(
            [poly.clone(), From::<Vec<Ratio<_>>>::from(vec![2.into()])],
            *poly.to_sturm_sequence()
        );
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into(), 2.into(), 3.into()]);
        assert_eq!(
            [
                poly.clone(),
                From::<Vec<Ratio<_>>>::from(vec![2.into(), 6.into()]),
                From::<Vec<Ratio<_>>>::from(vec![(-2, 3).into()]),
            ],
            *poly.to_sturm_sequence()
        );
        poly = From::<Vec<Ratio<_>>>::from(vec![1.into(), 2.into(), 3.into(), 4.into()]);
        assert_eq!(
            [
                poly.clone(),
                From::<Vec<Ratio<_>>>::from(vec![2.into(), 6.into(), 12.into()]),
                From::<Vec<Ratio<_>>>::from(vec![(-5, 6).into(), (-5, 6).into()]),
                From::<Vec<Ratio<_>>>::from(vec![(-8).into()]),
            ],
            *poly.to_sturm_sequence()
        );
    }
}
