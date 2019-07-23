// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::prelude::*;
use crate::traits::MakeCoefficient;
use crate::util::Sign;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::One;
use num_traits::{zero, Zero};
use std::borrow::Cow;
use std::error::Error;
use std::fmt;
use std::ops::Deref;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::{AddAssign, Mul, MulAssign};
use std::slice;
use std::vec;

mod ops;

/// A single-variable polynomial.
///
/// the term at index `n` is `self.coefficients()[n] * pow(x, n)`
///
/// # Invariants
///
/// `self.coefficients().last()` is either `None` or `Some(v)` where `!v.is_zero()`
#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct Polynomial<T> {
    coefficients: Vec<T>,
}

impl<T: GCD> GCD for Polynomial<T> {
    type Output = Self;
    fn gcd(&self, _rhs: &Self) -> Self {
        // FIXME: finish
        unimplemented!()
    }
}

impl<T> Default for Polynomial<T> {
    fn default() -> Self {
        Self {
            coefficients: Vec::default(),
        }
    }
}

impl<T: Zero> From<Vec<T>> for Polynomial<T> {
    fn from(coefficients: Vec<T>) -> Self {
        let mut retval = Self { coefficients };
        retval.remove_extra_zeros();
        retval
    }
}

impl<T: Zero + Clone + Integer> From<Vec<T>> for Polynomial<Ratio<T>> {
    fn from(coefficients: Vec<T>) -> Self {
        let coefficients = coefficients.into_iter().map(Into::into).collect();
        let mut retval = Self { coefficients };
        retval.remove_extra_zeros();
        retval
    }
}

impl<T: Zero + Clone + Integer> From<Polynomial<T>> for Polynomial<Ratio<T>> {
    fn from(src: Polynomial<T>) -> Self {
        let coefficients = src.into_iter().map(Into::into).collect();
        Self { coefficients }
    }
}

impl<T> Polynomial<T> {
    pub fn coefficients(&self) -> &Vec<T> {
        &self.coefficients
    }
    pub fn into_coefficients(self) -> Vec<T> {
        self.coefficients
    }
    pub fn iter(&self) -> slice::Iter<T> {
        self.coefficients.iter()
    }
    pub fn iter_mut(&mut self) -> slice::IterMut<T> {
        self.coefficients.iter_mut()
    }
    pub fn len(&self) -> usize {
        self.coefficients.len()
    }
    pub fn is_empty(&self) -> bool {
        self.coefficients.is_empty()
    }
    fn remove_extra_zeros(&mut self)
    where
        T: Zero,
    {
        while let Some(tail) = self.coefficients.last() {
            if tail.is_zero() {
                self.coefficients.pop();
            } else {
                break;
            }
        }
    }
    /// returns greatest common divisor of all coefficients
    pub fn content(&self) -> T
    where
        T: GCD<Output = T> + Zero + Clone,
    {
        self.iter()
            .fold(None, |lhs: Option<T>, rhs| match lhs {
                None => Some(rhs.clone()),
                Some(lhs) => Some(lhs.gcd(rhs)),
            })
            .unwrap_or_else(zero)
    }
    pub fn sign_at_infinity(&self, input_sign: Sign) -> Option<Sign>
    where
        T: PartialOrd + Zero,
    {
        let sign_last = Sign::new(self.coefficients.last()?)?;
        if self.len() % 2 != 0 && input_sign == Sign::Negative {
            Some(-sign_last)
        } else {
            Some(sign_last)
        }
    }
    pub fn to_sturm_sequence(&self) -> SturmSequence<T>
    where
        T: Clone + Zero + AddAssign + Neg<Output = T>,
        for<'a> &'a Polynomial<T>: Rem<Output = Polynomial<T>> + Derivative<Output = Polynomial<T>>,
    {
        self.clone().into_sturm_sequence()
    }
    pub fn into_sturm_sequence(self) -> SturmSequence<T>
    where
        T: Clone + Zero + AddAssign + Neg<Output = T>,
        for<'a> &'a Polynomial<T>: Rem<Output = Polynomial<T>> + Derivative<Output = Polynomial<T>>,
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
}

impl<T: Clone + Integer + AddAssign + One + for<'a> Mul<&'a T, Output = T>> Polynomial<Ratio<T>> {
    pub fn split_out_denominator(self) -> (Polynomial<T>, T) {
        let lcm = self.iter().fold(None, |a: Option<Cow<T>>, b: &Ratio<T>| {
            Some(match a {
                None => Cow::Borrowed(b.denom()),
                Some(a) => Cow::Owned(a.lcm(b.denom())),
            })
        });
        let lcm = match lcm {
            None => return (Zero::zero(), One::one()),
            Some(lcm) => lcm.into_owned(),
        };
        let coefficients: Vec<_> = self
            .into_iter()
            .map(|v| {
                let (numer, denom) = v.into();
                numer * &lcm / denom
            })
            .collect();
        (coefficients.into(), lcm)
    }
}

impl<T> PolynomialEval<T> for Polynomial<T>
where
    T: Zero + AddAssign,
    for<'a> T: MulAssign<&'a T>,
{
    fn eval(self, x: &T) -> T {
        let mut iter = self.into_iter().rev();
        if let Some(last) = iter.next() {
            let mut retval = last;
            for coefficient in iter {
                retval *= x;
                retval += coefficient;
            }
            retval
        } else {
            zero()
        }
    }
}

impl<'a, T> PolynomialEval<T> for &'a Polynomial<T>
where
    T: Zero + AddAssign<&'a T> + Clone,
    for<'b> T: MulAssign<&'b T>,
{
    fn eval(self, x: &T) -> T {
        let mut iter = self.iter().rev();
        if let Some(last) = iter.next() {
            let mut retval = last.clone();
            for coefficient in iter {
                retval *= x;
                retval += coefficient;
            }
            retval
        } else {
            zero()
        }
    }
}

impl<'a, T> PolynomialEval<Ratio<T>> for &'a Polynomial<T>
where
    for<'b> Ratio<T>: MulAssign<&'b Ratio<T>> + AddAssign<&'b T>,
    T: Clone + Into<Ratio<T>>,
    Ratio<T>: Zero,
{
    fn eval(self, x: &Ratio<T>) -> Ratio<T> {
        let mut iter = self.iter().rev();
        if let Some(last) = iter.next() {
            let mut retval = last.clone().into();
            for coefficient in iter {
                retval *= x;
                retval += coefficient;
            }
            retval
        } else {
            zero()
        }
    }
}

impl<T> PolynomialEval<Ratio<T>> for Polynomial<T>
where
    for<'b> Ratio<T>: MulAssign<&'b Ratio<T>>,
    T: Clone + Into<Ratio<T>>,
    Ratio<T>: Zero + AddAssign<T>,
{
    fn eval(self, x: &Ratio<T>) -> Ratio<T> {
        let mut iter = self.into_iter().rev();
        if let Some(last) = iter.next() {
            let mut retval = last.clone().into();
            for coefficient in iter {
                retval *= x;
                retval += coefficient;
            }
            retval
        } else {
            zero()
        }
    }
}

impl<'a, T, U> PolynomialEval<U> for &'a mut Polynomial<T>
where
    &'a Polynomial<T>: PolynomialEval<U>,
{
    fn eval(self, x: &U) -> U {
        PolynomialEval::eval(&*self, x)
    }
}

impl<T> IntoIterator for Polynomial<T> {
    type Item = T;
    type IntoIter = vec::IntoIter<T>;
    fn into_iter(self) -> Self::IntoIter {
        self.coefficients.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Polynomial<T> {
    type Item = &'a T;
    type IntoIter = slice::Iter<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Polynomial<T> {
    type Item = &'a mut T;
    type IntoIter = slice::IterMut<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T: fmt::Display> fmt::Display for Polynomial<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.coefficients.is_empty() {
            write!(f, "0")
        } else {
            for (power, coefficient) in self.coefficients.iter().enumerate() {
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

impl<T> Derivative for Polynomial<T>
where
    T: Mul<Output = T> + MakeCoefficient<usize>,
    T: Zero,
{
    type Output = Self;
    fn derivative(self) -> Self {
        let mut iter = self.into_iter().enumerate();
        if iter.next().is_none() {
            return Default::default();
        }
        Polynomial::from(
            iter.map(|(power, coefficient)| coefficient * MakeCoefficient::make_coefficient(power))
                .collect::<Vec<T>>(),
        )
    }
}

impl<'a, T> Derivative for &'a Polynomial<T>
where
    &'a T: Mul<T, Output = T>,
    T: Zero + MakeCoefficient<usize>,
{
    type Output = Polynomial<T>;
    fn derivative(self) -> Polynomial<T> {
        let mut iter = self.iter().enumerate();
        if iter.next().is_none() {
            return Default::default();
        }
        Polynomial::from(
            iter.map(|(power, coefficient)| coefficient * MakeCoefficient::make_coefficient(power))
                .collect::<Vec<T>>(),
        )
    }
}

impl<'a, T> Derivative for &'a mut Polynomial<T>
where
    &'a Polynomial<T>: Derivative,
{
    type Output = <&'a Polynomial<T> as Derivative>::Output;
    fn derivative(self) -> Self::Output {
        (self as &Polynomial<T>).derivative()
    }
}

#[derive(Clone, PartialEq, Eq, Debug, Hash)]
pub struct SturmSequence<T>(Vec<Polynomial<T>>);

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

impl<T> SturmSequence<T> {
    pub fn new(polynomial: Polynomial<T>) -> Self
    where
        T: Clone + Zero + AddAssign + Neg<Output = T> + MakeCoefficient<usize>,
        for<'a> &'a T: Mul<T, Output = T>,
        for<'a> &'a Polynomial<T>: Rem<Output = Polynomial<T>>,
    {
        polynomial.into_sturm_sequence()
    }
    #[allow(dead_code)]
    fn count_sign_changes<EvalFn: FnMut(&Polynomial<T>) -> Option<Sign>>(
        &self,
        eval_fn: EvalFn,
    ) -> usize {
        let _ = eval_fn;
        unimplemented!()
    }
    pub fn distinct_real_root_count(&self) -> Result<usize, PolynomialIsZero> {
        if self.is_empty() {
            return Err(PolynomialIsZero);
        }
        unimplemented!()
    }
}

impl<T> Deref for SturmSequence<T> {
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
    fn test_split_out_denominator() {
        let mut poly: Polynomial<Ratio<i32>> = Zero::zero();
        assert_eq!(poly.split_out_denominator(), (vec![].into(), 1));
        poly = From::<Vec<Ratio<_>>>::from(vec![
            (46, 205).into(),
            (43, 410).into(),
            (71, 410).into(),
            (62, 615).into(),
        ]);
        assert_eq!(
            poly.split_out_denominator(),
            (vec![276, 129, 213, 124].into(), 1230)
        );
        poly = From::<Vec<Ratio<_>>>::from(vec![(1, 2).into()]);
        assert_eq!(poly.split_out_denominator(), (vec![1].into(), 2));
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
