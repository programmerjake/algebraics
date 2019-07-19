// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::prelude::*;
use num_rational::Ratio;
use num_traits::{zero, Zero};
use std::fmt::{self, Display, Formatter};
use std::ops::{AddAssign, Mul, MulAssign};
use std::slice;
use std::vec;

mod ops;

#[derive(Clone, PartialEq, Eq, Debug)]
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

impl<T: Display> Display for Polynomial<T> {
    fn fmt(&self, f: &mut Formatter) -> fmt::Result {
        if self.coefficients.is_empty() {
            write!(f, "<empty polynomial>")
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

impl<T, O> Derivative<Polynomial<O>> for Polynomial<T>
where
    T: Mul<usize, Output = O>,
    O: Zero,
{
    fn derivative(self) -> Polynomial<O> {
        let mut iter = self.into_iter().enumerate();
        if iter.next().is_none() {
            return Default::default();
        }
        Polynomial::from(
            iter.map(|(power, coefficient)| coefficient * power)
                .collect::<Vec<O>>(),
        )
    }
}

impl<'a, T, O> Derivative<Polynomial<O>> for &'a Polynomial<T>
where
    &'a T: Mul<usize, Output = O>,
    O: Zero,
{
    fn derivative(self) -> Polynomial<O> {
        let mut iter = self.iter().enumerate();
        if iter.next().is_none() {
            return Default::default();
        }
        Polynomial::from(
            iter.map(|(power, coefficient)| coefficient * power)
                .collect::<Vec<O>>(),
        )
    }
}

impl<'a, T, O> Derivative<Polynomial<O>> for &'a mut Polynomial<T>
where
    &'a Polynomial<T>: Derivative<Polynomial<O>>,
{
    fn derivative(self) -> Polynomial<O> {
        (self as &Polynomial<T>).derivative()
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
        let poly = Polynomial::<i32>::from(vec![]);
        assert_eq!(format!("{}", poly), "<empty polynomial>");
        let poly = Polynomial::from(vec![1]);
        assert_eq!(format!("{}", poly), "1");
        let poly = Polynomial::from(vec![1, 2]);
        assert_eq!(format!("{}", poly), "1 + 2*x");
        let poly = Polynomial::from(vec![1, 2, 3]);
        assert_eq!(format!("{}", poly), "1 + 2*x + 3*x^2");
        let poly = Polynomial::from(vec![1, 2, 3, 4]);
        assert_eq!(format!("{}", poly), "1 + 2*x + 3*x^2 + 4*x^3");
    }

}
