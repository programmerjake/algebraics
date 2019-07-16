use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{zero, Zero};
use std::fmt::{self, Display, Formatter};
use std::mem;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;
use std::ops::{Add, AddAssign, Mul, MulAssign};
use std::slice;
use std::vec;

pub trait GCD<Rhs = Self> {
    type Output;
    fn gcd(&self, rhs: &Rhs) -> Self::Output;
}

impl<T: Integer> GCD for T {
    type Output = T;
    fn gcd(&self, rhs: &T) -> T {
        Integer::gcd(self, rhs)
    }
}

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

pub trait PolynomialEval<T> {
    fn eval(self, x: &T) -> T;
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

pub trait Derivative<Output = Self> {
    fn derivative(self) -> Output;
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

fn pairwise_op_ref_ref<
    'l,
    'r,
    L,
    R,
    O: Zero,
    Op: FnMut(&'l L, &'r R) -> O,
    OpL: FnMut(&'l L) -> O,
    OpR: FnMut(&'r R) -> O,
>(
    l: &'l Polynomial<L>,
    r: &'r Polynomial<R>,
    mut op: Op,
    mut op_l: OpL,
    mut op_r: OpR,
) -> Polynomial<O> {
    let mut coefficients = Vec::with_capacity(l.len().max(r.len()));
    let mut l_iter = l.iter();
    let mut r_iter = r.iter();
    loop {
        match (l_iter.next(), r_iter.next()) {
            (Some(l), Some(r)) => coefficients.push(op(l, r)),
            (Some(l), None) => coefficients.push(op_l(l)),
            (None, Some(r)) => coefficients.push(op_r(r)),
            (None, None) => break,
        }
    }
    coefficients.into()
}

fn pairwise_op_eq_move<L: Zero, R, Op: FnMut(&mut L, R), OpL: FnMut(&mut L), OpR: FnMut(R) -> L>(
    l: &mut Polynomial<L>,
    r: Polynomial<R>,
    mut op: Op,
    mut op_l: OpL,
    op_r: OpR,
) {
    let mut r_iter = r.into_iter();
    for l in l.coefficients.iter_mut() {
        match r_iter.next() {
            Some(r) => op(l, r),
            None => op_l(l),
        }
    }
    l.coefficients.extend(r_iter.map(op_r));
    l.remove_extra_zeros()
}

fn pairwise_op_eq_ref<
    'r,
    L: Zero,
    R,
    Op: FnMut(&mut L, &'r R),
    OpL: FnMut(&mut L),
    OpR: FnMut(&'r R) -> L,
>(
    l: &mut Polynomial<L>,
    r: &'r Polynomial<R>,
    mut op: Op,
    mut op_l: OpL,
    op_r: OpR,
) {
    let mut r_iter = r.into_iter();
    for l in l.iter_mut() {
        match r_iter.next() {
            Some(r) => op(l, r),
            None => op_l(l),
        }
    }
    l.coefficients.extend(r_iter.map(op_r));
    l.remove_extra_zeros()
}

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
                let r_value = mem::replace(r, temp.take().unwrap_or_else(zero));
                temp = Some(mem::replace(r, l - r_value));
            },
            |r| {
                let r_value = mem::replace(r, temp2.take().unwrap_or_else(zero));
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

impl<'a, T: Zero + AddAssign> Mul for &'a Polynomial<T>
where
    &'a T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    #[allow(clippy::suspicious_arithmetic_impl)]
    fn mul(self, rhs: &'a Polynomial<T>) -> Polynomial<T> {
        if self.is_zero() || rhs.is_zero() {
            return zero();
        }
        let mut retval_coefficients = Vec::with_capacity(self.len() + rhs.len());
        for l_index in 0..self.len() {
            if self.coefficients[l_index].is_zero() {
                continue;
            }
            for r_index in 0..rhs.len() {
                let index = l_index + r_index;
                if index == retval_coefficients.len() {
                    retval_coefficients
                        .push(&self.coefficients[l_index] * &rhs.coefficients[r_index]);
                } else {
                    retval_coefficients[index] +=
                        &self.coefficients[l_index] * &rhs.coefficients[r_index];
                }
            }
        }
        retval_coefficients.into()
    }
}

impl<'a, T: Zero + AddAssign> Mul<Polynomial<T>> for &'a Polynomial<T>
where
    for<'b> &'b T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    fn mul(self, rhs: Polynomial<T>) -> Polynomial<T> {
        self * &rhs
    }
}

impl<'a, T: Zero + AddAssign> Mul<&'a Polynomial<T>> for Polynomial<T>
where
    for<'b> &'b T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    fn mul(self, rhs: &'a Polynomial<T>) -> Polynomial<T> {
        &self * rhs
    }
}

impl<T: Zero + AddAssign> Mul for Polynomial<T>
where
    for<'a> &'a T: Mul<Output = T>,
{
    type Output = Polynomial<T>;
    fn mul(self, rhs: Polynomial<T>) -> Polynomial<T> {
        &self * &rhs
    }
}

impl<T: Zero + AddAssign> MulAssign for Polynomial<T>
where
    for<'a> &'a T: Mul<Output = T>,
{
    fn mul_assign(&mut self, rhs: Polynomial<T>) {
        *self = &*self * rhs;
    }
}

impl<'a, T: Zero + AddAssign> MulAssign<&'a Polynomial<T>> for Polynomial<T>
where
    for<'b> &'b T: Mul<Output = T>,
{
    fn mul_assign(&mut self, rhs: &'a Polynomial<T>) {
        *self = &*self * rhs;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fmt::Debug;

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

    #[allow(clippy::too_many_arguments)]
    fn test_op_helper<
        T: Clone + PartialEq + Debug,
        OpEqMove: Fn(&mut T, T),
        OpEqRef: Fn(&mut T, &T),
        OpRefRef: Fn(&T, &T) -> T,
        OpMoveRef: Fn(T, &T) -> T,
        OpRefMove: Fn(&T, T) -> T,
        OpMoveMove: Fn(T, T) -> T,
    >(
        l: T,
        r: T,
        expected: &T,
        op_eq_move: OpEqMove,
        op_eq_ref: OpEqRef,
        op_ref_ref: OpRefRef,
        op_move_ref: OpMoveRef,
        op_ref_move: OpRefMove,
        op_move_move: OpMoveMove,
    ) {
        let mut eq_move_result = l.clone();
        op_eq_move(&mut eq_move_result, r.clone());
        assert_eq!(eq_move_result, *expected);
        let mut eq_ref_result = l.clone();
        op_eq_ref(&mut eq_ref_result, &r);
        assert_eq!(eq_ref_result, *expected);
        assert_eq!(op_ref_ref(&l, &r), *expected);
        assert_eq!(op_ref_move(&l, r.clone()), *expected);
        assert_eq!(op_move_ref(l.clone(), &r), *expected);
        assert_eq!(op_move_move(l, r), *expected);
    }

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
    fn test_mul() {
        let test = |l: Polynomial<i32>, r: Polynomial<i32>, expected: &Polynomial<i32>| {
            test_op_helper(
                l,
                r,
                expected,
                |l, r| *l *= r,
                |l, r| *l *= r,
                |l, r| l * r,
                |l, r| l * r,
                |l, r| l * r,
                |l, r| l * r,
            );
        };
        test(
            vec![10, 11, 12].into(),
            vec![10, -11, 3, 2, 1].into(),
            &vec![100, 0, 29, -79, 68, 35, 12].into(),
        );
    }

}
