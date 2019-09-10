// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::util::DebugAsDisplay;
use crate::util::Sign;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::One;
use num_traits::Signed;
use num_traits::Zero;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::fmt;
use std::mem;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Mul;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RealAlgebraicNumberData {
    pub minimal_polynomial: Polynomial<BigInt>,
    pub lower_bound: Ratio<BigInt>,
    pub upper_bound: Ratio<BigInt>,
}

fn debug_real_algebraic_number(
    data: &RealAlgebraicNumberData,
    f: &mut fmt::Formatter,
    struct_name: &str,
) -> fmt::Result {
    f.debug_struct(struct_name)
        .field(
            "minimal_polynomial",
            &DebugAsDisplay(&data.minimal_polynomial),
        )
        .field("lower_bound", &DebugAsDisplay(&data.lower_bound))
        .field("upper_bound", &DebugAsDisplay(&data.upper_bound))
        .finish()
}

impl fmt::Debug for RealAlgebraicNumberData {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug_real_algebraic_number(self, f, "RealAlgebraicNumberData")
    }
}

#[derive(Clone)]
pub struct RealAlgebraicNumber {
    data: RealAlgebraicNumberData,
}

impl fmt::Debug for RealAlgebraicNumber {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        debug_real_algebraic_number(&self.data(), f, "RealAlgebraicNumber")
    }
}

macro_rules! impl_from_int_or_ratio {
    ($t:ident) => {
        impl From<$t> for RealAlgebraicNumber {
            fn from(value: $t) -> Self {
                let value = BigInt::from(value);
                Self::new_unchecked(
                    [-&value, BigInt::one()].into(),
                    value.clone().into(),
                    value.into(),
                )
            }
        }

        impl From<Ratio<$t>> for RealAlgebraicNumber {
            fn from(value: Ratio<$t>) -> Self {
                let (numer, denom) = value.into();
                let numer = BigInt::from(numer);
                if denom.is_one() {
                    return numer.into();
                }
                let denom = BigInt::from(denom);
                let neg_numer = -&numer;
                let ratio = Ratio::new_raw(numer, denom.clone());
                Self::new_unchecked([neg_numer, denom].into(), ratio.clone(), ratio)
            }
        }
    };
}

impl_from_int_or_ratio!(u8);
impl_from_int_or_ratio!(u16);
impl_from_int_or_ratio!(u32);
impl_from_int_or_ratio!(u64);
impl_from_int_or_ratio!(u128);
impl_from_int_or_ratio!(usize);
impl_from_int_or_ratio!(BigUint);
impl_from_int_or_ratio!(i8);
impl_from_int_or_ratio!(i16);
impl_from_int_or_ratio!(i32);
impl_from_int_or_ratio!(i64);
impl_from_int_or_ratio!(i128);
impl_from_int_or_ratio!(isize);
impl_from_int_or_ratio!(BigInt);

#[derive(Copy, Clone, Debug)]
enum ValueOrInfinity<T> {
    PositiveInfinity,
    Value(T),
    Zero,
    NegativeInfinity,
}

impl<T> ValueOrInfinity<T> {
    #[allow(dead_code)]
    fn as_ref(&self) -> ValueOrInfinity<&T> {
        match self {
            ValueOrInfinity::PositiveInfinity => ValueOrInfinity::PositiveInfinity,
            ValueOrInfinity::Value(value) => ValueOrInfinity::Value(value),
            ValueOrInfinity::Zero => ValueOrInfinity::Zero,
            ValueOrInfinity::NegativeInfinity => ValueOrInfinity::NegativeInfinity,
        }
    }
}

#[derive(Copy, Clone, Debug)]
struct SignChanges {
    sign_change_count: usize,
    is_root: bool,
}

fn sign_changes_at(
    sturm_sequence: &[Polynomial<BigInt>],
    at: ValueOrInfinity<&Ratio<BigInt>>,
) -> SignChanges {
    let mut sign_change_count = 0;
    let mut last_sign = None;
    let mut is_root = false;
    for polynomial in sturm_sequence {
        let sign = match at {
            ValueOrInfinity::PositiveInfinity => Sign::new(&polynomial.highest_power_coefficient()),
            ValueOrInfinity::Value(at) => Sign::new(&polynomial.eval_generic(at, Ratio::zero())),
            ValueOrInfinity::Zero => Sign::new(&polynomial.coefficient(0)),
            ValueOrInfinity::NegativeInfinity => {
                let degree = polynomial.degree().unwrap_or(0);
                if degree == 0 || degree.is_odd() {
                    Sign::new(&polynomial.highest_power_coefficient())
                } else {
                    Some(Sign::Positive)
                }
            }
        };
        if let Some(sign) = sign {
            if last_sign != Some(sign) {
                sign_change_count += 1;
            }
            last_sign = Some(sign);
        } else if last_sign.is_none() {
            is_root = true;
        }
    }
    SignChanges {
        sign_change_count,
        is_root,
    }
}

#[derive(Debug)]
struct BoundAndSignChanges<'a> {
    bound: &'a mut Ratio<BigInt>,
    sign_changes: Option<SignChanges>,
}

impl<'a> BoundAndSignChanges<'a> {
    #[inline]
    fn new(bound: &'a mut Ratio<BigInt>) -> Self {
        Self {
            bound,
            sign_changes: None,
        }
    }
    fn get_sign_changes(&mut self, primitive_sturm_sequence: &[Polynomial<BigInt>]) -> SignChanges {
        if let Some(sign_changes) = self.sign_changes {
            sign_changes
        } else {
            let sign_changes =
                sign_changes_at(primitive_sturm_sequence, ValueOrInfinity::Value(self.bound));
            self.sign_changes = Some(sign_changes);
            sign_changes
        }
    }
    fn set(&mut self, bound: Ratio<BigInt>, sign_changes: SignChanges) {
        *self.bound = bound;
        self.sign_changes = Some(sign_changes);
    }
}

impl Deref for BoundAndSignChanges<'_> {
    type Target = Ratio<BigInt>;
    fn deref(&self) -> &Ratio<BigInt> {
        &self.bound
    }
}

impl DerefMut for BoundAndSignChanges<'_> {
    fn deref_mut(&mut self) -> &mut Ratio<BigInt> {
        &mut self.bound
    }
}

fn distance(a: usize, b: usize) -> usize {
    if a < b {
        b - a
    } else {
        a - b
    }
}

#[derive(Debug)]
struct BoundsShrinker<'a> {
    minimal_polynomial: &'a Polynomial<BigInt>,
    primitive_sturm_sequence: Cow<'a, [Polynomial<BigInt>]>,
    lower_bound: BoundAndSignChanges<'a>,
    upper_bound: BoundAndSignChanges<'a>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum BoundsShrinkResult {
    Exact,
    Range,
}

impl<'a> BoundsShrinker<'a> {
    #[inline]
    fn with_primitive_sturm_sequence(
        minimal_polynomial: &'a Polynomial<BigInt>,
        primitive_sturm_sequence: Cow<'a, [Polynomial<BigInt>]>,
        lower_bound: &'a mut Ratio<BigInt>,
        upper_bound: &'a mut Ratio<BigInt>,
    ) -> Self {
        BoundsShrinker {
            minimal_polynomial,
            primitive_sturm_sequence,
            lower_bound: BoundAndSignChanges::new(lower_bound),
            upper_bound: BoundAndSignChanges::new(upper_bound),
        }
    }
    fn new(
        minimal_polynomial: &'a Polynomial<BigInt>,
        lower_bound: &'a mut Ratio<BigInt>,
        upper_bound: &'a mut Ratio<BigInt>,
    ) -> Self {
        Self::with_primitive_sturm_sequence(
            minimal_polynomial,
            Cow::Owned(minimal_polynomial.to_primitive_sturm_sequence()),
            lower_bound,
            upper_bound,
        )
    }
    fn shrink(&mut self) -> BoundsShrinkResult {
        if *self.lower_bound == *self.upper_bound {
            BoundsShrinkResult::Exact
        } else if self.minimal_polynomial.degree() == Some(1) {
            let value = Ratio::new(
                -self.minimal_polynomial.coefficient(0),
                self.minimal_polynomial.coefficient(1),
            );
            *self.lower_bound = value.clone();
            *self.upper_bound = value;
            BoundsShrinkResult::Exact
        } else {
            // TODO: also use newton's method
            let middle = (&*self.lower_bound + &*self.upper_bound) / BigInt::from(2);
            let lower_bound_sign_changes = self
                .lower_bound
                .get_sign_changes(&self.primitive_sturm_sequence);
            assert!(!lower_bound_sign_changes.is_root);
            let upper_bound_sign_changes = self
                .upper_bound
                .get_sign_changes(&self.primitive_sturm_sequence);
            assert!(!upper_bound_sign_changes.is_root);
            assert_eq!(
                distance(
                    lower_bound_sign_changes.sign_change_count,
                    upper_bound_sign_changes.sign_change_count
                ),
                1
            );
            let middle_sign_changes = sign_changes_at(
                &self.primitive_sturm_sequence,
                ValueOrInfinity::Value(&middle),
            );
            assert!(!middle_sign_changes.is_root);
            if middle_sign_changes.sign_change_count == lower_bound_sign_changes.sign_change_count {
                self.lower_bound.set(middle, middle_sign_changes);
            } else {
                assert_eq!(
                    middle_sign_changes.sign_change_count,
                    upper_bound_sign_changes.sign_change_count
                );
                self.upper_bound.set(middle, middle_sign_changes);
            }
            BoundsShrinkResult::Range
        }
    }
}

impl RealAlgebraicNumber {
    pub fn new_unchecked(
        minimal_polynomial: Polynomial<BigInt>,
        lower_bound: Ratio<BigInt>,
        upper_bound: Ratio<BigInt>,
    ) -> Self {
        Self {
            data: RealAlgebraicNumberData {
                minimal_polynomial,
                lower_bound,
                upper_bound,
            },
        }
    }
    #[inline]
    pub fn minimal_polynomial(&self) -> &Polynomial<BigInt> {
        &self.data().minimal_polynomial
    }
    #[inline]
    pub fn data(&self) -> &RealAlgebraicNumberData {
        &self.data
    }
    #[inline]
    pub fn into_data(self) -> RealAlgebraicNumberData {
        self.data
    }
    pub fn degree(&self) -> usize {
        self.minimal_polynomial()
            .degree()
            .expect("known to be non-zero")
    }
    #[inline]
    pub fn is_rational(&self) -> bool {
        self.degree() <= 1
    }
    pub fn is_integer(&self) -> bool {
        self.is_rational() && self.minimal_polynomial().coefficient(1).is_one()
    }
    pub fn to_rational(&self) -> Option<Ratio<BigInt>> {
        if self.is_rational() {
            Some(Ratio::new_raw(
                -self.minimal_polynomial().coefficient(0),
                self.minimal_polynomial().coefficient(1),
            ))
        } else {
            None
        }
    }
    pub fn to_integer(&self) -> Option<BigInt> {
        if self.is_integer() {
            Some(-self.minimal_polynomial().coefficient(0))
        } else {
            None
        }
    }
    #[inline]
    pub fn lower_bound(&self) -> &Ratio<BigInt> {
        &self.data().lower_bound
    }
    #[inline]
    pub fn upper_bound(&self) -> &Ratio<BigInt> {
        &self.data().upper_bound
    }
    fn bounds_shrinker(&mut self) -> BoundsShrinker {
        let RealAlgebraicNumberData {
            minimal_polynomial,
            lower_bound,
            upper_bound,
        } = &mut self.data;
        BoundsShrinker::new(minimal_polynomial, lower_bound, upper_bound)
    }
}

fn neg(value: Cow<RealAlgebraicNumber>) -> RealAlgebraicNumber {
    let degree_is_odd = value.degree().is_odd();
    fn do_neg<I: Iterator<Item = BigInt>>(
        iter: I,
        degree_is_odd: bool,
        neg_lower_bound: Ratio<BigInt>,
        neg_upper_bound: Ratio<BigInt>,
    ) -> RealAlgebraicNumber {
        let minimal_polynomial = iter
            .enumerate()
            .map(|(index, coefficient)| {
                if index.is_odd() == degree_is_odd {
                    coefficient
                } else {
                    -coefficient
                }
            })
            .collect();

        // swap negated bounds
        let lower_bound = neg_upper_bound;
        let upper_bound = neg_lower_bound;
        RealAlgebraicNumber::new_unchecked(minimal_polynomial, lower_bound, upper_bound)
    }
    match value {
        Cow::Borrowed(value) => do_neg(
            value.minimal_polynomial().iter(),
            degree_is_odd,
            -value.lower_bound(),
            -value.upper_bound(),
        ),
        Cow::Owned(RealAlgebraicNumber {
            data:
                RealAlgebraicNumberData {
                    minimal_polynomial,
                    lower_bound,
                    upper_bound,
                },
        }) => do_neg(
            minimal_polynomial.into_iter(),
            degree_is_odd,
            -lower_bound,
            -upper_bound,
        ),
    }
}

impl Neg for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn neg(self) -> Self::Output {
        neg(Cow::Borrowed(self))
    }
}

impl Neg for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn neg(self) -> Self::Output {
        neg(Cow::Owned(self))
    }
}

#[derive(Clone)]
struct EvalPoint(Polynomial<Polynomial<BigInt>>);

impl fmt::Debug for EvalPoint {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_tuple("EvalPoint")
            .field(&DebugAsDisplay(&self.0))
            .finish()
    }
}

impl EvalPoint {
    fn zero() -> Self {
        EvalPoint(Polynomial::zero())
    }
    fn add_eval_point() -> &'static Self {
        fn make_eval_point() -> EvalPoint {
            EvalPoint(
                vec![
                    vec![BigInt::zero(), BigInt::one()].into(),
                    vec![-BigInt::one()].into(),
                ]
                .into(),
            )
        }
        lazy_static! {
            static ref EVAL_POINT: EvalPoint = make_eval_point();
        }
        &EVAL_POINT
    }
    fn div_eval_point() -> &'static Self {
        fn make_eval_point() -> EvalPoint {
            EvalPoint(
                vec![
                    Polynomial::zero(),
                    vec![BigInt::zero(), BigInt::one()].into(),
                ]
                .into(),
            )
        }
        lazy_static! {
            static ref EVAL_POINT: EvalPoint = make_eval_point();
        }
        &EVAL_POINT
    }
}

impl Add<BigInt> for EvalPoint {
    type Output = Self;
    fn add(self, rhs: BigInt) -> Self {
        println!("self + rhs: ({}) + ({})", self.0, rhs);
        let retval = self.0 + Polynomial::from(rhs);
        println!("retval: {}", retval);
        EvalPoint(retval)
    }
}

impl Mul<&'_ EvalPoint> for EvalPoint {
    type Output = Self;
    fn mul(self, rhs: &Self) -> Self {
        println!("self * rhs: ({}) * ({})", self.0, rhs.0);
        let retval = self.0 * &rhs.0;
        println!("retval: {}", retval);
        EvalPoint(retval)
    }
}

#[derive(Clone)]
struct ResultFactor {
    primitive_sturm_sequence: Vec<Polynomial<BigInt>>,
}

impl ResultFactor {
    fn factor(&self) -> Cow<Polynomial<BigInt>> {
        self.primitive_sturm_sequence
            .get(0)
            .map(Cow::Borrowed)
            .unwrap_or_else(|| Cow::Owned(Polynomial::zero()))
    }
    fn into_factor(self) -> Polynomial<BigInt> {
        self.primitive_sturm_sequence
            .into_iter()
            .next()
            .unwrap_or_else(Polynomial::zero)
    }
}

impl fmt::Debug for ResultFactor {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.factor())
    }
}

impl AddAssign for RealAlgebraicNumber {
    fn add_assign(&mut self, mut rhs: RealAlgebraicNumber) {
        #![allow(clippy::suspicious_op_assign_impl)] // we need to use other operators
        if self.is_rational() && rhs.is_rational() {
            *self = (self.to_rational().expect("known to be rational")
                + rhs.to_rational().expect("known to be rational"))
            .into();
            return;
        }
        let mut lhs_bounds_shrinker = self.bounds_shrinker();
        let mut rhs_bounds_shrinker = rhs.bounds_shrinker();
        let resultant_lhs: Polynomial<Polynomial<BigInt>> = lhs_bounds_shrinker
            .minimal_polynomial
            .iter()
            .map(Polynomial::from)
            .collect();
        println!("resultant_lhs: {}", resultant_lhs);
        let eval_point = EvalPoint::add_eval_point();
        println!("eval_point: {:?}", eval_point);
        let resultant_rhs = rhs_bounds_shrinker
            .minimal_polynomial
            .eval_generic(eval_point, EvalPoint::zero())
            .0;
        println!("resultant_rhs: {}", resultant_rhs);
        let resultant = resultant_lhs.resultant(resultant_rhs);
        println!("resultant: {}", resultant);
        let mut factors: Vec<ResultFactor> = resultant
            .factor()
            .polynomial_factors
            .into_iter()
            .map(|factor| ResultFactor {
                primitive_sturm_sequence: factor.polynomial.into_primitive_sturm_sequence(),
            })
            .collect();
        println!("factors: {:?}", factors);
        let mut factors_temp = Vec::with_capacity(factors.len());
        let result = 'result_loop: loop {
            let lower_bound = &*lhs_bounds_shrinker.lower_bound + &*rhs_bounds_shrinker.lower_bound;
            let upper_bound = &*lhs_bounds_shrinker.upper_bound + &*rhs_bounds_shrinker.upper_bound;
            println!("lower_bound: {}", lower_bound);
            println!("upper_bound: {}", upper_bound);
            mem::swap(&mut factors, &mut factors_temp);
            factors.clear();
            for factor in factors_temp.drain(..) {
                dbg!(&factor);
                let lower_bound_sign_changes = sign_changes_at(
                    &factor.primitive_sturm_sequence,
                    ValueOrInfinity::Value(&lower_bound),
                );
                if lower_bound_sign_changes.is_root {
                    println!("found root: {}", lower_bound);
                    break 'result_loop lower_bound.into();
                }
                let upper_bound_sign_changes = sign_changes_at(
                    &factor.primitive_sturm_sequence,
                    ValueOrInfinity::Value(&upper_bound),
                );
                if upper_bound_sign_changes.is_root {
                    println!("found root: {}", upper_bound);
                    break 'result_loop upper_bound.into();
                }
                if lower_bound_sign_changes.sign_change_count
                    != upper_bound_sign_changes.sign_change_count
                {
                    println!("retained: {:?}", factor);
                    factors.push(factor);
                } else {
                    println!("discarded: {:?}", factor);
                }
            }
            if factors.len() <= 1 {
                break RealAlgebraicNumber::new_unchecked(
                    factors.remove(0).into_factor(),
                    lower_bound,
                    upper_bound,
                );
            }
            lhs_bounds_shrinker.shrink();
            rhs_bounds_shrinker.shrink();
        };
        *self = result;
    }
}

impl AddAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    fn add_assign(&mut self, rhs: &RealAlgebraicNumber) {
        *self += rhs.clone();
    }
}

impl Add for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn add(mut self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self += rhs;
        self
    }
}

impl Add<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn add(mut self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self += rhs;
        self
    }
}

impl Add<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn add(self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().add(rhs)
    }
}

impl<'a, 'b> Add<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn add(self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().add(rhs)
    }
}

lazy_static! {
    static ref ZERO: RealAlgebraicNumber = 0.into();
    static ref ONE: RealAlgebraicNumber = 1.into();
}

impl Zero for RealAlgebraicNumber {
    fn zero() -> Self {
        ZERO.clone()
    }
    #[inline]
    fn is_zero(&self) -> bool {
        self.minimal_polynomial() == ZERO.minimal_polynomial()
    }
}

impl SubAssign for RealAlgebraicNumber {
    fn sub_assign(&mut self, rhs: RealAlgebraicNumber) {
        self.add_assign(-rhs);
    }
}

impl SubAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    fn sub_assign(&mut self, rhs: &RealAlgebraicNumber) {
        self.add_assign(-rhs);
    }
}

impl Sub for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn sub(mut self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self -= rhs;
        self
    }
}

impl Sub<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn sub(mut self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self -= rhs;
        self
    }
}

impl Sub<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn sub(self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().sub(rhs)
    }
}

impl<'a, 'b> Sub<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn sub(self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().sub(rhs)
    }
}

impl PartialEq for RealAlgebraicNumber {
    fn eq(&self, rhs: &RealAlgebraicNumber) -> bool {
        (self - rhs).is_zero()
    }
}

impl Eq for RealAlgebraicNumber {}

impl PartialOrd for RealAlgebraicNumber {
    fn partial_cmp(&self, rhs: &RealAlgebraicNumber) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl Ord for RealAlgebraicNumber {
    fn cmp(&self, rhs: &RealAlgebraicNumber) -> Ordering {
        let difference = self - rhs;
        if difference.is_zero() {
            Ordering::Equal
        } else if let Some(value) = difference.to_rational() {
            if value.is_positive() {
                Ordering::Greater
            } else {
                Ordering::Less
            }
        } else {
            let difference = difference.into_data();
            if difference.lower_bound.is_positive() {
                Ordering::Greater
            } else if difference.upper_bound.is_negative() {
                Ordering::Less
            } else {
                let primitive_sturm_sequence = difference
                    .minimal_polynomial
                    .into_primitive_sturm_sequence();
                let lower_bound_sign_changes = sign_changes_at(
                    &primitive_sturm_sequence,
                    ValueOrInfinity::Value(&difference.lower_bound),
                );
                assert!(!lower_bound_sign_changes.is_root);
                let upper_bound_sign_changes = sign_changes_at(
                    &primitive_sturm_sequence,
                    ValueOrInfinity::Value(&difference.upper_bound),
                );
                assert!(!upper_bound_sign_changes.is_root);
                let zero_sign_changes =
                    sign_changes_at(&primitive_sturm_sequence, ValueOrInfinity::Zero);
                assert!(!zero_sign_changes.is_root);
                if lower_bound_sign_changes.sign_change_count == zero_sign_changes.sign_change_count
                {
                    Ordering::Greater
                } else {
                    assert_eq!(
                        upper_bound_sign_changes.sign_change_count,
                        zero_sign_changes.sign_change_count
                    );
                    Ordering::Less
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::test_op_helper;
    use num_integer::Roots;

    fn r(n: i128, d: i128) -> Ratio<BigInt> {
        Ratio::new(BigInt::from(n), BigInt::from(d))
    }

    fn ri(v: i128) -> Ratio<BigInt> {
        Ratio::from(BigInt::from(v))
    }

    fn p(poly: &[i128]) -> Polynomial<BigInt> {
        poly.iter().copied().map(BigInt::from).collect()
    }

    fn make_sqrt(
        v: i128,
        lower_bound: Ratio<BigInt>,
        upper_bound: Ratio<BigInt>,
    ) -> RealAlgebraicNumber {
        let sqrt = v.sqrt();
        assert_ne!(
            sqrt * sqrt,
            v,
            "make_sqrt doesn't work with perfect squares"
        );
        RealAlgebraicNumber::new_unchecked(p(&[-v, 0, 1]), lower_bound, upper_bound)
    }

    #[test]
    fn test_debug() {
        fn test_case(
            poly: Polynomial<BigInt>,
            lower_bound: Ratio<BigInt>,
            upper_bound: Ratio<BigInt>,
            expected: &str,
        ) {
            let real_algebraic_number =
                RealAlgebraicNumber::new_unchecked(poly, lower_bound, upper_bound);
            let string = format!("{:?}", real_algebraic_number);
            assert_eq!(&string, expected);
        }

        test_case(
            p(&[0, 1]),
            ri(0),
            ri(0),
            "RealAlgebraicNumber { minimal_polynomial: 0 + 1*X, lower_bound: 0, upper_bound: 0 }",
        );

        test_case(
            p(&[-2, 0, 1]),
            ri(1),
            ri(2),
            "RealAlgebraicNumber { minimal_polynomial: -2 + 0*X + 1*X^2, lower_bound: 1, upper_bound: 2 }",
        );

        test_case(
            p(&[
                10_788_246_961,
                1_545_510_240,
                -29_925_033_224,
                1_820_726_496,
                19_259_216_972,
                -6_781_142_688,
                -2_872_989_528,
                2_147_919_840,
                -306_405_418,
                -105_773_280,
                53_150_088,
                -10_681_440,
                1_243_820,
                -89568,
                3928,
                -96,
                1,
            ]),
            r(22_46827, 100_000),
            r(22_4683, 10_000),
            "RealAlgebraicNumber { minimal_polynomial: 10788246961 \
             + 1545510240*X \
             + -29925033224*X^2 \
             + 1820726496*X^3 \
             + 19259216972*X^4 \
             + -6781142688*X^5 \
             + -2872989528*X^6 \
             + 2147919840*X^7 \
             + -306405418*X^8 \
             + -105773280*X^9 \
             + 53150088*X^10 \
             + -10681440*X^11 \
             + 1243820*X^12 \
             + -89568*X^13 \
             + 3928*X^14 \
             + -96*X^15 \
             + 1*X^16, \
             lower_bound: 2246827/100000, \
             upper_bound: 224683/10000 }",
        );
    }

    #[test]
    fn test_neg() {
        fn test_case(
            real_algebraic_number: RealAlgebraicNumber,
            expected: RealAlgebraicNumberData,
        ) {
            assert_eq!(real_algebraic_number.neg().into_data(), expected);
        }
        test_case(
            RealAlgebraicNumber::new_unchecked(p(&[-1, -2, 1]), ri(2), ri(3)),
            RealAlgebraicNumberData {
                minimal_polynomial: p(&[-1, 2, 1]),
                lower_bound: ri(-3),
                upper_bound: ri(-2),
            },
        );
        test_case(
            RealAlgebraicNumber::from(1),
            RealAlgebraicNumber::from(-1).into_data(),
        );
        test_case(
            RealAlgebraicNumber::from(r(4, 5)),
            RealAlgebraicNumber::from(r(-4, 5)).into_data(),
        );
    }

    #[test]
    fn test_add() {
        fn test_case<
            A: Into<RealAlgebraicNumber>,
            B: Into<RealAlgebraicNumber>,
            E: Into<RealAlgebraicNumber>,
        >(
            a: A,
            b: B,
            expected: E,
        ) {
            let a = a.into();
            println!("a: {:?}", a);
            let b = b.into();
            println!("b: {:?}", b);
            let expected = expected.into();
            println!("expected: {:?}", expected);
            test_op_helper(
                a,
                b,
                &expected,
                |l, r| *l += r,
                |l, r| *l += r,
                |l, r| l + r,
                |l, r| l + r,
                |l, r| l + r,
                |l, r| l + r,
            );
        }
        test_case(1, 2, 1 + 2);
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(8, ri(1), ri(3)),
        );
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(3, ri(1), ri(2)),
            RealAlgebraicNumber::new_unchecked(p(&[1, 0, -10, 0, 1]), ri(3), ri(4)),
        );
        test_case(
            // sqrt(5) - sqrt(3) + 1
            RealAlgebraicNumber::new_unchecked(p(&[-11, 28, -10, -4, 1]), ri(1), ri(2)),
            // sqrt(3) - sqrt(5) + 1 / 2
            RealAlgebraicNumber::new_unchecked(p(&[1, 248, -232, -32, 16]), ri(-1), ri(0)),
            r(3, 2),
        );
    }
}
