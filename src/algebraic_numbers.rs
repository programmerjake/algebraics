// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::{
    interval_arithmetic::DyadicFractionInterval,
    polynomial::Polynomial,
    traits::{AlwaysExactDiv, AlwaysExactDivAssign, CeilLog2, ExactDiv, ExactDivAssign, FloorLog2},
    util::{DebugAsDisplay, Sign},
};
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{Num, One, Pow, Signed, ToPrimitive, Zero};
use std::{
    borrow::Cow,
    cmp::Ordering,
    error::Error,
    fmt, hash, mem,
    ops::{
        Add, AddAssign, Deref, DerefMut, Div, DivAssign, Mul, MulAssign, Neg, Rem, RemAssign, Sub,
        SubAssign,
    },
};

pub trait IntoRationalExponent {
    fn into_rational_exponent(self) -> Ratio<BigInt>;
}

impl<T: IntoRationalExponent + Clone> IntoRationalExponent for &'_ T {
    fn into_rational_exponent(self) -> Ratio<BigInt> {
        (*self).clone().into_rational_exponent()
    }
}

impl<N: Into<BigInt>, D: Into<BigInt>> IntoRationalExponent for (N, D) {
    fn into_rational_exponent(self) -> Ratio<BigInt> {
        let (numer, denom) = self;
        Ratio::new(numer.into(), denom.into())
    }
}

#[derive(Clone)]
pub struct RealAlgebraicNumberData {
    pub minimal_polynomial: Polynomial<BigInt>,
    pub interval: DyadicFractionInterval,
}

impl hash::Hash for RealAlgebraicNumberData {
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        let Self {
            minimal_polynomial,
            interval,
        } = self;
        minimal_polynomial.hash(state);
        interval.hash(state);
    }
}

impl PartialEq for RealAlgebraicNumberData {
    fn eq(&self, rhs: &Self) -> bool {
        let Self {
            minimal_polynomial,
            interval,
        } = self;
        *minimal_polynomial == rhs.minimal_polynomial && interval.is_same(&rhs.interval)
    }
}

impl Eq for RealAlgebraicNumberData {}

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
        .field("interval", &data.interval)
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
                    DyadicFractionInterval::from_int(value, 0),
                )
            }
        }

        impl IntoRationalExponent for $t {
            fn into_rational_exponent(self) -> Ratio<BigInt> {
                BigInt::from(self).into()
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
                Self::new_unchecked(
                    [neg_numer, denom].into(),
                    DyadicFractionInterval::from_ratio(ratio, 0),
                )
            }
        }

        impl IntoRationalExponent for Ratio<$t> {
            fn into_rational_exponent(self) -> Ratio<BigInt> {
                let (numer, denom) = self.into();
                Ratio::new_raw(numer.into(), denom.into())
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
    #[allow(dead_code)]
    PositiveInfinity,
    Value(T),
    Zero,
    #[allow(dead_code)]
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
struct IntervalAndSignChanges<'a> {
    interval: &'a mut DyadicFractionInterval,
    lower_bound_sign_changes: Option<SignChanges>,
    upper_bound_sign_changes: Option<SignChanges>,
}

impl<'a> IntervalAndSignChanges<'a> {
    #[inline]
    fn new(interval: &'a mut DyadicFractionInterval) -> Self {
        Self {
            interval,
            lower_bound_sign_changes: None,
            upper_bound_sign_changes: None,
        }
    }
    fn get_sign_changes_helper<
        GSC: Fn(&mut Self) -> &mut Option<SignChanges>,
        GIB: Fn(&DyadicFractionInterval) -> Ratio<BigInt>,
    >(
        &mut self,
        primitive_sturm_sequence: &[Polynomial<BigInt>],
        get_sign_changes: GSC,
        get_interval_bound: GIB,
    ) -> SignChanges {
        if let Some(sign_changes) = *get_sign_changes(self) {
            sign_changes
        } else {
            let at = get_interval_bound(&self.interval);
            let sign_changes =
                sign_changes_at(primitive_sturm_sequence, ValueOrInfinity::Value(&at));
            *get_sign_changes(self) = Some(sign_changes);
            sign_changes
        }
    }
    fn get_lower_bound_sign_changes(
        &mut self,
        primitive_sturm_sequence: &[Polynomial<BigInt>],
    ) -> SignChanges {
        self.get_sign_changes_helper(
            primitive_sturm_sequence,
            |v| &mut v.lower_bound_sign_changes,
            DyadicFractionInterval::lower_bound,
        )
    }
    fn get_upper_bound_sign_changes(
        &mut self,
        primitive_sturm_sequence: &[Polynomial<BigInt>],
    ) -> SignChanges {
        self.get_sign_changes_helper(
            primitive_sturm_sequence,
            |v| &mut v.upper_bound_sign_changes,
            DyadicFractionInterval::upper_bound,
        )
    }
    fn set_to_dyadic_fraction(&mut self, numer: BigInt, sign_changes: SignChanges) {
        *self.interval =
            DyadicFractionInterval::from_dyadic_fraction(numer, self.interval.log2_denom());
        self.lower_bound_sign_changes = Some(sign_changes);
        self.upper_bound_sign_changes = Some(sign_changes);
    }
    fn set_lower_bound(&mut self, lower_bound_numer: BigInt, sign_changes: SignChanges) {
        self.interval.set_lower_bound_numer(lower_bound_numer);
        self.lower_bound_sign_changes = Some(sign_changes);
    }
    fn set_upper_bound(&mut self, upper_bound_numer: BigInt, sign_changes: SignChanges) {
        self.interval.set_upper_bound_numer(upper_bound_numer);
        self.upper_bound_sign_changes = Some(sign_changes);
    }
}

impl Deref for IntervalAndSignChanges<'_> {
    type Target = DyadicFractionInterval;
    fn deref(&self) -> &DyadicFractionInterval {
        &self.interval
    }
}

impl DerefMut for IntervalAndSignChanges<'_> {
    fn deref_mut(&mut self) -> &mut DyadicFractionInterval {
        &mut self.interval
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
struct IntervalShrinker<'a> {
    minimal_polynomial: &'a Polynomial<BigInt>,
    primitive_sturm_sequence: Cow<'a, [Polynomial<BigInt>]>,
    interval: IntervalAndSignChanges<'a>,
}

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
enum IntervalShrinkResult {
    Exact,
    Range,
}

impl<'a> IntervalShrinker<'a> {
    #[inline]
    fn with_primitive_sturm_sequence(
        minimal_polynomial: &'a Polynomial<BigInt>,
        primitive_sturm_sequence: Cow<'a, [Polynomial<BigInt>]>,
        interval: &'a mut DyadicFractionInterval,
    ) -> Self {
        IntervalShrinker {
            minimal_polynomial,
            primitive_sturm_sequence,
            interval: IntervalAndSignChanges::new(interval),
        }
    }
    fn new(
        minimal_polynomial: &'a Polynomial<BigInt>,
        interval: &'a mut DyadicFractionInterval,
    ) -> Self {
        Self::with_primitive_sturm_sequence(
            minimal_polynomial,
            Cow::Owned(minimal_polynomial.to_primitive_sturm_sequence()),
            interval,
        )
    }
    fn shrink(&mut self) -> IntervalShrinkResult {
        let range_size = self.interval.upper_bound_numer() - self.interval.lower_bound_numer();
        assert!(!range_size.is_negative());
        if range_size.is_zero() {
            IntervalShrinkResult::Exact
        } else {
            // TODO: also use newton's method
            lazy_static! {
                static ref RANGE_SIZE_CUTOFF: BigInt = 16.into();
            }
            if range_size < *RANGE_SIZE_CUTOFF {
                let log2_denom = self.interval.log2_denom();
                self.interval.convert_log2_denom(log2_denom + 1);
            }
            let lower_bound_sign_changes = self
                .interval
                .get_lower_bound_sign_changes(&self.primitive_sturm_sequence);
            if lower_bound_sign_changes.is_root {
                self.interval.set_upper_bound(
                    self.interval.lower_bound_numer().clone(),
                    lower_bound_sign_changes,
                );
                return IntervalShrinkResult::Exact;
            }
            let upper_bound_sign_changes = self
                .interval
                .get_upper_bound_sign_changes(&self.primitive_sturm_sequence);
            if upper_bound_sign_changes.is_root {
                self.interval.set_lower_bound(
                    self.interval.upper_bound_numer().clone(),
                    upper_bound_sign_changes,
                );
                return IntervalShrinkResult::Exact;
            }
            assert_eq!(
                distance(
                    lower_bound_sign_changes.sign_change_count,
                    upper_bound_sign_changes.sign_change_count
                ),
                1,
                "improper root count, lwoer"
            );
            let middle_numer =
                (self.interval.lower_bound_numer() + self.interval.upper_bound_numer()) / 2i32;
            let middle = Ratio::new(
                middle_numer.clone(),
                BigInt::one() << self.interval.log2_denom(),
            );
            let middle_sign_changes = sign_changes_at(
                &self.primitive_sturm_sequence,
                ValueOrInfinity::Value(&middle),
            );
            if middle_sign_changes.is_root {
                self.interval
                    .set_to_dyadic_fraction(middle_numer, middle_sign_changes);
                return IntervalShrinkResult::Exact;
            }
            if middle_sign_changes.sign_change_count == lower_bound_sign_changes.sign_change_count {
                self.interval
                    .set_lower_bound(middle_numer, middle_sign_changes);
            } else {
                assert_eq!(
                    middle_sign_changes.sign_change_count,
                    upper_bound_sign_changes.sign_change_count
                );
                self.interval
                    .set_upper_bound(middle_numer, middle_sign_changes);
            }
            IntervalShrinkResult::Range
        }
    }
}

impl RealAlgebraicNumber {
    pub fn new_unchecked(
        minimal_polynomial: Polynomial<BigInt>,
        interval: DyadicFractionInterval,
    ) -> Self {
        Self {
            data: RealAlgebraicNumberData {
                minimal_polynomial,
                interval,
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
    pub fn interval(&self) -> &DyadicFractionInterval {
        &self.data().interval
    }
    fn interval_shrinker(&mut self) -> IntervalShrinker {
        let RealAlgebraicNumberData {
            minimal_polynomial,
            interval,
        } = &mut self.data;
        IntervalShrinker::new(minimal_polynomial, interval)
    }
    pub fn into_integer_floor(mut self) -> BigInt {
        if let Some(ratio) = self.to_rational() {
            ratio.floor().to_integer()
        } else {
            let mut interval_shrinker = self.interval_shrinker();
            loop {
                let (floor_interval_lower_bound_numer, floor_interval_upper_bound_numer, _) =
                    interval_shrinker.interval.floor(0).destructure();
                if floor_interval_lower_bound_numer == floor_interval_upper_bound_numer {
                    return floor_interval_lower_bound_numer;
                }
                interval_shrinker.shrink();
            }
        }
    }
    pub fn to_integer_floor(&self) -> BigInt {
        if let Some(ratio) = self.to_rational() {
            ratio.floor().to_integer()
        } else {
            self.clone().into_integer_floor()
        }
    }
    pub fn into_floor(self) -> Self {
        self.into_integer_floor().into()
    }
    pub fn floor(&self) -> Self {
        self.to_integer_floor().into()
    }
    /// returns `self - self.floor()`
    pub fn into_fract(mut self) -> Self {
        if let Some(ratio) = self.to_rational() {
            ratio.fract().into()
        } else {
            let mut interval_shrinker = self.interval_shrinker();
            loop {
                let (floor_interval_lower_bound_numer, floor_interval_upper_bound_numer, _) =
                    interval_shrinker.interval.floor(0).destructure();
                if floor_interval_lower_bound_numer == floor_interval_upper_bound_numer {
                    return self - RealAlgebraicNumber::from(floor_interval_lower_bound_numer);
                }
                interval_shrinker.shrink();
            }
        }
    }
    /// returns `self - self.floor()`
    pub fn fract(&self) -> Self {
        if let Some(ratio) = self.to_rational() {
            ratio.fract().into()
        } else {
            self.clone().into_fract()
        }
    }
    pub fn into_integer_ceil(self) -> BigInt {
        self.neg().into_integer_floor().neg()
    }
    pub fn to_integer_ceil(&self) -> BigInt {
        self.neg().into_integer_floor().neg()
    }
    pub fn into_ceil(self) -> Self {
        self.neg().into_floor().neg()
    }
    pub fn ceil(&self) -> Self {
        self.neg().into_floor().neg()
    }
    pub fn cmp_with_zero(&self) -> Ordering {
        if self.is_zero() {
            Ordering::Equal
        } else if self.interval().lower_bound_numer().is_positive() {
            Ordering::Greater
        } else if self.interval().upper_bound_numer().is_negative() {
            Ordering::Less
        } else if let Some(value) = self.to_rational() {
            value.cmp(&Ratio::zero())
        } else {
            let primitive_sturm_sequence = self.minimal_polynomial().to_primitive_sturm_sequence();
            let lower_bound_sign_changes = sign_changes_at(
                &primitive_sturm_sequence,
                ValueOrInfinity::Value(&self.interval().lower_bound()),
            );
            assert!(!lower_bound_sign_changes.is_root);
            let upper_bound_sign_changes = sign_changes_at(
                &primitive_sturm_sequence,
                ValueOrInfinity::Value(&self.interval().upper_bound()),
            );
            assert!(!upper_bound_sign_changes.is_root);
            let zero_sign_changes =
                sign_changes_at(&primitive_sturm_sequence, ValueOrInfinity::Zero);
            assert!(!zero_sign_changes.is_root);
            if lower_bound_sign_changes.sign_change_count == zero_sign_changes.sign_change_count {
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
    pub fn into_integer_trunc(self) -> BigInt {
        match self.cmp_with_zero() {
            Ordering::Equal => BigInt::zero(),
            Ordering::Greater => self.into_integer_floor(),
            Ordering::Less => self.into_integer_ceil(),
        }
    }
    pub fn to_integer_trunc(&self) -> BigInt {
        match self.cmp_with_zero() {
            Ordering::Equal => BigInt::zero(),
            Ordering::Greater => self.to_integer_floor(),
            Ordering::Less => self.to_integer_ceil(),
        }
    }
    pub fn into_trunc(self) -> Self {
        self.into_integer_trunc().into()
    }
    pub fn trunc(&self) -> Self {
        self.to_integer_trunc().into()
    }
    /// shrinks the interval till it doesn't contain zero
    #[must_use]
    fn remove_zero_from_interval(&mut self) -> Option<(Sign, IntervalShrinker)> {
        let sign = match self.cmp_with_zero() {
            Ordering::Equal => return None,
            Ordering::Less => Sign::Negative,
            Ordering::Greater => Sign::Positive,
        };
        match sign {
            Sign::Negative => {
                if self.interval().upper_bound_numer().is_positive() {
                    self.data.interval.set_upper_bound_to_zero();
                }
            }
            Sign::Positive => {
                if self.interval().lower_bound_numer().is_negative() {
                    self.data.interval.set_lower_bound_to_zero();
                }
            }
        }
        let mut interval_shrinker = self.interval_shrinker();
        while interval_shrinker.interval.contains_zero() {
            interval_shrinker.shrink();
        }
        Some((sign, interval_shrinker))
    }
    pub fn checked_recip(&self) -> Option<Self> {
        if let Some(value) = self.to_rational() {
            if value.is_zero() {
                return None;
            }
            return Some(value.recip().into());
        }
        let mut value = self.clone();
        value
            .remove_zero_from_interval()
            .expect("known to be non-zero");
        let RealAlgebraicNumberData {
            minimal_polynomial,
            interval,
        } = value.into_data();
        let minimal_polynomial = minimal_polynomial.into_iter().rev().collect();
        Some(RealAlgebraicNumber::new_unchecked(
            minimal_polynomial,
            interval.recip(),
        ))
    }
    pub fn recip(&self) -> Self {
        self.checked_recip()
            .expect("checked_recip called on zero value")
    }
    pub fn negative_one() -> Self {
        NEGATIVE_ONE.clone()
    }
    pub fn set_negative_one(&mut self) {
        *self = Self::negative_one();
    }
    pub fn is_negative_one(&self) -> bool {
        self.minimal_polynomial() == NEGATIVE_ONE.minimal_polynomial()
    }
    fn checked_pow_impl(base: Cow<Self>, exponent: Ratio<BigInt>) -> Option<Self> {
        lazy_static! {
            static ref NEGATIVE_ONE_RATIO: Ratio<BigInt> = BigInt::from(-1).into();
        }
        if exponent.is_zero() {
            if base.is_zero() {
                None
            } else {
                Some(Self::one())
            }
        } else if exponent.is_one() {
            Some(base.into_owned())
        } else if exponent == *NEGATIVE_ONE_RATIO {
            base.checked_recip()
        } else if base.is_zero() {
            if exponent.is_negative() {
                None
            } else {
                Some(Self::zero())
            }
        } else if base.is_one() {
            Some(Self::one())
        } else if base.is_negative_one() {
            if exponent.is_integer() {
                Some(if exponent.numer().is_odd() {
                    Self::negative_one()
                } else {
                    Self::one()
                })
            } else {
                None
            }
        } else {
            let base_is_negative = base.is_negative();
            let result_sign = if base_is_negative {
                if exponent.is_integer() {
                    if exponent.numer().is_odd() {
                        Sign::Negative
                    } else {
                        Sign::Positive
                    }
                } else {
                    return None;
                }
            } else {
                Sign::Positive
            };
            let exponent_sign = Sign::new(&exponent).expect("known to be non-zero");
            let (exponent_numer, exponent_denom) = exponent.abs().into();
            let exponent_numer = exponent_numer
                .to_usize()
                .expect("exponent numerator too big");
            let exponent_denom = exponent_denom
                .to_usize()
                .expect("exponent denominator too big");
            if exponent_denom == 1 {
                if let Some((mut numer, mut denom)) = base.to_rational().map(Into::into) {
                    if exponent_sign == Sign::Negative {
                        mem::swap(&mut numer, &mut denom);
                    }
                    // workaround pow not working for Ratio
                    return Some(
                        Ratio::new(numer.pow(exponent_numer), denom.pow(exponent_numer)).into(),
                    );
                }
            }
            let mut base = if exponent_sign == Sign::Negative {
                base.recip() // base was already checked for zero
            } else {
                base.into_owned()
            };
            let resultant_lhs: Polynomial<Polynomial<BigInt>> = base
                .minimal_polynomial()
                .iter()
                .map(Polynomial::from)
                .collect();
            let resultant_rhs: Polynomial<Polynomial<BigInt>> =
                Polynomial::make_monomial(-Polynomial::<BigInt>::one(), exponent_numer)
                    + Polynomial::make_monomial(BigInt::one(), exponent_denom);
            let resultant = resultant_lhs.resultant(resultant_rhs);
            struct PowRootSelector<'a> {
                base: IntervalShrinker<'a>,
                exponent: Ratio<BigInt>,
                result_sign: Sign,
            }
            impl RootSelector for PowRootSelector<'_> {
                fn get_interval(&self) -> DyadicFractionInterval {
                    let mut interval = self.base.interval.abs();
                    let lower_bound_is_zero = interval.lower_bound_numer().is_zero();
                    if interval.upper_bound_numer().is_zero() {
                        assert!(lower_bound_is_zero);
                        return interval;
                    }
                    if lower_bound_is_zero {
                        interval.set_to_upper_bound();
                    }
                    interval = interval.log();
                    interval *= &self.exponent;
                    interval = interval.into_exp();
                    if lower_bound_is_zero {
                        interval.set_lower_bound_to_zero();
                    }
                    match self.result_sign {
                        Sign::Positive => interval,
                        Sign::Negative => -interval,
                    }
                }
                fn shrink_interval(&mut self) {
                    self.base.shrink();
                }
            }
            Some(
                PowRootSelector {
                    base: base.interval_shrinker(),
                    exponent: Ratio::new(exponent_numer.into(), exponent_denom.into()),
                    result_sign,
                }
                .select_root(resultant),
            )
        }
    }
    pub fn checked_into_pow<E: IntoRationalExponent>(self, exponent: E) -> Option<Self> {
        Self::checked_pow_impl(Cow::Owned(self), exponent.into_rational_exponent())
    }
    pub fn checked_pow<E: IntoRationalExponent>(&self, exponent: E) -> Option<Self> {
        Self::checked_pow_impl(Cow::Borrowed(self), exponent.into_rational_exponent())
    }
    /// returns `Some(log2(self))` if self is a power of 2, otherwise `None`
    pub fn to_integer_log2(&self) -> Option<i64> {
        let (numer, denom) = self.to_rational()?.into();
        if denom.is_one() {
            let retval = numer.floor_log2()?;
            if retval == numer.ceil_log2().expect("known to be positive") {
                return Some(retval.to_i64().expect("overflow"));
            }
        } else if numer.is_one() {
            let retval = denom.floor_log2().expect("known to be positive");
            if retval == denom.ceil_log2().expect("known to be positive") {
                return Some(-retval.to_i64().expect("overflow"));
            }
        }
        None
    }
    fn do_checked_floor_ceil_log2<
        FloorCeilLog2: Fn(&DyadicFractionInterval) -> Option<(i64, i64)>,
    >(
        value: Cow<Self>,
        floor_ceil_log2: FloorCeilLog2,
    ) -> Option<i64> {
        if !value.is_positive() {
            return None;
        }
        if let Some(retval) = value.to_integer_log2() {
            Some(retval)
        } else {
            let mut value = value.into_owned();
            let mut interval_shrinker = value
                .remove_zero_from_interval()
                .expect("known to be positive")
                .1;
            loop {
                let (retval_lower_bound, retval_upper_bound) =
                    floor_ceil_log2(&interval_shrinker.interval).expect("known to be positive");
                if retval_lower_bound == retval_upper_bound {
                    return Some(retval_lower_bound);
                }
                interval_shrinker.shrink();
            }
        }
    }
    /// returns `Some(floor(log2(self)))` if `self` is positive, otherwise `None`
    pub fn into_checked_floor_log2(self) -> Option<i64> {
        Self::do_checked_floor_ceil_log2(Cow::Owned(self), DyadicFractionInterval::floor_log2)
    }
    /// returns `Some(floor(log2(self)))` if `self` is positive, otherwise `None`
    pub fn checked_floor_log2(&self) -> Option<i64> {
        Self::do_checked_floor_ceil_log2(Cow::Borrowed(self), DyadicFractionInterval::floor_log2)
    }
    /// returns `Some(ceil(log2(self)))` if `self` is positive, otherwise `None`
    pub fn into_checked_ceil_log2(self) -> Option<i64> {
        Self::do_checked_floor_ceil_log2(Cow::Owned(self), DyadicFractionInterval::ceil_log2)
    }
    /// returns `Some(floor(log2(self)))` if `self` is positive, otherwise `None`
    pub fn checked_ceil_log2(&self) -> Option<i64> {
        Self::do_checked_floor_ceil_log2(Cow::Borrowed(self), DyadicFractionInterval::ceil_log2)
    }
}

fn neg(value: Cow<RealAlgebraicNumber>) -> RealAlgebraicNumber {
    let degree_is_odd = value.degree().is_odd();
    fn do_neg<I: Iterator<Item = BigInt>>(
        iter: I,
        degree_is_odd: bool,
        negated_interval: DyadicFractionInterval,
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
        RealAlgebraicNumber::new_unchecked(minimal_polynomial, negated_interval)
    }
    match value {
        Cow::Borrowed(value) => do_neg(
            value.minimal_polynomial().iter(),
            degree_is_odd,
            -value.interval(),
        ),
        Cow::Owned(RealAlgebraicNumber {
            data:
                RealAlgebraicNumberData {
                    minimal_polynomial,
                    interval,
                },
        }) => do_neg(minimal_polynomial.into_iter(), degree_is_odd, -interval),
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
}

impl Add<BigInt> for EvalPoint {
    type Output = Self;
    fn add(self, rhs: BigInt) -> Self {
        EvalPoint(self.0 + Polynomial::from(rhs))
    }
}

impl Mul<&'_ EvalPoint> for EvalPoint {
    type Output = Self;
    fn mul(self, rhs: &Self) -> Self {
        EvalPoint(self.0 * &rhs.0)
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

trait RootSelector: Sized {
    fn get_interval(&self) -> DyadicFractionInterval;
    fn shrink_interval(&mut self);
    fn select_root(mut self, polynomial: Polynomial<BigInt>) -> RealAlgebraicNumber {
        let mut factors: Vec<ResultFactor> = polynomial
            .factor()
            .polynomial_factors
            .into_iter()
            .map(|factor| ResultFactor {
                primitive_sturm_sequence: factor.polynomial.into_primitive_sturm_sequence(),
            })
            .collect();
        let mut factors_temp = Vec::with_capacity(factors.len());
        loop {
            let interval = self.get_interval();
            let (lower_bound, upper_bound) = interval.to_ratio_range();
            mem::swap(&mut factors, &mut factors_temp);
            factors.clear();
            let mut roots_left = 0;
            for factor in factors_temp.drain(..) {
                let lower_bound_sign_changes = sign_changes_at(
                    &factor.primitive_sturm_sequence,
                    ValueOrInfinity::Value(&lower_bound),
                );
                if lower_bound_sign_changes.is_root {
                    return lower_bound.into();
                }
                let upper_bound_sign_changes = sign_changes_at(
                    &factor.primitive_sturm_sequence,
                    ValueOrInfinity::Value(&upper_bound),
                );
                if upper_bound_sign_changes.is_root {
                    return upper_bound.into();
                }
                if lower_bound_sign_changes.sign_change_count
                    != upper_bound_sign_changes.sign_change_count
                {
                    let num_roots = distance(
                        lower_bound_sign_changes.sign_change_count,
                        upper_bound_sign_changes.sign_change_count,
                    );
                    roots_left += num_roots;
                    factors.push(factor);
                }
            }
            if roots_left <= 1 {
                break RealAlgebraicNumber::new_unchecked(
                    factors.remove(0).into_factor(),
                    interval,
                );
            }
            self.shrink_interval();
        }
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
        if rhs.is_zero() {
            return;
        }
        if self.is_zero() {
            *self = rhs;
            return;
        }
        let resultant_lhs: Polynomial<Polynomial<BigInt>> = self
            .minimal_polynomial()
            .iter()
            .map(Polynomial::from)
            .collect();
        let eval_point = EvalPoint::add_eval_point();
        let resultant_rhs = rhs
            .minimal_polynomial()
            .eval_generic(eval_point, EvalPoint::zero())
            .0;
        let resultant = resultant_lhs.resultant(resultant_rhs);
        struct AddRootSelector<'a> {
            lhs_interval_shrinker: IntervalShrinker<'a>,
            rhs_interval_shrinker: IntervalShrinker<'a>,
        }
        impl RootSelector for AddRootSelector<'_> {
            fn get_interval(&self) -> DyadicFractionInterval {
                &*self.lhs_interval_shrinker.interval + &*self.rhs_interval_shrinker.interval
            }
            fn shrink_interval(&mut self) {
                self.lhs_interval_shrinker.shrink();
                self.rhs_interval_shrinker.shrink();
            }
        }
        let lhs_interval_shrinker = self.interval_shrinker();
        let rhs_interval_shrinker = rhs.interval_shrinker();
        *self = AddRootSelector {
            lhs_interval_shrinker,
            rhs_interval_shrinker,
        }
        .select_root(resultant);
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
    static ref NEGATIVE_ONE: RealAlgebraicNumber = (-1).into();
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

impl One for RealAlgebraicNumber {
    fn one() -> Self {
        ONE.clone()
    }
    #[inline]
    fn is_one(&self) -> bool {
        self.minimal_polynomial() == ONE.minimal_polynomial()
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

#[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
pub struct RealAlgebraicNumberParseError {
    private: (),
}

impl fmt::Display for RealAlgebraicNumberParseError {
    fn fmt(&self, _f: &mut fmt::Formatter) -> fmt::Result {
        unimplemented!()
    }
}

impl Error for RealAlgebraicNumberParseError {}

impl Num for RealAlgebraicNumber {
    type FromStrRadixErr = RealAlgebraicNumberParseError;
    fn from_str_radix(_str: &str, _radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        unimplemented!()
    }
}

impl Signed for RealAlgebraicNumber {
    fn abs(&self) -> Self {
        if self.is_negative() {
            -self
        } else {
            self.clone()
        }
    }

    fn abs_sub(&self, other: &Self) -> Self {
        let difference = self - other;
        if difference.is_negative() {
            Self::zero()
        } else {
            difference
        }
    }

    /// Returns the sign of the number.
    ///
    /// * `0` if the number is zero
    /// * `1` if the number is positive
    /// * `-1` if the number is negative
    fn signum(&self) -> Self {
        match self.cmp_with_zero() {
            Ordering::Equal => Self::zero(),
            Ordering::Greater => Self::one(),
            Ordering::Less => -Self::one(),
        }
    }

    fn is_positive(&self) -> bool {
        self.cmp_with_zero() == Ordering::Greater
    }

    fn is_negative(&self) -> bool {
        self.cmp_with_zero() == Ordering::Less
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
        (self - rhs).cmp_with_zero()
    }
}

impl MulAssign for RealAlgebraicNumber {
    fn mul_assign(&mut self, mut rhs: RealAlgebraicNumber) {
        #![allow(clippy::suspicious_op_assign_impl)] // we need to use other operators
        if self.is_rational() && rhs.is_rational() {
            *self = (self.to_rational().expect("known to be rational")
                * rhs.to_rational().expect("known to be rational"))
            .into();
            return;
        }
        if self.is_zero() || rhs.is_zero() {
            self.set_zero();
            return;
        }
        if rhs.is_one() {
            return;
        }
        if self.is_one() {
            *self = rhs;
            return;
        }
        let resultant_lhs: Polynomial<Polynomial<BigInt>> = self
            .minimal_polynomial()
            .iter()
            .enumerate()
            .rev()
            .map(|(power, coefficient)| Polynomial::make_monomial(coefficient, power))
            .collect();
        let resultant_rhs: Polynomial<Polynomial<BigInt>> = rhs
            .minimal_polynomial()
            .iter()
            .map(Polynomial::from)
            .collect();
        let resultant = resultant_lhs.resultant(resultant_rhs);
        struct MulRootSelector<'a> {
            lhs_interval_shrinker: IntervalShrinker<'a>,
            rhs_interval_shrinker: IntervalShrinker<'a>,
        }
        impl RootSelector for MulRootSelector<'_> {
            fn get_interval(&self) -> DyadicFractionInterval {
                &*self.lhs_interval_shrinker.interval * &*self.rhs_interval_shrinker.interval
            }
            fn shrink_interval(&mut self) {
                self.lhs_interval_shrinker.shrink();
                self.rhs_interval_shrinker.shrink();
            }
        }
        let lhs_interval_shrinker = self.interval_shrinker();
        let rhs_interval_shrinker = rhs.interval_shrinker();
        *self = MulRootSelector {
            lhs_interval_shrinker,
            rhs_interval_shrinker,
        }
        .select_root(resultant);
    }
}

impl MulAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    fn mul_assign(&mut self, rhs: &RealAlgebraicNumber) {
        *self *= rhs.clone();
    }
}

impl Mul for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn mul(mut self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self *= rhs;
        self
    }
}

impl Mul<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn mul(mut self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self *= rhs;
        self
    }
}

impl Mul<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn mul(self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().mul(rhs)
    }
}

impl<'a, 'b> Mul<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn mul(self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().mul(rhs)
    }
}

impl ExactDivAssign for RealAlgebraicNumber {
    fn checked_exact_div_assign(&mut self, rhs: RealAlgebraicNumber) -> Result<(), ()> {
        self.checked_exact_div_assign(&rhs)
    }
}

impl ExactDivAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    fn checked_exact_div_assign(&mut self, rhs: &RealAlgebraicNumber) -> Result<(), ()> {
        self.mul_assign(&rhs.checked_recip().ok_or(())?);
        Ok(())
    }
}

impl AlwaysExactDiv<RealAlgebraicNumber> for RealAlgebraicNumber {}
impl AlwaysExactDiv<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {}
impl AlwaysExactDiv<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {}
impl<'a, 'b> AlwaysExactDiv<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {}
impl AlwaysExactDivAssign<RealAlgebraicNumber> for RealAlgebraicNumber {}
impl AlwaysExactDivAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {}

impl ExactDiv for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn checked_exact_div(mut self, rhs: RealAlgebraicNumber) -> Option<RealAlgebraicNumber> {
        self.checked_exact_div_assign(rhs).ok()?;
        Some(self)
    }
}

impl ExactDiv<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn checked_exact_div(mut self, rhs: &RealAlgebraicNumber) -> Option<RealAlgebraicNumber> {
        self.checked_exact_div_assign(rhs).ok()?;
        Some(self)
    }
}

impl ExactDiv<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn checked_exact_div(self, rhs: RealAlgebraicNumber) -> Option<RealAlgebraicNumber> {
        self.clone().checked_exact_div(rhs)
    }
}

impl<'a, 'b> ExactDiv<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn checked_exact_div(self, rhs: &RealAlgebraicNumber) -> Option<RealAlgebraicNumber> {
        self.clone().checked_exact_div(rhs)
    }
}

impl DivAssign<RealAlgebraicNumber> for RealAlgebraicNumber {
    fn div_assign(&mut self, rhs: RealAlgebraicNumber) {
        self.exact_div_assign(rhs);
    }
}

impl DivAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    fn div_assign(&mut self, rhs: &RealAlgebraicNumber) {
        self.exact_div_assign(rhs);
    }
}

impl Div<RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn div(self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.exact_div(rhs)
    }
}

impl Div<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn div(self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.exact_div(rhs)
    }
}

impl Div<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn div(self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.exact_div(rhs)
    }
}

impl<'a, 'b> Div<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn div(self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.exact_div(rhs)
    }
}

impl RemAssign<RealAlgebraicNumber> for RealAlgebraicNumber {
    fn rem_assign(&mut self, rhs: RealAlgebraicNumber) {
        self.rem_assign(&rhs)
    }
}

impl RemAssign<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    fn rem_assign(&mut self, rhs: &RealAlgebraicNumber) {
        *self -= (&*self / rhs).trunc() * rhs;
    }
}

impl Rem<RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn rem(mut self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.rem_assign(rhs);
        self
    }
}

impl Rem<RealAlgebraicNumber> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn rem(self, rhs: RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().rem(rhs)
    }
}

impl Rem<&'_ RealAlgebraicNumber> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn rem(mut self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.rem_assign(rhs);
        self
    }
}

impl<'a, 'b> Rem<&'a RealAlgebraicNumber> for &'b RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn rem(self, rhs: &RealAlgebraicNumber) -> RealAlgebraicNumber {
        self.clone().rem(rhs)
    }
}

impl<E: IntoRationalExponent> Pow<E> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn pow(self, exponent: E) -> RealAlgebraicNumber {
        self.checked_into_pow(exponent.into_rational_exponent())
            .expect("checked_pow failed")
    }
}

impl<E: IntoRationalExponent> Pow<E> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn pow(self, exponent: E) -> RealAlgebraicNumber {
        self.checked_pow(exponent.into_rational_exponent())
            .expect("checked_pow failed")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::{test_checked_op_helper, test_op_helper};
    use num_integer::Roots;

    fn r(n: i128, d: i128) -> Ratio<BigInt> {
        Ratio::new(BigInt::from(n), BigInt::from(d))
    }

    fn ri(v: i128) -> Ratio<BigInt> {
        Ratio::from(BigInt::from(v))
    }

    fn bi(v: i128) -> BigInt {
        BigInt::from(v)
    }

    fn p(poly: &[i128]) -> Polynomial<BigInt> {
        poly.iter().copied().map(BigInt::from).collect()
    }

    fn make_sqrt(v: i128, interval: DyadicFractionInterval) -> RealAlgebraicNumber {
        let sqrt = v.sqrt();
        assert_ne!(
            sqrt * sqrt,
            v,
            "make_sqrt doesn't work with perfect squares"
        );
        RealAlgebraicNumber::new_unchecked(p(&[-v, 0, 1]), interval)
    }

    #[test]
    fn test_debug() {
        fn test_case(poly: Polynomial<BigInt>, interval: DyadicFractionInterval, expected: &str) {
            let real_algebraic_number = RealAlgebraicNumber::new_unchecked(poly, interval);
            let string = format!("{:?}", real_algebraic_number);
            assert_eq!(&string, expected);
        }

        test_case(
            p(&[0, 1]),
            DyadicFractionInterval::from_int(bi(0), 0),
            "RealAlgebraicNumber { minimal_polynomial: 0 + 1*X, interval: DyadicFractionInterval { lower_bound_numer: 0, upper_bound_numer: 0, log2_denom: 0 } }",
        );

        test_case(
            p(&[-2, 0, 1]),
            DyadicFractionInterval::from_int_range(bi(1), bi(2), 0),
            "RealAlgebraicNumber { minimal_polynomial: -2 + 0*X + 1*X^2, interval: DyadicFractionInterval { lower_bound_numer: 1, upper_bound_numer: 2, log2_denom: 0 } }",
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
            DyadicFractionInterval::from_ratio_range(r(22_46827, 100_000), r(22_4683, 10_000), 32),
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
             interval: DyadicFractionInterval { \
             lower_bound_numer: 96500484847, \
             upper_bound_numer: 96500613697, \
             log2_denom: 32 } }",
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
            RealAlgebraicNumber::new_unchecked(
                p(&[-1, -2, 1]),
                DyadicFractionInterval::from_int_range(bi(2), bi(3), 0),
            ),
            RealAlgebraicNumberData {
                minimal_polynomial: p(&[-1, 2, 1]),
                interval: DyadicFractionInterval::from_int_range(bi(-3), bi(-2), 0),
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
    fn test_cmp_with_zero() {
        fn test_case<V: Into<RealAlgebraicNumber>>(value: V, expected: Ordering) {
            let value = value.into();
            println!("value: {:?}", value);
            println!("expected: {:?}", expected);
            let result = value.cmp_with_zero();
            println!("result: {:?}", result);
            assert_eq!(expected, result);
        }
        test_case(0, Ordering::Equal);
        test_case(1, Ordering::Greater);
        test_case(-1, Ordering::Less);
        test_case(r(-1, 12), Ordering::Less);
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 1]),
                DyadicFractionInterval::from_int_range(bi(-1000), bi(1000), 0),
            ),
            Ordering::Less,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[-1, 1, 1]),
                DyadicFractionInterval::from_int_range(bi(-1), bi(1000), 0),
            ),
            Ordering::Greater,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[-3, 1, 1]),
                DyadicFractionInterval::from_int_range(bi(-1000), bi(1), 0),
            ),
            Ordering::Less,
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
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(8, DyadicFractionInterval::from_int_range(bi(1), bi(3), 0)),
        );
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(3, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 0, -10, 0, 1]),
                DyadicFractionInterval::from_int_range(bi(3), bi(4), 0),
            ),
        );
        test_case(
            // sqrt(5) - sqrt(3) + 1
            RealAlgebraicNumber::new_unchecked(
                p(&[-11, 28, -10, -4, 1]),
                DyadicFractionInterval::from_int_range(bi(1), bi(2), 0),
            ),
            // sqrt(3) - sqrt(5) + 1 / 2
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 248, -232, -32, 16]),
                DyadicFractionInterval::from_int_range(bi(-1), bi(0), 0),
            ),
            r(3, 2),
        );
    }

    #[test]
    fn test_sub() {
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
                |l, r| *l -= r,
                |l, r| *l -= r,
                |l, r| l - r,
                |l, r| l - r,
                |l, r| l - r,
                |l, r| l - r,
            );
        }
        test_case(1, 2, 1 - 2);
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(-2), bi(-1), 0)),
            make_sqrt(8, DyadicFractionInterval::from_int_range(bi(1), bi(3), 0)),
        );
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(3, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 0, -10, 0, 1]),
                DyadicFractionInterval::from_int_range(bi(-1), bi(0), 0),
            ),
        );
    }

    #[test]
    fn test_floor_ceil() {
        fn test_case<V: Into<RealAlgebraicNumber>, F: Into<BigInt>, C: Into<BigInt>>(
            value: V,
            expected_floor: F,
            expected_ceil: C,
        ) {
            let value = value.into();
            println!("value: {:?}", value);
            let expected_floor = expected_floor.into();
            println!("expected_floor: {}", expected_floor);
            let expected_ceil = expected_ceil.into();
            println!("expected_ceil: {}", expected_ceil);
            let floor = value.to_integer_floor();
            println!("floor: {}", floor);
            let ceil = value.into_integer_ceil();
            println!("ceil: {}", ceil);
            assert!(expected_floor == floor);
            assert!(expected_ceil == ceil);
        }
        test_case(1, 1, 1);
        test_case(r(6, 5), 1, 2);
        test_case(r(4, 5), 0, 1);
        test_case(r(-1, 5), -1, 0);
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            1,
            2,
        );
        test_case(
            make_sqrt(
                2_000_000,
                DyadicFractionInterval::from_int_range(bi(1000), bi(2000), 0),
            ),
            1_414,
            1_415,
        );
        test_case(
            make_sqrt(
                5_00000_00000,
                DyadicFractionInterval::from_int_range(bi(1_00000), bi(3_00000), 0),
            ),
            2_23606,
            2_23607,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 0, -10, 0, 1]),
                DyadicFractionInterval::from_int_range(bi(-1), bi(0), 0),
            ),
            -1,
            0,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 3, 2, 1]),
                DyadicFractionInterval::from_int_range(bi(-1000), bi(1000), 0),
            ),
            -1,
            0,
        );
    }

    #[test]
    fn test_mul() {
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
                |l, r| *l *= r,
                |l, r| *l *= r,
                |l, r| l * r,
                |l, r| l * r,
                |l, r| l * r,
                |l, r| l * r,
            );
        }
        test_case(1, 0, 0);
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            0,
            0,
        );
        test_case(
            0,
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            0,
        );
        test_case(1, 2, 2);
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(-2), bi(-1), 0)),
            -2,
        );
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(3, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(6, DyadicFractionInterval::from_int_range(bi(1), bi(10), 0)),
        );
    }

    #[test]
    fn test_div() {
        fn test_case<A: Into<RealAlgebraicNumber>, B: Into<RealAlgebraicNumber>>(
            a: A,
            b: B,
            expected: Option<RealAlgebraicNumber>,
        ) {
            let a = a.into();
            println!("a: {:?}", a);
            let b = b.into();
            println!("b: {:?}", b);
            println!("expected: {:?}", expected);
            test_checked_op_helper(
                a,
                b,
                &expected,
                |l, r| l.checked_exact_div_assign(r),
                |l, r| l.checked_exact_div_assign(r),
                |l, r| l.checked_exact_div(r),
                |l, r| l.checked_exact_div(r),
                |l, r| l.checked_exact_div(r),
                |l, r| l.checked_exact_div(r),
            );
        }
        test_case(1, 0, None);
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            0,
            None,
        );
        test_case(
            0,
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            Some(0.into()),
        );
        test_case(1, 2, Some(r(1, 2).into()));
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(-2), bi(-1), 0)),
            Some((-1).into()),
        );
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            make_sqrt(3, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            Some(RealAlgebraicNumber::new_unchecked(
                p(&[-2, 0, 3]),
                DyadicFractionInterval::from_int_range(bi(0), bi(1), 0),
            )),
        );
    }

    #[test]
    fn test_pow() {
        fn test_case<B: Into<RealAlgebraicNumber>, E: Into<Ratio<BigInt>>>(
            base: B,
            exponent: E,
            expected: Option<RealAlgebraicNumber>,
        ) {
            let base = base.into();
            let exponent = exponent.into();
            println!("base: {:?}", base);
            println!("exponent: {}", exponent);
            println!("expected: {:?}", expected);
            let result = base.checked_into_pow(exponent);
            println!("result: {:?}", result);
            assert!(result == expected);
        }
        test_case(0, ri(0), None);
        test_case(1, ri(0), Some(1.into()));
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            ri(0),
            Some(1.into()),
        );
        test_case(r(2, 3), ri(1), Some(r(2, 3).into()));
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            ri(1),
            Some(make_sqrt(
                2,
                DyadicFractionInterval::from_int_range(bi(1), bi(2), 0),
            )),
        );
        test_case(r(2, 3), ri(-1), Some(r(3, 2).into()));
        test_case(r(-2, 3), ri(-1), Some(r(-3, 2).into()));
        test_case(0, ri(-1), None);
        test_case(0, ri(-2), None);
        test_case(0, ri(2), Some(0.into()));
        test_case(1, ri(2), Some(1.into()));
        test_case(1, r(2, 3), Some(1.into()));
        test_case(-1, ri(3), Some((-1).into()));
        test_case(-1, ri(1234), Some(1.into()));
        test_case(-1, r(1, 2), None);
        test_case(-2, r(1, 2), None);
        test_case(-2, ri(2), Some(4.into()));
        test_case(-2, ri(3), Some((-8).into()));
        test_case(r(-2, 3), ri(3), Some(r(-8, 27).into()));
        test_case(r(-2, 3), ri(-3), Some(r(-27, 8).into()));
        test_case(
            make_sqrt(8, DyadicFractionInterval::from_int_range(bi(2), bi(3), 0)),
            r(-2, 3),
            Some(r(1, 2).into()),
        );
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            ri(2),
            Some(2.into()),
        );
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            ri(-2),
            Some(r(1, 2).into()),
        );
        test_case(
            make_sqrt(5, DyadicFractionInterval::from_int_range(bi(1), bi(5), 0)),
            r(5, 3),
            Some(RealAlgebraicNumber::new_unchecked(
                p(&[-3125, 0, 0, 0, 0, 0, 1]),
                DyadicFractionInterval::from_int_range(bi(1), bi(20), 0),
            )),
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[5, -20, 16]),
                DyadicFractionInterval::from_ratio_range(ri(0), r(1, 2), 1),
            ),
            r(1, 2),
            Some(RealAlgebraicNumber::new_unchecked(
                p(&[5, 0, -20, 0, 16]),
                DyadicFractionInterval::from_ratio_range(r(1, 2), r(3, 4), 2),
            )),
        );
    }

    #[test]
    fn test_integer_floor_ceil_log2() {
        fn test_case<V: Into<RealAlgebraicNumber>>(
            value: V,
            expected_integer_log2: Option<i64>,
            expected_floor_log2: Option<i64>,
            expected_ceil_log2: Option<i64>,
        ) {
            let value = value.into();
            println!("value: {:?}", value);
            println!("expected_integer_log2: {:?}", expected_integer_log2);
            println!("expected_floor_log2: {:?}", expected_floor_log2);
            println!("expected_ceil_log2: {:?}", expected_ceil_log2);
            let integer_log2 = value.to_integer_log2();
            println!("integer_log2: {:?}", integer_log2);
            let floor_log2 = value.checked_floor_log2();
            println!("floor_log2: {:?}", floor_log2);
            let ceil_log2 = value.into_checked_ceil_log2();
            println!("ceil_log2: {:?}", ceil_log2);
            assert!(expected_integer_log2 == integer_log2);
            assert!(expected_floor_log2 == floor_log2);
            assert!(expected_ceil_log2 == ceil_log2);
        }
        test_case(1, Some(0), Some(0), Some(0));
        test_case(16, Some(4), Some(4), Some(4));
        test_case(r(1, 16), Some(-4), Some(-4), Some(-4));
        test_case(r(6, 5), None, Some(0), Some(1));
        test_case(r(-6, 5), None, None, None);
        test_case(0, None, None, None);
        test_case(r(4, 5), None, Some(-1), Some(0));
        test_case(r(-1, 5), None, None, None);
        test_case(
            make_sqrt(2, DyadicFractionInterval::from_int_range(bi(1), bi(2), 0)),
            None,
            Some(0),
            Some(1),
        );
        test_case(
            make_sqrt(
                2_000_000,
                DyadicFractionInterval::from_int_range(bi(1000), bi(2000), 0),
            ),
            None,
            Some(10),
            Some(11),
        );
        test_case(
            make_sqrt(
                200_000_000_000_000_000_000_000_000_000,
                DyadicFractionInterval::from_int_range(
                    bi(1000),
                    bi(200_000_000_000_000_000_000),
                    0,
                ),
            ),
            None,
            Some(48),
            Some(49),
        );
        test_case(
            make_sqrt(
                5_00000_00000,
                DyadicFractionInterval::from_int_range(bi(1_00000), bi(3_00000), 0),
            ),
            None,
            Some(17),
            Some(18),
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 0, -10, 0, 1]),
                DyadicFractionInterval::from_int_range(bi(-1), bi(0), 0),
            ),
            None,
            None,
            None,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[1, 0, -10, 0, 1]),
                DyadicFractionInterval::from_int_range(bi(0), bi(1), 0),
            ),
            None,
            Some(-2),
            Some(-1),
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(
                p(&[-1, 3, -2, 1]),
                DyadicFractionInterval::from_int_range(bi(-1000), bi(1000), 0),
            ),
            None,
            Some(-2),
            Some(-1),
        );
    }
}
