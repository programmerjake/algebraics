// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::polynomial::Polynomial;
use crate::traits::AlwaysExactDiv;
use crate::traits::AlwaysExactDivAssign;
use crate::traits::ExactDiv;
use crate::traits::ExactDivAssign;
use crate::traits::FloorLog2;
use crate::util::DebugAsDisplay;
use crate::util::Sign;
use num_bigint::BigInt;
use num_bigint::BigUint;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::Num;
use num_traits::One;
use num_traits::Pow;
use num_traits::Signed;
use num_traits::ToPrimitive;
use num_traits::Zero;
use std::borrow::Cow;
use std::cmp::Ordering;
use std::error::Error;
use std::fmt;
use std::mem;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Deref;
use std::ops::DerefMut;
use std::ops::Div;
use std::ops::DivAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Rem;
use std::ops::RemAssign;
use std::ops::Sub;
use std::ops::SubAssign;

#[derive(Clone, Eq, PartialEq, Hash)]
pub struct RealAlgebraicNumberData {
    pub minimal_polynomial: Polynomial<BigInt>,
    // FIXME: switch to using DyadicFractionInterval instead of rational bounds
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
    pub fn into_integer_floor(mut self) -> BigInt {
        if let Some(ratio) = self.to_rational() {
            ratio.floor().to_integer()
        } else {
            let mut bounds_shrinker = self.bounds_shrinker();
            loop {
                let lower_bound_floor = bounds_shrinker.lower_bound.floor();
                let upper_bound_floor = bounds_shrinker.upper_bound.floor();
                if lower_bound_floor == upper_bound_floor {
                    return lower_bound_floor.to_integer();
                }
                bounds_shrinker.shrink();
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
            let mut bounds_shrinker = self.bounds_shrinker();
            loop {
                let lower_bound_floor = bounds_shrinker.lower_bound.floor();
                let upper_bound_floor = bounds_shrinker.upper_bound.floor();
                if lower_bound_floor == upper_bound_floor {
                    return self - RealAlgebraicNumber::from(lower_bound_floor);
                }
                bounds_shrinker.shrink();
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
        } else if self.lower_bound().is_positive() {
            Ordering::Greater
        } else if self.upper_bound().is_negative() {
            Ordering::Less
        } else if let Some(value) = self.to_rational() {
            value.cmp(&Ratio::zero())
        } else {
            let primitive_sturm_sequence = self.minimal_polynomial().to_primitive_sturm_sequence();
            let lower_bound_sign_changes = sign_changes_at(
                &primitive_sturm_sequence,
                ValueOrInfinity::Value(self.lower_bound()),
            );
            assert!(!lower_bound_sign_changes.is_root);
            let upper_bound_sign_changes = sign_changes_at(
                &primitive_sturm_sequence,
                ValueOrInfinity::Value(self.upper_bound()),
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
    pub fn checked_recip(&self) -> Option<Self> {
        if let Some(value) = self.to_rational() {
            if value.is_zero() {
                return None;
            }
            return Some(value.recip().into());
        }
        let sign = match self.cmp_with_zero() {
            Ordering::Equal => unreachable!("already checked for zero"),
            Ordering::Less => Sign::Negative,
            Ordering::Greater => Sign::Positive,
        };
        let mut value = self.clone();
        match sign {
            Sign::Negative => {
                if value.upper_bound().is_positive() {
                    value.data.upper_bound.set_zero();
                }
            }
            Sign::Positive => {
                if value.lower_bound().is_negative() {
                    value.data.lower_bound.set_zero();
                }
            }
        }
        let mut bounds_shrinker = value.bounds_shrinker();
        while bounds_shrinker.lower_bound.is_zero() || bounds_shrinker.upper_bound.is_zero() {
            bounds_shrinker.shrink();
        }
        let RealAlgebraicNumberData {
            minimal_polynomial,
            lower_bound,
            upper_bound,
        } = value.into_data();
        let (lower_bound, upper_bound) = (upper_bound.recip(), lower_bound.recip());
        let minimal_polynomial = minimal_polynomial.into_iter().rev().collect();
        Some(RealAlgebraicNumber::new_unchecked(
            minimal_polynomial,
            lower_bound,
            upper_bound,
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
        println!("checked_pow:");
        println!("base: {:?}", base);
        println!("exponent: {}", exponent);
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
            println!("exponent_sign: {:?}", exponent_sign);
            let (exponent_numer, exponent_denom) = exponent.abs().into();
            let exponent_numer = exponent_numer
                .to_usize()
                .expect("exponent numerator too big");
            println!("exponent_numer: {}", exponent_numer);
            let exponent_denom = exponent_denom
                .to_usize()
                .expect("exponent denominator too big");
            println!("exponent_denom: {}", exponent_denom);
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
            println!("base: {:?}", base);
            let resultant_lhs: Polynomial<Polynomial<BigInt>> = base
                .minimal_polynomial()
                .iter()
                .map(Polynomial::from)
                .collect();
            println!("resultant_lhs: {}", resultant_lhs);
            let resultant_rhs: Polynomial<Polynomial<BigInt>> =
                Polynomial::make_monomial(-Polynomial::<BigInt>::one(), exponent_numer)
                    + Polynomial::make_monomial(BigInt::one(), exponent_denom);
            println!("resultant_rhs: {}", resultant_rhs);
            let resultant = resultant_lhs.resultant(resultant_rhs);
            println!("resultant: {}", resultant);
            struct PowRootSelector<'a> {
                base: BoundsShrinker<'a>,
                exponent: Ratio<BigInt>,
                result_sign: Sign,
            }
            impl RootSelector for PowRootSelector<'_> {
                fn get_bounds(&self) -> Bounds<Ratio<BigInt>> {
                    let bounds = if self.base.lower_bound.is_positive() {
                        let lower_bound = self.base.lower_bound.clone();
                        let upper_bound = self.base.upper_bound.clone();
                        Bounds {
                            lower_bound,
                            upper_bound,
                        }
                    } else if self.base.upper_bound.is_negative() {
                        let lower_bound = -&*self.base.upper_bound;
                        let upper_bound = -&*self.base.lower_bound;
                        Bounds {
                            lower_bound,
                            upper_bound,
                        }
                    } else {
                        let lower_bound = Ratio::zero();
                        let upper_bound =
                            self.base.lower_bound.abs().max(self.base.upper_bound.abs());
                        Bounds {
                            lower_bound,
                            upper_bound,
                        }
                    };
                    let bounds = pow_bounds(bounds, &self.exponent);
                    match self.result_sign {
                        Sign::Positive => bounds,
                        Sign::Negative => Bounds {
                            lower_bound: -bounds.upper_bound,
                            upper_bound: -bounds.lower_bound,
                        },
                    }
                }
                fn shrink_bounds(&mut self) {
                    self.base.shrink();
                }
            }
            Some(
                PowRootSelector {
                    base: base.bounds_shrinker(),
                    exponent: Ratio::new(exponent_numer.into(), exponent_denom.into()),
                    result_sign,
                }
                .select_root(resultant),
            )
        }
    }
    pub fn checked_into_pow<E: Into<Ratio<BigInt>>>(self, exponent: E) -> Option<Self> {
        Self::checked_pow_impl(Cow::Owned(self), exponent.into())
    }
    pub fn checked_pow<E: Into<Ratio<BigInt>>>(&self, exponent: E) -> Option<Self> {
        Self::checked_pow_impl(Cow::Borrowed(self), exponent.into())
    }
}

#[derive(Clone)]
struct DyadicFractionBounds {
    log2_denom: usize,
    lower_bound_numer: BigInt,
    upper_bound_numer: BigInt,
}

impl fmt::Debug for DyadicFractionBounds {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("DyadicFractionBounds")
            .field("log2_denom", &self.log2_denom)
            .field(
                "lower_bound_numer",
                &DebugAsDisplay(&self.lower_bound_numer),
            )
            .field(
                "upper_bound_numer",
                &DebugAsDisplay(&self.upper_bound_numer),
            )
            .finish()
    }
}

impl From<Bounds<Ratio<BigInt>>> for DyadicFractionBounds {
    fn from(bounds: Bounds<Ratio<BigInt>>) -> Self {
        let (mut lower_bound_numer, lower_bound_denom) = bounds.lower_bound.into();
        let (mut upper_bound_numer, upper_bound_denom) = bounds.upper_bound.into();
        let log2_denom = lower_bound_denom.bits().max(upper_bound_denom.bits());
        lower_bound_numer <<= log2_denom;
        upper_bound_numer <<= log2_denom;
        let lower_bound_numer = Ratio::new(lower_bound_numer, lower_bound_denom)
            .floor()
            .to_integer();
        let upper_bound_numer = Ratio::new(upper_bound_numer, upper_bound_denom)
            .ceil()
            .to_integer();
        Self {
            log2_denom,
            lower_bound_numer,
            upper_bound_numer,
        }
    }
}

impl From<DyadicFractionBounds> for Bounds<Ratio<BigInt>> {
    fn from(bounds: DyadicFractionBounds) -> Self {
        let denom = BigInt::one() << bounds.log2_denom;
        Bounds {
            lower_bound: Ratio::new(bounds.lower_bound_numer, denom.clone()),
            upper_bound: Ratio::new(bounds.upper_bound_numer, denom),
        }
    }
}

fn log2_bounds(bounds: Bounds<Ratio<BigInt>>) -> Bounds<Ratio<BigInt>> {
    println!("log2_bounds:");
    dbg!(&bounds);
    assert!(bounds.lower_bound.is_positive());
    assert!(bounds.lower_bound <= bounds.upper_bound);
    let bounds = DyadicFractionBounds::from(bounds);
    dbg!(&bounds);
    // FIXME: handle lower_bound rounding to zero
    // FIXME: handle passing in a precision to handle lower_bound == upper_bound
    let lower_bound_numer_floor_log2 = bounds.lower_bound_numer.floor_log2();
    let upper_bound_numer_floor_log2 = bounds.upper_bound_numer.floor_log2();

    unimplemented!();
}

fn exp2_bounds(bounds: Bounds<Ratio<BigInt>>) -> Bounds<Ratio<BigInt>> {
    assert!(bounds.lower_bound <= bounds.upper_bound);
    unimplemented!();
}

fn pow_bounds(
    mut bounds: Bounds<Ratio<BigInt>>,
    exponent: &Ratio<BigInt>,
) -> Bounds<Ratio<BigInt>> {
    assert!(!bounds.lower_bound.is_negative());
    assert!(exponent.is_positive());
    let lower_bound_is_zero = bounds.lower_bound.is_zero();
    if lower_bound_is_zero {
        if bounds.upper_bound.is_zero() {
            return bounds;
        }
        bounds.lower_bound = &bounds.upper_bound / BigInt::from(2);
    }
    bounds = log2_bounds(bounds);
    bounds.lower_bound *= exponent;
    bounds.upper_bound *= exponent;
    bounds = exp2_bounds(bounds);
    if lower_bound_is_zero {
        bounds.lower_bound.set_zero();
    }
    bounds
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

#[derive(Copy, Clone, PartialEq)]
struct Bounds<T> {
    lower_bound: T,
    upper_bound: T,
}

impl<T: fmt::Display> fmt::Debug for Bounds<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("Bounds")
            .field("lower_bound", &DebugAsDisplay(&self.lower_bound))
            .field("upper_bound", &DebugAsDisplay(&self.upper_bound))
            .finish()
    }
}

trait RootSelector: Sized {
    fn get_bounds(&self) -> Bounds<Ratio<BigInt>>;
    fn shrink_bounds(&mut self);
    fn select_root(mut self, polynomial: Polynomial<BigInt>) -> RealAlgebraicNumber {
        let mut factors: Vec<ResultFactor> = polynomial
            .factor()
            .polynomial_factors
            .into_iter()
            .map(|factor| ResultFactor {
                primitive_sturm_sequence: factor.polynomial.into_primitive_sturm_sequence(),
            })
            .collect();
        println!("factors: {:?}", factors);
        let mut factors_temp = Vec::with_capacity(factors.len());
        loop {
            let Bounds {
                lower_bound,
                upper_bound,
            } = self.get_bounds();
            println!("lower_bound: {}", lower_bound);
            println!("upper_bound: {}", upper_bound);
            mem::swap(&mut factors, &mut factors_temp);
            factors.clear();
            let mut roots_left = 0;
            for factor in factors_temp.drain(..) {
                dbg!(&factor);
                let lower_bound_sign_changes = sign_changes_at(
                    &factor.primitive_sturm_sequence,
                    ValueOrInfinity::Value(&lower_bound),
                );
                if lower_bound_sign_changes.is_root {
                    println!("found root: {}", lower_bound);
                    return lower_bound.into();
                }
                let upper_bound_sign_changes = sign_changes_at(
                    &factor.primitive_sturm_sequence,
                    ValueOrInfinity::Value(&upper_bound),
                );
                if upper_bound_sign_changes.is_root {
                    println!("found root: {}", upper_bound);
                    return upper_bound.into();
                }
                if lower_bound_sign_changes.sign_change_count
                    != upper_bound_sign_changes.sign_change_count
                {
                    println!("retained: {:?}", factor);
                    let num_roots = distance(
                        lower_bound_sign_changes.sign_change_count,
                        upper_bound_sign_changes.sign_change_count,
                    );
                    roots_left += dbg!(num_roots);
                    factors.push(factor);
                } else {
                    println!("discarded: {:?}", factor);
                }
            }
            if roots_left <= 1 {
                break RealAlgebraicNumber::new_unchecked(
                    factors.remove(0).into_factor(),
                    lower_bound,
                    upper_bound,
                );
            }
            self.shrink_bounds();
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
        struct AddRootShrinker<'a> {
            lhs_bounds_shrinker: BoundsShrinker<'a>,
            rhs_bounds_shrinker: BoundsShrinker<'a>,
        }
        impl RootSelector for AddRootShrinker<'_> {
            fn get_bounds(&self) -> Bounds<Ratio<BigInt>> {
                let lower_bound =
                    &*self.lhs_bounds_shrinker.lower_bound + &*self.rhs_bounds_shrinker.lower_bound;
                let upper_bound =
                    &*self.lhs_bounds_shrinker.upper_bound + &*self.rhs_bounds_shrinker.upper_bound;
                Bounds {
                    lower_bound,
                    upper_bound,
                }
            }
            fn shrink_bounds(&mut self) {
                self.lhs_bounds_shrinker.shrink();
                self.rhs_bounds_shrinker.shrink();
            }
        }
        let lhs_bounds_shrinker = self.bounds_shrinker();
        let rhs_bounds_shrinker = rhs.bounds_shrinker();
        *self = AddRootShrinker {
            lhs_bounds_shrinker,
            rhs_bounds_shrinker,
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
pub enum RealAlgebraicNumberParseError {}

impl fmt::Display for RealAlgebraicNumberParseError {
    fn fmt(&self, _f: &mut fmt::Formatter) -> fmt::Result {
        match *self {}
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
        println!("mul_assign:");
        dbg!(&self);
        dbg!(&rhs);
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
        println!("resultant_lhs: {}", resultant_lhs);
        let resultant_rhs: Polynomial<Polynomial<BigInt>> = rhs
            .minimal_polynomial()
            .iter()
            .map(Polynomial::from)
            .collect();
        println!("resultant_rhs: {}", resultant_rhs);
        let resultant = resultant_lhs.resultant(resultant_rhs);
        println!("resultant: {}", resultant);
        struct MulRootShrinker<'a> {
            lhs_bounds_shrinker: BoundsShrinker<'a>,
            rhs_bounds_shrinker: BoundsShrinker<'a>,
        }
        impl RootSelector for MulRootShrinker<'_> {
            fn get_bounds(&self) -> Bounds<Ratio<BigInt>> {
                let mut bounds = [
                    &*self.lhs_bounds_shrinker.lower_bound * &*self.rhs_bounds_shrinker.lower_bound,
                    &*self.lhs_bounds_shrinker.lower_bound * &*self.rhs_bounds_shrinker.upper_bound,
                    &*self.lhs_bounds_shrinker.upper_bound * &*self.rhs_bounds_shrinker.lower_bound,
                    &*self.lhs_bounds_shrinker.upper_bound * &*self.rhs_bounds_shrinker.upper_bound,
                ];
                bounds.sort_unstable();
                let [lower_bound, _, _, upper_bound] = bounds;
                assert!(lower_bound <= upper_bound);
                Bounds {
                    lower_bound,
                    upper_bound,
                }
            }
            fn shrink_bounds(&mut self) {
                self.lhs_bounds_shrinker.shrink();
                self.rhs_bounds_shrinker.shrink();
            }
        }
        let lhs_bounds_shrinker = self.bounds_shrinker();
        let rhs_bounds_shrinker = rhs.bounds_shrinker();
        *self = MulRootShrinker {
            lhs_bounds_shrinker,
            rhs_bounds_shrinker,
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

impl<E: Into<Ratio<BigInt>>> Pow<E> for RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn pow(self, exponent: E) -> RealAlgebraicNumber {
        self.checked_into_pow(exponent).expect("checked_pow failed")
    }
}

impl<E: Into<Ratio<BigInt>>> Pow<E> for &'_ RealAlgebraicNumber {
    type Output = RealAlgebraicNumber;
    fn pow(self, exponent: E) -> RealAlgebraicNumber {
        self.checked_pow(exponent).expect("checked_pow failed")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::test_checked_op_helper;
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
            RealAlgebraicNumber::new_unchecked(p(&[1, 1]), ri(-1000), ri(1000)),
            Ordering::Less,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(p(&[-1, 1, 1]), ri(-1), ri(1000)),
            Ordering::Greater,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(p(&[-3, 1, 1]), ri(-1000), ri(1)),
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
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(2, ri(-2), ri(-1)),
            make_sqrt(8, ri(1), ri(3)),
        );
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(3, ri(1), ri(2)),
            RealAlgebraicNumber::new_unchecked(p(&[1, 0, -10, 0, 1]), ri(-1), ri(0)),
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
        test_case(make_sqrt(2, ri(1), ri(2)), 1, 2);
        test_case(make_sqrt(2_000_000, ri(1000), ri(2000)), 1_414, 1_415);
        test_case(
            make_sqrt(5_00000_00000, ri(1_00000), ri(3_00000)),
            2_23606,
            2_23607,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(p(&[1, 0, -10, 0, 1]), ri(-1), ri(0)),
            -1,
            0,
        );
        test_case(
            RealAlgebraicNumber::new_unchecked(p(&[1, 3, 2, 1]), ri(-1000), ri(1000)),
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
        test_case(make_sqrt(2, ri(1), ri(2)), 0, 0);
        test_case(0, make_sqrt(2, ri(1), ri(2)), 0);
        test_case(1, 2, 2);
        test_case(make_sqrt(2, ri(1), ri(2)), make_sqrt(2, ri(-2), ri(-1)), -2);
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(3, ri(1), ri(2)),
            make_sqrt(6, ri(1), ri(10)),
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
        test_case(make_sqrt(2, ri(1), ri(2)), 0, None);
        test_case(0, make_sqrt(2, ri(1), ri(2)), Some(0.into()));
        test_case(1, 2, Some(r(1, 2).into()));
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(2, ri(-2), ri(-1)),
            Some((-1).into()),
        );
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            make_sqrt(3, ri(1), ri(2)),
            Some(RealAlgebraicNumber::new_unchecked(
                p(&[-2, 0, 3]),
                ri(0),
                ri(1),
            )),
        );
    }

    #[test]
    fn test_log2_bounds() {
        fn test_case(input: Bounds<Ratio<BigInt>>, expected: Bounds<Ratio<BigInt>>) {
            println!("input: {:?}", input);
            println!("expected: {:?}", expected);
            let result = log2_bounds(input);
            println!("result: {:?}", result);
            assert!(expected == result);
        }
        test_case(
            Bounds {
                lower_bound: ri(1),
                upper_bound: ri(1),
            },
            Bounds {
                lower_bound: ri(0),
                upper_bound: ri(0),
            },
        );
        unimplemented!("add more test cases");
    }

    #[test]
    fn test_exp2_bounds() {
        fn test_case(input: Bounds<Ratio<BigInt>>, expected: Bounds<Ratio<BigInt>>) {
            println!("input: {:?}", input);
            println!("expected: {:?}", expected);
            let result = exp2_bounds(input);
            println!("result: {:?}", result);
            assert!(expected == result);
        }
        test_case(
            Bounds {
                lower_bound: ri(0),
                upper_bound: ri(0),
            },
            Bounds {
                lower_bound: ri(1),
                upper_bound: ri(1),
            },
        );
        unimplemented!("add more test cases");
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
        test_case(make_sqrt(2, ri(1), ri(2)), ri(0), Some(1.into()));
        test_case(r(2, 3), ri(1), Some(r(2, 3).into()));
        test_case(
            make_sqrt(2, ri(1), ri(2)),
            ri(1),
            Some(make_sqrt(2, ri(1), ri(2))),
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
        test_case(make_sqrt(8, ri(2), ri(3)), r(-2, 3), Some(r(1, 2).into()));
        test_case(make_sqrt(2, ri(1), ri(2)), ri(2), Some(2.into()));
        test_case(make_sqrt(2, ri(1), ri(2)), ri(-2), Some(r(1, 2).into()));
        unimplemented!("add more cases");
    }
}
