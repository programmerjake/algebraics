// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::{
    traits::{
        AlwaysExactDiv, AlwaysExactDivAssign, CeilLog2, ExactDiv, ExactDivAssign, FloorLog2,
        IntervalUnion, IntervalUnionAssign,
    },
    util::DebugAsDisplay,
};
use num_bigint::{BigInt, BigUint};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{FromPrimitive, One, Pow, Signed, ToPrimitive, Zero};
use std::{
    borrow::Cow,
    fmt, mem,
    ops::{Add, AddAssign, Div, DivAssign, Mul, MulAssign, Neg, Sub, SubAssign},
    sync::{Arc, RwLock},
};

fn convert_log2_denom_floor(numer: &mut BigInt, old_log2_denom: usize, new_log2_denom: usize) {
    if new_log2_denom >= old_log2_denom {
        *numer <<= new_log2_denom - old_log2_denom;
    } else {
        *numer >>= old_log2_denom - new_log2_denom;
    }
}

fn convert_log2_denom_ceil(numer: &mut BigInt, old_log2_denom: usize, new_log2_denom: usize) {
    if new_log2_denom >= old_log2_denom {
        *numer <<= new_log2_denom - old_log2_denom;
    } else {
        let mut numer_value = mem::take(numer);
        numer_value = -numer_value;
        numer_value >>= old_log2_denom - new_log2_denom;
        numer_value = -numer_value;
        *numer = numer_value;
    }
}

struct ConstantCache {
    cache: RwLock<Arc<Vec<Arc<DyadicFractionInterval>>>>,
}

impl ConstantCache {
    fn new() -> Self {
        Self {
            cache: RwLock::new(Vec::new().into()),
        }
    }
    fn log2_denom_to_cache_index(log2_denom: usize) -> usize {
        let f = |log2_denom| ((log2_denom as f64 + 1.0).log2() * 3.0).floor() as usize;
        let min_log2_denom = 32;
        f(log2_denom.max(min_log2_denom)) - f(min_log2_denom)
    }
    fn get_required_log2_denom_for_cache_index(cache_index: usize) -> usize {
        let mut bit = !(!0usize >> 1); // just top bit set
        let mut retval = 0;
        while bit != 0 {
            if Self::log2_denom_to_cache_index(retval | bit) <= cache_index {
                retval |= bit;
            }
            bit >>= 1;
        }
        retval
    }
    #[inline]
    fn read_cache(
        &self,
        cache_index: usize,
    ) -> Result<Arc<DyadicFractionInterval>, Arc<Vec<Arc<DyadicFractionInterval>>>> {
        let read_lock = self.cache.read().unwrap();
        if let Some(entry) = read_lock.get(cache_index) {
            Ok(entry.clone())
        } else {
            Err(read_lock.clone())
        }
    }
    fn write_cache(&self, new_cache: Vec<Arc<DyadicFractionInterval>>) {
        let mut write_lock = self.cache.write().unwrap();
        // check because some other thread could have calculated a more accurate in the mean time
        if new_cache.len() > write_lock.len() {
            *write_lock = Arc::new(new_cache);
        }
    }
    #[cold]
    fn fill_cache<F: Fn(usize) -> DyadicFractionInterval>(
        &self,
        old_cache: Arc<Vec<Arc<DyadicFractionInterval>>>,
        cache_index: usize,
        compute_fn: F,
    ) -> Arc<DyadicFractionInterval> {
        let computed_result =
            compute_fn(Self::get_required_log2_denom_for_cache_index(cache_index));
        let mut new_cache: Vec<Arc<_>> = Vec::with_capacity(cache_index + 1);
        new_cache.extend(old_cache.iter().cloned());
        for i in new_cache.len()..cache_index {
            let log2_denom = Self::get_required_log2_denom_for_cache_index(i);
            new_cache.push(computed_result.to_converted_log2_denom(log2_denom).into());
        }
        let log2_denom = Self::get_required_log2_denom_for_cache_index(cache_index);
        assert!(computed_result.log2_denom >= log2_denom);
        let retval = Arc::new(computed_result.into_converted_log2_denom(log2_denom));
        new_cache.push(retval.clone());
        self.write_cache(new_cache);
        retval
    }
    fn get<F: Fn(usize) -> DyadicFractionInterval>(
        &self,
        log2_denom: usize,
        compute_fn: F,
    ) -> DyadicFractionInterval {
        let cache_index = Self::log2_denom_to_cache_index(log2_denom);
        match self.read_cache(cache_index) {
            Ok(entry) => entry,
            Err(cache) => self.fill_cache(cache, cache_index, compute_fn),
        }
        .to_converted_log2_denom(log2_denom)
    }
}

/// inclusive interval of the form `[a / 2^n, b / 2^n]` where `a` and `b` are integers and `n` is an unsigned integer.
#[derive(Clone, Default, Hash)]
pub struct DyadicFractionInterval {
    lower_bound_numer: BigInt,
    upper_bound_numer: BigInt,
    log2_denom: usize,
}

impl DyadicFractionInterval {
    pub fn new(lower_bound_numer: BigInt, upper_bound_numer: BigInt, log2_denom: usize) -> Self {
        assert!(lower_bound_numer <= upper_bound_numer);
        Self {
            lower_bound_numer,
            upper_bound_numer,
            log2_denom,
        }
    }
    pub fn from_ratio_range(
        lower_bound: Ratio<BigInt>,
        upper_bound: Ratio<BigInt>,
        log2_denom: usize,
    ) -> Self {
        assert!(lower_bound <= upper_bound);
        let denom = BigInt::one() << log2_denom;
        let lower_bound_numer = (lower_bound * &denom).floor().to_integer();
        let upper_bound_numer = (upper_bound * denom).ceil().to_integer();
        Self {
            lower_bound_numer,
            upper_bound_numer,
            log2_denom,
        }
    }
    pub fn from_ratio(ratio: Ratio<BigInt>, log2_denom: usize) -> Self {
        let (mut numer, denom) = ratio.into();
        numer <<= log2_denom;
        let ratio = Ratio::new(numer, denom);
        let lower_bound_numer = ratio.floor().to_integer();
        let upper_bound_numer = ratio.ceil().to_integer();
        Self {
            lower_bound_numer,
            upper_bound_numer,
            log2_denom,
        }
    }
    pub fn from_int(value: BigInt, log2_denom: usize) -> Self {
        Self::from_dyadic_fraction(value << log2_denom, log2_denom)
    }
    pub fn from_int_range(lower_bound: BigInt, upper_bound: BigInt, log2_denom: usize) -> Self {
        Self::new(lower_bound, upper_bound, 0).into_converted_log2_denom(log2_denom)
    }
    pub fn from_dyadic_fraction(numer: BigInt, log2_denom: usize) -> Self {
        Self {
            lower_bound_numer: numer.clone(),
            upper_bound_numer: numer,
            log2_denom,
        }
    }
    pub fn zero(log2_denom: usize) -> Self {
        Self {
            lower_bound_numer: BigInt::zero(),
            upper_bound_numer: BigInt::zero(),
            log2_denom,
        }
    }
    pub fn one(log2_denom: usize) -> Self {
        Self::from_int(BigInt::one(), log2_denom)
    }
    pub fn negative_one(log2_denom: usize) -> Self {
        Self::from_int(-BigInt::one(), log2_denom)
    }
    pub fn set_zero(&mut self) {
        self.lower_bound_numer.set_zero();
        self.upper_bound_numer.set_zero();
    }
    pub fn set_one(&mut self) {
        self.lower_bound_numer.set_one();
        self.lower_bound_numer <<= self.log2_denom;
        self.upper_bound_numer.clone_from(&self.lower_bound_numer);
    }
    pub fn set_negative_one(&mut self) {
        self.lower_bound_numer.set_one();
        self.lower_bound_numer <<= self.log2_denom;
        self.lower_bound_numer = -mem::take(&mut self.lower_bound_numer);
        self.upper_bound_numer.clone_from(&self.lower_bound_numer);
    }
    pub fn into_ratio_range(self) -> (Ratio<BigInt>, Ratio<BigInt>) {
        let denom = BigInt::one() << self.log2_denom;
        (
            Ratio::new(self.lower_bound_numer, denom.clone()),
            Ratio::new(self.upper_bound_numer, denom),
        )
    }
    pub fn to_ratio_range(&self) -> (Ratio<BigInt>, Ratio<BigInt>) {
        self.clone().into_ratio_range()
    }
    pub fn into_lower_bound(self) -> Ratio<BigInt> {
        Ratio::new(self.lower_bound_numer, BigInt::one() << self.log2_denom)
    }
    pub fn into_upper_bound(self) -> Ratio<BigInt> {
        Ratio::new(self.upper_bound_numer, BigInt::one() << self.log2_denom)
    }
    pub fn lower_bound(&self) -> Ratio<BigInt> {
        Ratio::new(
            self.lower_bound_numer.clone(),
            BigInt::one() << self.log2_denom,
        )
    }
    pub fn upper_bound(&self) -> Ratio<BigInt> {
        Ratio::new(
            self.upper_bound_numer.clone(),
            BigInt::one() << self.log2_denom,
        )
    }
    pub fn log2_denom(&self) -> usize {
        self.log2_denom
    }
    pub fn lower_bound_numer(&self) -> &BigInt {
        &self.lower_bound_numer
    }
    pub fn upper_bound_numer(&self) -> &BigInt {
        &self.upper_bound_numer
    }
    /// convert to a tuple `(self.lower_bound_numer, self.upper_bound_numer, self.log2_denom)`
    pub fn destructure(self) -> (BigInt, BigInt, usize) {
        (
            self.lower_bound_numer,
            self.upper_bound_numer,
            self.log2_denom,
        )
    }
    pub fn set_to_lower_bound(&mut self) {
        self.upper_bound_numer.clone_from(&self.lower_bound_numer);
    }
    pub fn set_to_upper_bound(&mut self) {
        self.lower_bound_numer.clone_from(&self.upper_bound_numer);
    }
    pub fn set_lower_bound_numer(&mut self, lower_bound_numer: BigInt) {
        assert!(lower_bound_numer <= self.upper_bound_numer);
        self.lower_bound_numer = lower_bound_numer;
    }
    pub fn set_upper_bound_numer(&mut self, upper_bound_numer: BigInt) {
        assert!(self.lower_bound_numer <= upper_bound_numer);
        self.upper_bound_numer = upper_bound_numer;
    }
    pub fn set_lower_bound_to_zero(&mut self) {
        assert!(!self.upper_bound_numer.is_negative());
        self.lower_bound_numer.set_zero();
    }
    pub fn set_upper_bound_to_zero(&mut self) {
        assert!(!self.lower_bound_numer.is_positive());
        self.upper_bound_numer.set_zero();
    }
    pub fn convert_log2_denom(&mut self, log2_denom: usize) {
        convert_log2_denom_floor(&mut self.lower_bound_numer, self.log2_denom, log2_denom);
        convert_log2_denom_ceil(&mut self.upper_bound_numer, self.log2_denom, log2_denom);
        self.log2_denom = log2_denom;
    }
    pub fn into_converted_log2_denom(mut self, log2_denom: usize) -> Self {
        self.convert_log2_denom(log2_denom);
        self
    }
    pub fn to_converted_log2_denom(&self, log2_denom: usize) -> Self {
        self.clone().into_converted_log2_denom(log2_denom)
    }
    fn do_op_assign<Op: Fn(&mut BigInt, &mut BigInt, &BigInt, &BigInt, usize) -> R, R>(
        &mut self,
        rhs: Cow<DyadicFractionInterval>,
        op: Op,
    ) -> R {
        if rhs.log2_denom >= self.log2_denom {
            let shift_amount = rhs.log2_denom - self.log2_denom;
            self.lower_bound_numer <<= shift_amount;
            self.upper_bound_numer <<= shift_amount;
            self.log2_denom = rhs.log2_denom;
            op(
                &mut self.lower_bound_numer,
                &mut self.upper_bound_numer,
                &rhs.lower_bound_numer,
                &rhs.upper_bound_numer,
                self.log2_denom,
            )
        } else {
            let shift_amount = self.log2_denom - rhs.log2_denom;
            let rhs_lower_bound_numer;
            let rhs_upper_bound_numer;
            match rhs {
                Cow::Borrowed(rhs) => {
                    rhs_lower_bound_numer = &rhs.lower_bound_numer << shift_amount;
                    rhs_upper_bound_numer = &rhs.upper_bound_numer << shift_amount;
                }
                Cow::Owned(rhs) => {
                    rhs_lower_bound_numer = rhs.lower_bound_numer << shift_amount;
                    rhs_upper_bound_numer = rhs.upper_bound_numer << shift_amount;
                }
            }
            op(
                &mut self.lower_bound_numer,
                &mut self.upper_bound_numer,
                &rhs_lower_bound_numer,
                &rhs_upper_bound_numer,
                self.log2_denom,
            )
        }
    }
    fn do_add_assign(&mut self, rhs: Cow<DyadicFractionInterval>) {
        self.do_op_assign(
            rhs,
            |lhs_lower_bound_numer,
             lhs_upper_bound_numer,
             rhs_lower_bound_numer,
             rhs_upper_bound_numer,
             _log2_denom| {
                *lhs_lower_bound_numer += rhs_lower_bound_numer;
                *lhs_upper_bound_numer += rhs_upper_bound_numer;
            },
        );
    }
    fn do_sub_assign(&mut self, rhs: Cow<DyadicFractionInterval>) {
        self.do_op_assign(
            rhs,
            |lhs_lower_bound_numer,
             lhs_upper_bound_numer,
             rhs_lower_bound_numer,
             rhs_upper_bound_numer,
             _log2_denom| {
                // rhs swapped and subtracted
                *lhs_lower_bound_numer -= rhs_upper_bound_numer;
                *lhs_upper_bound_numer -= rhs_lower_bound_numer;
            },
        );
    }
    fn do_mul_assign_int(&mut self, rhs: &BigInt) {
        if rhs.is_negative() {
            mem::swap(&mut self.lower_bound_numer, &mut self.upper_bound_numer);
        }
        self.lower_bound_numer.mul_assign(rhs);
        self.upper_bound_numer.mul_assign(rhs);
    }
    fn do_mul_assign_ratio(&mut self, rhs: &Ratio<BigInt>) {
        if rhs.is_negative() {
            mem::swap(&mut self.lower_bound_numer, &mut self.upper_bound_numer);
        }
        self.lower_bound_numer = (rhs * &self.lower_bound_numer).floor().to_integer();
        self.upper_bound_numer = (rhs * &self.upper_bound_numer).ceil().to_integer();
    }
    fn do_mul_assign(&mut self, rhs: Cow<DyadicFractionInterval>) {
        self.do_op_assign(
            rhs,
            |lhs_lower_bound_numer,
             lhs_upper_bound_numer,
             rhs_lower_bound_numer,
             rhs_upper_bound_numer,
             log2_denom| {
                let mut bounds = [
                    Some(&*lhs_lower_bound_numer * rhs_lower_bound_numer),
                    Some(&*lhs_lower_bound_numer * rhs_upper_bound_numer),
                    Some(&*lhs_upper_bound_numer * rhs_lower_bound_numer),
                    Some(&*lhs_upper_bound_numer * rhs_upper_bound_numer),
                ];
                let mut lower_bound = None;
                for bound in &mut bounds {
                    match (&mut lower_bound, bound) {
                        (_, None) => {}
                        (None, bound) => lower_bound = bound.take(),
                        (Some(lower_bound), Some(bound)) => {
                            if *bound < *lower_bound {
                                mem::swap(lower_bound, bound)
                            }
                        }
                    }
                }
                let mut upper_bound = None;
                for bound in &mut bounds {
                    match (&mut upper_bound, bound) {
                        (_, None) => {}
                        (None, bound) => upper_bound = bound.take(),
                        (Some(upper_bound), Some(bound)) => {
                            if *bound > *upper_bound {
                                mem::swap(upper_bound, bound)
                            }
                        }
                    }
                }
                *lhs_lower_bound_numer = lower_bound.expect("known to exist") >> log2_denom;
                *lhs_upper_bound_numer = -(-upper_bound.expect("known to exist") >> log2_denom);
            },
        );
    }
    fn do_checked_div_assign(&mut self, rhs: Cow<DyadicFractionInterval>) -> Result<(), ()> {
        if let Some(recip) = rhs.checked_recip() {
            *self *= recip;
            Ok(())
        } else {
            Err(())
        }
    }
    fn do_div_assign(&mut self, rhs: Cow<DyadicFractionInterval>) {
        *self *= rhs.recip();
    }
    pub fn checked_recip(&self) -> Option<Self> {
        if self.contains_zero() {
            None
        } else {
            let dividend = BigInt::one() << (2 * self.log2_denom);
            let lower_bound_numer = dividend.div_floor(&self.upper_bound_numer);
            let upper_bound_numer = dividend.div_ceil(&self.lower_bound_numer);
            Some(Self {
                lower_bound_numer,
                upper_bound_numer,
                log2_denom: self.log2_denom,
            })
        }
    }
    pub fn recip(&self) -> Self {
        self.checked_recip().expect("division by zero")
    }
    pub fn into_square(mut self) -> Self {
        let contains_zero = self.contains_zero();
        let lower_bound_numer_is_negative = self.lower_bound_numer.is_negative();
        let upper_bound_numer_is_negative = self.upper_bound_numer.is_negative();
        let mut min = if lower_bound_numer_is_negative {
            -self.lower_bound_numer
        } else {
            self.lower_bound_numer
        };
        let mut max = if upper_bound_numer_is_negative {
            -self.upper_bound_numer
        } else {
            self.upper_bound_numer
        };
        if min > max {
            mem::swap(&mut min, &mut max);
        }
        self.lower_bound_numer = if contains_zero {
            BigInt::zero()
        } else {
            (&min * &min) >> self.log2_denom
        };
        self.upper_bound_numer = -(-(&max * &max) >> self.log2_denom);
        self
    }
    pub fn square_assign(&mut self) {
        *self = mem::take(self).into_square();
    }
    pub fn square(&self) -> Self {
        self.clone().into_square()
    }
    fn do_sqrt(radicand: Cow<Self>) -> Self {
        let log2_denom = radicand.log2_denom;
        let (scaled_lower_bound_numer, scaled_upper_bound_numer) = match radicand {
            Cow::Borrowed(radicand) => (
                &radicand.lower_bound_numer << log2_denom,
                &radicand.upper_bound_numer << log2_denom,
            ),
            Cow::Owned(radicand) => (
                radicand.lower_bound_numer << log2_denom,
                radicand.upper_bound_numer << log2_denom,
            ),
        };
        let lower_bound_numer = scaled_lower_bound_numer.sqrt();
        let sqrt = scaled_upper_bound_numer.sqrt();
        let upper_bound_numer = if &sqrt * &sqrt == scaled_upper_bound_numer {
            sqrt
        } else {
            sqrt + 1
        };
        Self {
            lower_bound_numer,
            upper_bound_numer,
            log2_denom,
        }
    }
    pub fn sqrt_assign(&mut self) {
        *self = mem::take(self).into_sqrt();
    }
    pub fn into_sqrt(self) -> Self {
        Self::do_sqrt(Cow::Owned(self))
    }
    pub fn sqrt(&self) -> Self {
        Self::do_sqrt(Cow::Borrowed(self))
    }
    pub fn contains_zero(&self) -> bool {
        !self.lower_bound_numer.is_positive() && !self.upper_bound_numer.is_negative()
    }
    fn do_interval_union_assign(&mut self, rhs: Cow<Self>) {
        self.do_op_assign(
            rhs,
            |lhs_lower_bound_numer,
             lhs_upper_bound_numer,
             rhs_lower_bound_numer,
             rhs_upper_bound_numer,
             _log2_denom| {
                if *lhs_lower_bound_numer > *rhs_lower_bound_numer {
                    lhs_lower_bound_numer.clone_from(rhs_lower_bound_numer);
                }
                if *lhs_upper_bound_numer < *rhs_upper_bound_numer {
                    lhs_upper_bound_numer.clone_from(rhs_upper_bound_numer);
                }
            },
        );
    }
    pub fn into_arithmetic_geometric_mean(self, rhs: Self) -> Self {
        assert!(!self.lower_bound_numer.is_negative());
        assert!(!rhs.lower_bound_numer.is_negative());
        let mut result = (&self).interval_union(&rhs);
        let mut result_range = &result.upper_bound_numer - &result.lower_bound_numer;
        let mut arithmetic_mean = (&self + &rhs) / 2i32;
        let mut geometric_mean = (self * rhs).into_sqrt();
        let mut next_result = (&arithmetic_mean).interval_union(&geometric_mean);
        let mut next_result_range = &next_result.upper_bound_numer - &next_result.lower_bound_numer;
        while next_result_range < result_range {
            result = next_result;
            result_range = next_result_range;
            let next_arithmetic_mean = (&arithmetic_mean + &geometric_mean) / 2;
            geometric_mean = (arithmetic_mean * geometric_mean).into_sqrt();
            arithmetic_mean = next_arithmetic_mean;
            next_result = (&arithmetic_mean).interval_union(&geometric_mean);
            next_result_range = &next_result.upper_bound_numer - &next_result.lower_bound_numer;
        }
        result
    }
    pub fn arithmetic_geometric_mean(&self, rhs: &Self) -> Self {
        self.clone().into_arithmetic_geometric_mean(rhs.clone())
    }
    pub fn sqrt_2(log2_denom: usize) -> Self {
        lazy_static! {
            static ref CACHE: ConstantCache = ConstantCache::new();
        }
        CACHE.get(log2_denom, |log2_denom: usize| -> Self {
            Self::from_int(2i32.into(), log2_denom).into_sqrt()
        })
    }
    #[allow(dead_code)] // FIXME: remove when implemented
    pub(crate) fn pi(log2_denom: usize) -> Self {
        lazy_static! {
            static ref CACHE: ConstantCache = ConstantCache::new();
        }
        let compute = |log2_denom: usize| -> Self {
            let log2_denom = log2_denom + 32 + log2_denom / 1000;
            let _ = log2_denom;
            unimplemented!(
                "finish implementing algorithm to compute pi using arithmetic_geometric_mean"
            );
        };
        CACHE.get(log2_denom, compute)
    }
    pub fn natural_log_of_2(log2_denom: usize) -> Self {
        lazy_static! {
            static ref CACHE: ConstantCache = ConstantCache::new();
        }
        let compute = |log2_denom: usize| -> Self {
            // TODO: switch to faster algorithm
            // uses series for log(2) == sum(i=1..inf of 1/(i * 2^i))
            let log2_denom = log2_denom
                + 10
                + (log2_denom + 1)
                    .floor_log2()
                    .expect("log2_denom + 1 is non-zero");
            let mut retval = Self::zero(log2_denom);
            for i in 1..log2_denom {
                retval +=
                    Self::from_ratio(Ratio::new(BigInt::one(), BigInt::from(i) << i), log2_denom);
            }
            retval.upper_bound_numer += 1;
            retval
        };
        CACHE.get(log2_denom, compute)
    }
    // TODO: implement exp/log in terms of arithmetic_geometric_mean and pi
    /// computes `log((self + 1) / (self - 1))` for `self >= 2`
    fn log_core(&self) -> Self {
        assert!(self.upper_bound_numer >= self.lower_bound_numer);
        let working_log2_denom = self.log2_denom
            + 10
            + (self.log2_denom + 1)
                .floor_log2()
                .expect("log2_denom + 1 is non-zero");
        let mut retval = Self::zero(working_log2_denom);
        let scaled_term_numerator = BigInt::from(2) << working_log2_denom;
        let mut power = self.to_converted_log2_denom(working_log2_denom);
        assert!(
            power.lower_bound_numer >= scaled_term_numerator,
            "input is too small, must be at least 2"
        );
        let self_squared = power.square();
        for i in 0..working_log2_denom {
            let term_denominator = &power * (i * 2 + 1);
            let term_lower_bound = Ratio::new(
                scaled_term_numerator.clone(),
                term_denominator.upper_bound_numer,
            );
            let term_upper_bound = Ratio::new(
                scaled_term_numerator.clone(),
                term_denominator.lower_bound_numer,
            );
            retval +=
                Self::from_ratio_range(term_lower_bound, term_upper_bound, working_log2_denom);
            power *= &self_squared;
        }
        retval.upper_bound_numer += 1;
        retval.into_converted_log2_denom(self.log2_denom)
    }
    pub fn log(&self) -> Self {
        assert!(self.lower_bound_numer.is_positive());
        assert!(self.upper_bound_numer >= self.lower_bound_numer);
        let working_log2_denom = self.log2_denom + 16;
        let i64_self_log2_denom =
            i64::from_usize(self.log2_denom).expect("self.log2_denom doesn't fit in i64");
        let mut lower_bound_shift = self
            .lower_bound_numer
            .floor_log2()
            .expect("already checked") as i64
            - i64_self_log2_denom;
        let mut upper_bound_shift = self
            .upper_bound_numer
            .floor_log2()
            .expect("already checked") as i64
            - i64_self_log2_denom;
        let (self_lower_bound, self_upper_bound) = self.to_ratio_range();
        let mut shifted_lower_bound = if lower_bound_shift < 0 {
            self_lower_bound * (BigInt::one() << (-lower_bound_shift) as usize)
        } else {
            self_lower_bound / (BigInt::one() << lower_bound_shift as usize)
        };
        let mut shifted_upper_bound = if upper_bound_shift < 0 {
            self_upper_bound * (BigInt::one() << (-upper_bound_shift) as usize)
        } else {
            self_upper_bound / (BigInt::one() << upper_bound_shift as usize)
        };
        lazy_static! {
            static ref THREE_OVER_TWO: Ratio<BigInt> = Ratio::new(3.into(), 2.into());
            static ref TWO: BigInt = 2.into();
            static ref ONE: BigInt = 1.into();
        }
        if shifted_lower_bound < *THREE_OVER_TWO {
            shifted_lower_bound *= &*TWO;
            lower_bound_shift -= 1;
        }
        if shifted_upper_bound < *THREE_OVER_TWO {
            shifted_upper_bound *= &*TWO;
            upper_bound_shift -= 1;
        }
        let mut retval = Self::from_int_range(
            BigInt::from(lower_bound_shift),
            BigInt::from(upper_bound_shift),
            working_log2_denom,
        );
        retval *= Self::natural_log_of_2(working_log2_denom);
        retval += Self::from_ratio(
            (shifted_lower_bound.clone() + &*ONE) / (shifted_lower_bound - &*ONE),
            working_log2_denom,
        )
        .log_core()
        .interval_union(
            Self::from_ratio(
                (shifted_upper_bound.clone() + &*ONE) / (shifted_upper_bound - &*ONE),
                working_log2_denom,
            )
            .log_core(),
        );
        retval.into_converted_log2_denom(self.log2_denom)
    }
    pub fn into_exp(mut self) -> Self {
        let original_log2_denom = self.log2_denom;
        self.convert_log2_denom(original_log2_denom + 10);
        let short_natural_log_of_2 = Self::natural_log_of_2(self.log2_denom);
        let mut extra_bits = 0;
        let mut calculate_needed_extra_bits = |v: &BigInt| {
            if v.is_positive() {
                extra_bits = extra_bits.max(
                    v.div_floor(&short_natural_log_of_2.lower_bound_numer)
                        .to_usize()
                        .expect("input too big in exp()"),
                );
            }
        };
        calculate_needed_extra_bits(&self.lower_bound_numer);
        calculate_needed_extra_bits(&self.upper_bound_numer);
        let working_log2_denom = (original_log2_denom
            + 32
            + (original_log2_denom + 1)
                .floor_log2()
                .expect("known to not fail")
                * 2)
        .checked_add(extra_bits)
        .expect("input too big in exp()");
        self.convert_log2_denom(working_log2_denom);
        let natural_log_of_2 = Self::natural_log_of_2(working_log2_denom);
        let (floor_power_of_2_lower_bound, remainder) = self
            .lower_bound_numer
            .div_mod_floor(&natural_log_of_2.upper_bound_numer);
        self.lower_bound_numer = remainder;
        let (floor_power_of_2_upper_bound, remainder) = self
            .upper_bound_numer
            .div_mod_floor(&natural_log_of_2.lower_bound_numer);
        self.upper_bound_numer = remainder;
        let mut term = Self::one(working_log2_denom);
        let mut retval = term.clone();
        for i in 1..working_log2_denom {
            term *= &self;
            term /= i;
            retval += &term;
            if term.upper_bound_numer.is_one() || term.upper_bound_numer.is_zero() {
                assert!(term.lower_bound_numer.is_zero());
                break;
            }
        }
        if let Some(shift_amount) = floor_power_of_2_lower_bound.abs().to_usize() {
            if floor_power_of_2_lower_bound.is_negative() {
                retval.lower_bound_numer >>= shift_amount;
            } else {
                retval.lower_bound_numer <<= shift_amount;
            }
        } else {
            assert!(
                floor_power_of_2_lower_bound.is_negative(),
                "overflow: input too big for exp()"
            );
            retval.lower_bound_numer.set_zero();
        }
        if let Some(shift_amount) = floor_power_of_2_upper_bound.abs().to_usize() {
            if floor_power_of_2_upper_bound.is_negative() {
                retval.upper_bound_numer = -retval.upper_bound_numer;
                retval.upper_bound_numer >>= shift_amount;
                retval.upper_bound_numer = -retval.upper_bound_numer;
            } else {
                retval.upper_bound_numer <<= shift_amount;
            }
        } else {
            assert!(
                floor_power_of_2_upper_bound.is_negative(),
                "overflow: input too big for exp()"
            );
            retval.upper_bound_numer.set_one();
        }
        retval.into_converted_log2_denom(original_log2_denom)
    }
    pub fn exp(&self) -> Self {
        self.clone().into_exp()
    }
    /// use instead of .eq() since .eq() wouldn't have well defined results in all cases
    pub fn is_same(&self, rhs: &Self) -> bool {
        let Self {
            lower_bound_numer,
            upper_bound_numer,
            log2_denom,
        } = self;
        *lower_bound_numer == rhs.lower_bound_numer
            && *upper_bound_numer == rhs.upper_bound_numer
            && *log2_denom == rhs.log2_denom
    }
    pub fn abs_assign(&mut self) {
        let contains_zero = self.contains_zero();
        if self.lower_bound_numer.is_negative() {
            self.lower_bound_numer = -mem::take(&mut self.lower_bound_numer);
        }
        if self.upper_bound_numer.is_negative() {
            self.upper_bound_numer = -mem::take(&mut self.upper_bound_numer);
        }
        if self.lower_bound_numer > self.upper_bound_numer {
            mem::swap(&mut self.lower_bound_numer, &mut self.upper_bound_numer);
        }
        if contains_zero {
            self.lower_bound_numer.set_zero();
        }
    }
    pub fn into_abs(mut self) -> Self {
        self.abs_assign();
        self
    }
    pub fn abs(&self) -> Self {
        self.clone().into_abs()
    }
    pub fn floor_assign(&mut self, new_log2_denom: usize) {
        self.lower_bound_numer >>= self.log2_denom;
        self.upper_bound_numer >>= self.log2_denom;
        self.log2_denom = 0;
        self.convert_log2_denom(new_log2_denom);
    }
    pub fn into_floor(mut self, new_log2_denom: usize) -> Self {
        self.floor_assign(new_log2_denom);
        self
    }
    pub fn floor(&self, new_log2_denom: usize) -> Self {
        self.clone().into_floor(new_log2_denom)
    }
    pub fn ceil_assign(&mut self, new_log2_denom: usize) {
        self.lower_bound_numer = -mem::take(&mut self.lower_bound_numer);
        self.upper_bound_numer = -mem::take(&mut self.upper_bound_numer);
        self.lower_bound_numer >>= self.log2_denom;
        self.upper_bound_numer >>= self.log2_denom;
        self.lower_bound_numer = -mem::take(&mut self.lower_bound_numer);
        self.upper_bound_numer = -mem::take(&mut self.upper_bound_numer);
        self.log2_denom = 0;
        self.convert_log2_denom(new_log2_denom);
    }
    pub fn into_ceil(mut self, new_log2_denom: usize) -> Self {
        self.ceil_assign(new_log2_denom);
        self
    }
    pub fn ceil(&self, new_log2_denom: usize) -> Self {
        self.clone().into_ceil(new_log2_denom)
    }
    pub(crate) fn floor_log2(&self) -> Option<(i64, i64)> {
        let lower_bound = self.lower_bound_numer.floor_log2()? as i64 - self.log2_denom as i64;
        let upper_bound = self.upper_bound_numer.floor_log2()? as i64 - self.log2_denom as i64;
        Some((lower_bound, upper_bound))
    }
    pub(crate) fn ceil_log2(&self) -> Option<(i64, i64)> {
        let lower_bound = self.lower_bound_numer.ceil_log2()? as i64 - self.log2_denom as i64;
        let upper_bound = self.upper_bound_numer.ceil_log2()? as i64 - self.log2_denom as i64;
        Some((lower_bound, upper_bound))
    }
}

impl fmt::Debug for DyadicFractionInterval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.debug_struct("DyadicFractionInterval")
            .field(
                "lower_bound_numer",
                &DebugAsDisplay(&self.lower_bound_numer),
            )
            .field(
                "upper_bound_numer",
                &DebugAsDisplay(&self.upper_bound_numer),
            )
            .field("log2_denom", &self.log2_denom)
            .finish()
    }
}

impl fmt::Display for DyadicFractionInterval {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "[{} / 2^{}, {} / 2^{}]",
            self.lower_bound_numer, self.log2_denom, self.upper_bound_numer, self.log2_denom
        )
    }
}

impl Neg for DyadicFractionInterval {
    type Output = Self;
    fn neg(self) -> Self {
        let Self {
            lower_bound_numer,
            upper_bound_numer,
            log2_denom,
        } = self;
        Self {
            lower_bound_numer: -upper_bound_numer,
            upper_bound_numer: -lower_bound_numer,
            log2_denom,
        }
    }
}

impl Neg for &'_ DyadicFractionInterval {
    type Output = DyadicFractionInterval;
    fn neg(self) -> DyadicFractionInterval {
        -self.clone()
    }
}

macro_rules! forward_op_to_op_assign {
    ($op_assign_trait:ident, $op_assign:ident, $op_trait:ident, $op:ident, $rhs:ty) => {
        impl $op_trait<$rhs> for DyadicFractionInterval {
            type Output = DyadicFractionInterval;
            fn $op(mut self, rhs: $rhs) -> DyadicFractionInterval {
                self.$op_assign(rhs);
                self
            }
        }

        impl $op_trait<&'_ $rhs> for DyadicFractionInterval {
            type Output = DyadicFractionInterval;
            fn $op(mut self, rhs: &$rhs) -> DyadicFractionInterval {
                self.$op_assign(rhs);
                self
            }
        }

        impl $op_trait<$rhs> for &'_ DyadicFractionInterval {
            type Output = DyadicFractionInterval;
            fn $op(self, rhs: $rhs) -> DyadicFractionInterval {
                self.clone().$op(rhs)
            }
        }

        impl<'a, 'b> $op_trait<&'a $rhs> for &'b DyadicFractionInterval {
            type Output = DyadicFractionInterval;
            fn $op(self, rhs: &$rhs) -> DyadicFractionInterval {
                self.clone().$op(rhs)
            }
        }
    };
}

macro_rules! forward_type_to_bigint {
    ($op_assign_trait:ident, $op_assign:ident, $op_trait:ident, $op:ident, $rhs:ty) => {
        impl $op_assign_trait<$rhs> for DyadicFractionInterval {
            fn $op_assign(&mut self, rhs: $rhs) {
                self.$op_assign(BigInt::from(rhs));
            }
        }

        impl $op_assign_trait<&'_ $rhs> for DyadicFractionInterval {
            fn $op_assign(&mut self, rhs: &$rhs) {
                self.$op_assign(BigInt::from(rhs.clone()));
            }
        }

        forward_op_to_op_assign!($op_assign_trait, $op_assign, $op_trait, $op, $rhs);

        impl $op_assign_trait<Ratio<$rhs>> for DyadicFractionInterval {
            fn $op_assign(&mut self, rhs: Ratio<$rhs>) {
                let (numer, denom) = rhs.into();
                self.$op_assign(Ratio::<BigInt>::new(numer.into(), denom.into()));
            }
        }

        impl $op_assign_trait<&'_ Ratio<$rhs>> for DyadicFractionInterval {
            fn $op_assign(&mut self, rhs: &Ratio<$rhs>) {
                self.$op_assign(rhs.clone());
            }
        }

        forward_op_to_op_assign!($op_assign_trait, $op_assign, $op_trait, $op, Ratio<$rhs>);
    };
}

macro_rules! forward_types_to_bigint {
    ($op_assign_trait:ident, $op_assign:ident, $op_trait:ident, $op:ident) => {
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, u8);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, u16);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, u32);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, u64);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, u128);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, usize);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, BigUint);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, i8);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, i16);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, i32);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, i64);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, i128);
        forward_type_to_bigint!($op_assign_trait, $op_assign, $op_trait, $op, isize);
    };
}

impl IntervalUnionAssign<DyadicFractionInterval> for DyadicFractionInterval {
    fn interval_union_assign(&mut self, rhs: DyadicFractionInterval) {
        self.do_interval_union_assign(Cow::Owned(rhs));
    }
}

impl IntervalUnionAssign<&'_ DyadicFractionInterval> for DyadicFractionInterval {
    fn interval_union_assign(&mut self, rhs: &DyadicFractionInterval) {
        self.do_interval_union_assign(Cow::Borrowed(rhs));
    }
}

forward_op_to_op_assign!(
    IntervalUnionAssign,
    interval_union_assign,
    IntervalUnion,
    interval_union,
    DyadicFractionInterval
);

impl AddAssign<DyadicFractionInterval> for DyadicFractionInterval {
    fn add_assign(&mut self, rhs: DyadicFractionInterval) {
        self.do_add_assign(Cow::Owned(rhs));
    }
}

impl AddAssign<&'_ DyadicFractionInterval> for DyadicFractionInterval {
    fn add_assign(&mut self, rhs: &DyadicFractionInterval) {
        self.do_add_assign(Cow::Borrowed(rhs));
    }
}

impl AddAssign<BigInt> for DyadicFractionInterval {
    fn add_assign(&mut self, mut rhs: BigInt) {
        rhs <<= self.log2_denom;
        self.lower_bound_numer.add_assign(&rhs);
        self.upper_bound_numer.add_assign(rhs);
    }
}

impl AddAssign<&'_ BigInt> for DyadicFractionInterval {
    fn add_assign(&mut self, rhs: &BigInt) {
        #![allow(clippy::suspicious_op_assign_impl)]
        let rhs = rhs << self.log2_denom;
        self.lower_bound_numer.add_assign(&rhs);
        self.upper_bound_numer.add_assign(rhs);
    }
}

impl AddAssign<Ratio<BigInt>> for DyadicFractionInterval {
    fn add_assign(&mut self, rhs: Ratio<BigInt>) {
        self.add_assign(DyadicFractionInterval::from_ratio(rhs, self.log2_denom))
    }
}

impl AddAssign<&'_ Ratio<BigInt>> for DyadicFractionInterval {
    fn add_assign(&mut self, rhs: &Ratio<BigInt>) {
        self.add_assign(rhs.clone())
    }
}

forward_types_to_bigint!(AddAssign, add_assign, Add, add);
forward_op_to_op_assign!(AddAssign, add_assign, Add, add, DyadicFractionInterval);
forward_op_to_op_assign!(AddAssign, add_assign, Add, add, Ratio<BigInt>);
forward_op_to_op_assign!(AddAssign, add_assign, Add, add, BigInt);

impl SubAssign<DyadicFractionInterval> for DyadicFractionInterval {
    fn sub_assign(&mut self, rhs: DyadicFractionInterval) {
        self.do_sub_assign(Cow::Owned(rhs));
    }
}

impl SubAssign<&'_ DyadicFractionInterval> for DyadicFractionInterval {
    fn sub_assign(&mut self, rhs: &DyadicFractionInterval) {
        self.do_sub_assign(Cow::Borrowed(rhs));
    }
}

impl SubAssign<BigInt> for DyadicFractionInterval {
    fn sub_assign(&mut self, mut rhs: BigInt) {
        rhs <<= self.log2_denom;
        self.lower_bound_numer.sub_assign(&rhs);
        self.upper_bound_numer.sub_assign(rhs);
    }
}

impl SubAssign<&'_ BigInt> for DyadicFractionInterval {
    fn sub_assign(&mut self, rhs: &BigInt) {
        #![allow(clippy::suspicious_op_assign_impl)]
        let rhs = rhs << self.log2_denom;
        self.lower_bound_numer.sub_assign(&rhs);
        self.upper_bound_numer.sub_assign(rhs);
    }
}

impl SubAssign<Ratio<BigInt>> for DyadicFractionInterval {
    fn sub_assign(&mut self, rhs: Ratio<BigInt>) {
        self.sub_assign(DyadicFractionInterval::from_ratio(rhs, self.log2_denom))
    }
}

impl SubAssign<&'_ Ratio<BigInt>> for DyadicFractionInterval {
    fn sub_assign(&mut self, rhs: &Ratio<BigInt>) {
        self.sub_assign(rhs.clone())
    }
}

forward_types_to_bigint!(SubAssign, sub_assign, Sub, sub);
forward_op_to_op_assign!(SubAssign, sub_assign, Sub, sub, DyadicFractionInterval);
forward_op_to_op_assign!(SubAssign, sub_assign, Sub, sub, Ratio<BigInt>);
forward_op_to_op_assign!(SubAssign, sub_assign, Sub, sub, BigInt);

impl MulAssign<DyadicFractionInterval> for DyadicFractionInterval {
    fn mul_assign(&mut self, rhs: DyadicFractionInterval) {
        self.do_mul_assign(Cow::Owned(rhs));
    }
}

impl MulAssign<&'_ DyadicFractionInterval> for DyadicFractionInterval {
    fn mul_assign(&mut self, rhs: &DyadicFractionInterval) {
        self.do_mul_assign(Cow::Borrowed(rhs));
    }
}

impl MulAssign<BigInt> for DyadicFractionInterval {
    fn mul_assign(&mut self, rhs: BigInt) {
        self.do_mul_assign_int(&rhs);
    }
}

impl MulAssign<&'_ BigInt> for DyadicFractionInterval {
    fn mul_assign(&mut self, rhs: &BigInt) {
        self.do_mul_assign_int(rhs);
    }
}

impl MulAssign<Ratio<BigInt>> for DyadicFractionInterval {
    fn mul_assign(&mut self, rhs: Ratio<BigInt>) {
        self.do_mul_assign_ratio(&rhs);
    }
}

impl MulAssign<&'_ Ratio<BigInt>> for DyadicFractionInterval {
    fn mul_assign(&mut self, rhs: &Ratio<BigInt>) {
        self.do_mul_assign_ratio(rhs);
    }
}

forward_types_to_bigint!(MulAssign, mul_assign, Mul, mul);
forward_op_to_op_assign!(MulAssign, mul_assign, Mul, mul, DyadicFractionInterval);
forward_op_to_op_assign!(MulAssign, mul_assign, Mul, mul, Ratio<BigInt>);
forward_op_to_op_assign!(MulAssign, mul_assign, Mul, mul, BigInt);

macro_rules! forward_to_exact_div_assign {
    ($rhs:ty) => {
        impl DivAssign<$rhs> for DyadicFractionInterval {
            fn div_assign(&mut self, rhs: $rhs) {
                self.exact_div_assign(rhs);
            }
        }

        impl AlwaysExactDiv<$rhs> for DyadicFractionInterval {}
        impl<'a> AlwaysExactDiv<$rhs> for &'a DyadicFractionInterval {}
        impl AlwaysExactDivAssign<$rhs> for DyadicFractionInterval {}

        impl ExactDiv<$rhs> for DyadicFractionInterval {
            type Output = DyadicFractionInterval;
            fn exact_div(mut self, rhs: $rhs) -> DyadicFractionInterval {
                self.exact_div_assign(rhs);
                self
            }
            fn checked_exact_div(mut self, rhs: $rhs) -> Option<DyadicFractionInterval> {
                if self.checked_exact_div_assign(rhs).is_ok() {
                    Some(self)
                } else {
                    None
                }
            }
        }

        impl<'a> ExactDiv<$rhs> for &'a DyadicFractionInterval {
            type Output = DyadicFractionInterval;
            fn exact_div(self, rhs: $rhs) -> DyadicFractionInterval {
                self.clone().exact_div(rhs)
            }
            fn checked_exact_div(self, rhs: $rhs) -> Option<DyadicFractionInterval> {
                self.clone().checked_exact_div(rhs)
            }
        }
    };
}

impl ExactDivAssign<DyadicFractionInterval> for DyadicFractionInterval {
    fn exact_div_assign(&mut self, rhs: DyadicFractionInterval) {
        self.do_div_assign(Cow::Owned(rhs))
    }
    fn checked_exact_div_assign(&mut self, rhs: DyadicFractionInterval) -> Result<(), ()> {
        self.do_checked_div_assign(Cow::Owned(rhs))
    }
}

impl ExactDivAssign<&'_ DyadicFractionInterval> for DyadicFractionInterval {
    fn exact_div_assign(&mut self, rhs: &DyadicFractionInterval) {
        self.do_div_assign(Cow::Borrowed(rhs))
    }
    fn checked_exact_div_assign(&mut self, rhs: &DyadicFractionInterval) -> Result<(), ()> {
        self.do_checked_div_assign(Cow::Borrowed(rhs))
    }
}

forward_to_exact_div_assign!(DyadicFractionInterval);
forward_to_exact_div_assign!(&'_ DyadicFractionInterval);

impl DivAssign<BigInt> for DyadicFractionInterval {
    fn div_assign(&mut self, rhs: BigInt) {
        self.do_mul_assign_ratio(&Ratio::new(BigInt::one(), rhs));
    }
}

impl DivAssign<&'_ BigInt> for DyadicFractionInterval {
    fn div_assign(&mut self, rhs: &BigInt) {
        self.do_mul_assign_ratio(&Ratio::new(BigInt::one(), rhs.clone()));
    }
}

impl DivAssign<Ratio<BigInt>> for DyadicFractionInterval {
    fn div_assign(&mut self, rhs: Ratio<BigInt>) {
        self.do_mul_assign_ratio(&rhs.recip());
    }
}

impl DivAssign<&'_ Ratio<BigInt>> for DyadicFractionInterval {
    fn div_assign(&mut self, rhs: &Ratio<BigInt>) {
        self.do_mul_assign_ratio(&rhs.recip());
    }
}

forward_types_to_bigint!(DivAssign, div_assign, Div, div);
forward_op_to_op_assign!(DivAssign, div_assign, Div, div, DyadicFractionInterval);
forward_op_to_op_assign!(DivAssign, div_assign, Div, div, Ratio<BigInt>);
forward_op_to_op_assign!(DivAssign, div_assign, Div, div, BigInt);

impl<E: Integer> Pow<E> for DyadicFractionInterval {
    type Output = DyadicFractionInterval;
    fn pow(mut self, mut exponent: E) -> DyadicFractionInterval {
        if exponent.is_zero() {
            self.set_one();
            self
        } else if exponent.is_one() {
            self
        } else {
            let zero_exponent = E::zero();
            if exponent < zero_exponent {
                exponent = zero_exponent - exponent;
                self = self.recip();
                if exponent.is_one() {
                    return self;
                }
            }
            let contains_zero = self.contains_zero();
            let DyadicFractionInterval {
                lower_bound_numer: mut base_lower_bound_numer,
                upper_bound_numer: mut base_upper_bound_numer,
                log2_denom,
            } = self;
            let mut lower_bound_numer_is_negative = base_lower_bound_numer.is_negative();
            let mut upper_bound_numer_is_negative = base_upper_bound_numer.is_negative();
            if lower_bound_numer_is_negative {
                base_lower_bound_numer = -base_lower_bound_numer;
            }
            if upper_bound_numer_is_negative {
                base_upper_bound_numer = -base_upper_bound_numer;
            }
            let mut bounds_swapped = base_lower_bound_numer > base_upper_bound_numer;
            if bounds_swapped {
                mem::swap(&mut base_lower_bound_numer, &mut base_upper_bound_numer);
            }
            if exponent.is_even() {
                lower_bound_numer_is_negative = false;
                upper_bound_numer_is_negative = false;
                bounds_swapped = false;
                if contains_zero {
                    base_lower_bound_numer.set_zero();
                }
            }
            let mut retval_upper_bound_numer = BigInt::one() << log2_denom;
            let mut retval_lower_bound_numer = retval_upper_bound_numer.clone();
            let mut neg_retval_upper_bound_numer = -retval_upper_bound_numer;
            loop {
                if exponent.is_odd() {
                    retval_lower_bound_numer *= &base_lower_bound_numer;
                    retval_lower_bound_numer >>= log2_denom;
                    neg_retval_upper_bound_numer *= &base_upper_bound_numer;
                    neg_retval_upper_bound_numer >>= log2_denom;
                }
                let two = E::one() + E::one();
                exponent = exponent / two;
                if exponent.is_zero() {
                    break;
                }
                base_lower_bound_numer = &base_lower_bound_numer * &base_lower_bound_numer;
                base_lower_bound_numer >>= log2_denom;
                base_upper_bound_numer = -&base_upper_bound_numer * &base_upper_bound_numer;
                base_upper_bound_numer >>= log2_denom;
                base_upper_bound_numer = -base_upper_bound_numer;
            }
            retval_upper_bound_numer = -neg_retval_upper_bound_numer;
            if bounds_swapped {
                mem::swap(&mut retval_lower_bound_numer, &mut retval_upper_bound_numer);
            }
            if lower_bound_numer_is_negative {
                retval_lower_bound_numer = -retval_lower_bound_numer;
            }
            if upper_bound_numer_is_negative {
                retval_upper_bound_numer = -retval_upper_bound_numer;
            }
            DyadicFractionInterval {
                lower_bound_numer: retval_lower_bound_numer,
                upper_bound_numer: retval_upper_bound_numer,
                log2_denom,
            }
        }
    }
}

impl<E: Integer> Pow<E> for &'_ DyadicFractionInterval {
    type Output = DyadicFractionInterval;
    fn pow(self, exponent: E) -> DyadicFractionInterval {
        self.clone().pow(exponent)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::{test_checked_op_helper, test_op_helper, test_unary_op_helper};
    use num_traits::ToPrimitive;
    use std::{
        borrow::{Borrow, BorrowMut},
        convert::TryInto,
        ops::{Deref, DerefMut},
    };

    type DFI = DyadicFractionInterval;

    #[derive(Clone)]
    struct SameWrapper<T: Borrow<DFI>>(T);

    impl<T: Borrow<DFI>> Deref for SameWrapper<T> {
        type Target = DFI;
        fn deref(&self) -> &DFI {
            self.0.borrow()
        }
    }

    impl<T: BorrowMut<DFI>> DerefMut for SameWrapper<T> {
        fn deref_mut(&mut self) -> &mut DFI {
            self.0.borrow_mut()
        }
    }

    impl<T: Borrow<DFI>> PartialEq for SameWrapper<T> {
        fn eq(&self, rhs: &Self) -> bool {
            self.is_same(rhs)
        }
    }

    impl<T: Borrow<DFI>> fmt::Debug for SameWrapper<T> {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            fmt::Debug::fmt(&**self, f)
        }
    }

    macro_rules! assert_same {
        ($a:expr, $b:expr) => {
            assert_eq!(SameWrapper($a), SameWrapper($b));
        };
        ($a:expr, $b:expr,) => {
            assert_same!($a, $b)
        };
        ($a:expr, $b:expr, $($msg:tt)+) => {
            assert_eq!(SameWrapper($a), SameWrapper($b), $($msg)+);
        };
    }

    fn r(n: i128, d: i128) -> Ratio<BigInt> {
        Ratio::new(n.into(), d.into())
    }

    fn ri(v: i128) -> Ratio<BigInt> {
        bi(v).into()
    }

    fn bi(v: i128) -> BigInt {
        v.into()
    }

    #[test]
    fn test_from_ratio_range() {
        assert_same!(
            DFI::from_ratio_range(r(2, 3), r(5, 7), 8),
            DFI::new(bi(170), bi(183), 8)
        );
        assert_same!(
            DFI::from_ratio_range(ri(-1), r(-5, 7), 8),
            DFI::new(bi(-256), bi(-182), 8)
        );
        assert_same!(
            DFI::from_ratio_range(r(5, 32), r(45, 32), 5),
            DFI::new(bi(5), bi(45), 5)
        );
        assert_same!(
            DFI::from_ratio_range(r(7, 32), r(8, 32), 5),
            DFI::new(bi(7), bi(8), 5)
        );
    }

    #[test]
    fn test_from_ratio() {
        assert_same!(DFI::from_ratio(r(2, 3), 8), DFI::new(bi(170), bi(171), 8));
        assert_same!(
            DFI::from_ratio(r(-2, 3), 8),
            DFI::new(bi(-171), bi(-170), 8)
        );
        assert_same!(DFI::from_ratio(r(1, 8), 8), DFI::new(bi(32), bi(32), 8));
    }

    #[test]
    fn test_convert_log2_denom() {
        assert_same!(
            DFI::new(bi(1), bi(2), 0).into_converted_log2_denom(2),
            DFI::new(bi(4), bi(8), 2)
        );
        assert_same!(
            DFI::new(bi(-2), bi(-1), 0).into_converted_log2_denom(2),
            DFI::new(bi(-8), bi(-4), 2)
        );
        assert_same!(
            DFI::new(bi(4), bi(8), 2).into_converted_log2_denom(0),
            DFI::new(bi(1), bi(2), 0)
        );
        assert_same!(
            DFI::new(bi(7), bi(7), 2).into_converted_log2_denom(0),
            DFI::new(bi(1), bi(2), 0)
        );
        assert_same!(
            DFI::new(bi(6), bi(6), 2).into_converted_log2_denom(0),
            DFI::new(bi(1), bi(2), 0)
        );
        assert_same!(
            DFI::new(bi(5), bi(5), 2).into_converted_log2_denom(0),
            DFI::new(bi(1), bi(2), 0)
        );
        assert_same!(
            DFI::new(bi(4), bi(4), 2).into_converted_log2_denom(0),
            DFI::new(bi(1), bi(1), 0)
        );
        assert_same!(
            DFI::new(bi(8), bi(8), 2).into_converted_log2_denom(0),
            DFI::new(bi(2), bi(2), 0)
        );
        assert_same!(
            DFI::new(bi(-8), bi(-4), 2).into_converted_log2_denom(0),
            DFI::new(bi(-2), bi(-1), 0)
        );
        assert_same!(
            DFI::new(bi(-7), bi(-7), 2).into_converted_log2_denom(0),
            DFI::new(bi(-2), bi(-1), 0)
        );
        assert_same!(
            DFI::new(bi(-6), bi(-6), 2).into_converted_log2_denom(0),
            DFI::new(bi(-2), bi(-1), 0)
        );
        assert_same!(
            DFI::new(bi(-5), bi(-5), 2).into_converted_log2_denom(0),
            DFI::new(bi(-2), bi(-1), 0)
        );
        assert_same!(
            DFI::new(bi(-4), bi(-4), 2).into_converted_log2_denom(0),
            DFI::new(bi(-1), bi(-1), 0)
        );
        assert_same!(
            DFI::new(bi(-8), bi(-8), 2).into_converted_log2_denom(0),
            DFI::new(bi(-2), bi(-2), 0)
        );
    }

    #[test]
    fn test_square() {
        assert_same!(
            DFI::new(bi(1), bi(2), 0).into_square(),
            DFI::new(bi(1), bi(4), 0)
        );
        assert_same!(
            DFI::new(bi(4), bi(5), 0).into_square(),
            DFI::new(bi(16), bi(25), 0)
        );
        assert_same!(
            DFI::new(bi(1), bi(1), 4).into_square(),
            DFI::new(bi(0), bi(1), 4)
        );
        assert_same!(
            DFI::new(bi(16), bi(16), 4).into_square(),
            DFI::new(bi(16), bi(16), 4)
        );
        assert_same!(
            DFI::new(bi(15), bi(15), 4).into_square(),
            DFI::new(bi(14), bi(15), 4)
        );
        assert_same!(
            DFI::new(bi(15), bi(15), 4).into_square(),
            DFI::new(bi(14), bi(15), 4)
        );
        assert_same!(
            DFI::new(bi(-16), bi(16), 4).into_square(),
            DFI::new(bi(0), bi(16), 4)
        );
        assert_same!(
            DFI::new(bi(-4), bi(5), 0).into_square(),
            DFI::new(bi(0), bi(25), 0)
        );
        assert_same!(
            DFI::new(bi(-5), bi(4), 0).into_square(),
            DFI::new(bi(0), bi(25), 0)
        );
        assert_same!(
            DFI::new(bi(-16), bi(-16), 4).into_square(),
            DFI::new(bi(16), bi(16), 4)
        );
        assert_same!(
            DFI::new(bi(-5), bi(-4), 0).into_square(),
            DFI::new(bi(16), bi(25), 0)
        );
    }

    #[test]
    fn test_sqrt() {
        assert_same!(
            DFI::new(bi(0), bi(1), 8).into_sqrt(),
            DFI::new(bi(0), bi(16), 8)
        );
        assert_same!(
            DFI::new(bi(1), bi(2), 8).into_sqrt(),
            DFI::new(bi(16), bi(23), 8)
        );
        assert_same!(
            DFI::new(bi(2), bi(3), 8).into_sqrt(),
            DFI::new(bi(22), bi(28), 8)
        );
        assert_same!(
            DFI::new(bi(3), bi(4), 8).into_sqrt(),
            DFI::new(bi(27), bi(32), 8)
        );
        assert_same!(
            DFI::new(bi(4), bi(5), 8).into_sqrt(),
            DFI::new(bi(32), bi(36), 8)
        );
        assert_same!(
            DFI::new(bi(512), bi(512), 8).into_sqrt(),
            DFI::new(bi(362), bi(363), 8)
        );
    }

    #[test]
    fn test_arithmetic_geometric_mean() {
        assert_same!(
            DFI::new(bi(0), bi(1), 8).into_arithmetic_geometric_mean(DFI::new(bi(0), bi(1), 8)),
            DFI::new(bi(0), bi(1), 8),
        );
        assert_same!(
            DFI::new(bi(256), bi(256), 8).into_arithmetic_geometric_mean(DFI::new(
                bi(512),
                bi(512),
                8
            )),
            DFI::new(bi(372), bi(374), 8),
        );
        assert_same!(
            DFI::new(bi(1) << 64, bi(1) << 64, 64).into_arithmetic_geometric_mean(DFI::new(
                bi(2) << 64,
                bi(2) << 64,
                64
            )),
            DFI::new(
                bi(26_873_051_318_597_756_702),
                bi(26_873_051_318_597_756_707),
                64
            ),
        );
    }

    #[test]
    fn test_debug() {
        assert_eq!(
            &format!("{:?}", DFI::new(bi(-123), bi(456), 789)),
            "DyadicFractionInterval { lower_bound_numer: -123, upper_bound_numer: 456, log2_denom: 789 }",
        );
        assert_eq!(
            &format!("{:#?}", DFI::new(bi(-123), bi(456), 789)),
            "DyadicFractionInterval {\n    lower_bound_numer: -123,\n    upper_bound_numer: 456,\n    log2_denom: 789,\n}",
        );
    }

    #[test]
    fn test_display() {
        assert_eq!(
            &format!("{}", DFI::new(bi(-123), bi(456), 789)),
            "[-123 / 2^789, 456 / 2^789]",
        );
    }

    #[test]
    fn test_interval_union() {
        fn test_case(lhs: DFI, rhs: DFI, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs.clone()),
                SameWrapper(rhs.clone()),
                &SameWrapper(expected.clone()),
                |SameWrapper(a), SameWrapper(b)| a.interval_union_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.interval_union_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
            );
            test_op_helper(
                SameWrapper(rhs),
                SameWrapper(lhs),
                &SameWrapper(expected),
                |SameWrapper(a), SameWrapper(b)| a.interval_union_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.interval_union_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.interval_union(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(3), bi(97), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(3), bi(194), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(6), bi(97), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(3), bi(97), 1),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-3), bi(97), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-5), bi(97), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-5), bi(97), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(-17), bi(97), 1),
            DFI::new(bi(-17), bi(97), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(-97), bi(17), 1),
            DFI::new(bi(-97), bi(17), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(-97), bi(-17), 1),
            DFI::new(bi(-97), bi(5), 1),
        );
    }

    #[test]
    fn test_add() {
        fn test_case(lhs: DFI, rhs: DFI, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs.clone()),
                SameWrapper(rhs.clone()),
                &SameWrapper(expected.clone()),
                |SameWrapper(a), SameWrapper(b)| a.add_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.add_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
            );
            test_op_helper(
                SameWrapper(rhs),
                SameWrapper(lhs),
                &SameWrapper(expected),
                |SameWrapper(a), SameWrapper(b)| a.add_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.add_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.add(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(20), bi(102), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(37), bi(199), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(23), bi(107), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(20), bi(102), 1),
        );
    }

    #[test]
    fn test_add_int() {
        fn test_case(lhs: DFI, rhs: BigInt, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.add_assign(b),
                |SameWrapper(a), b| a.add_assign(b),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            bi(23),
            DFI::new(bi(26), bi(28), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            bi(23),
            DFI::new(bi(49), bi(51), 1),
        );
    }

    #[test]
    fn test_add_ratio() {
        fn test_case(lhs: DFI, rhs: Ratio<BigInt>, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.add_assign(b),
                |SameWrapper(a), b| a.add_assign(b),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
                |SameWrapper(a), b| SameWrapper(a.add(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(7, 5),
            DFI::new(bi(4), bi(7), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(-7, 5),
            DFI::new(bi(1), bi(4), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            r(7, 5),
            DFI::new(bi(361), bi(364), 8),
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            r(-7, 5),
            DFI::new(bi(-356), bi(-353), 8),
        );
    }

    #[test]
    fn test_sub() {
        fn test_case(lhs: DFI, rhs: DFI, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs.clone()),
                SameWrapper(rhs.clone()),
                &SameWrapper(expected.clone()),
                |SameWrapper(a), SameWrapper(b)| a.sub_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.sub_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
            );
            test_op_helper(
                SameWrapper(-rhs),
                SameWrapper(-lhs),
                &SameWrapper(expected),
                |SameWrapper(a), SameWrapper(b)| a.sub_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.sub_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.sub(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-94), bi(-12), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-191), bi(-29), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(-91), bi(-7), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(-94), bi(-12), 1),
        );
    }

    #[test]
    fn test_sub_int() {
        fn test_case(lhs: DFI, rhs: BigInt, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.sub_assign(b),
                |SameWrapper(a), b| a.sub_assign(b),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            bi(23),
            DFI::new(bi(-20), bi(-18), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            bi(23),
            DFI::new(bi(-43), bi(-41), 1),
        );
    }

    #[test]
    fn test_sub_ratio() {
        fn test_case(lhs: DFI, rhs: Ratio<BigInt>, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.sub_assign(b),
                |SameWrapper(a), b| a.sub_assign(b),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
                |SameWrapper(a), b| SameWrapper(a.sub(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(7, 5),
            DFI::new(bi(1), bi(4), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(-7, 5),
            DFI::new(bi(4), bi(7), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            r(7, 5),
            DFI::new(bi(-356), bi(-353), 8),
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            r(-7, 5),
            DFI::new(bi(361), bi(364), 8),
        );
    }

    #[test]
    fn test_mul() {
        fn test_case(lhs: DFI, rhs: DFI, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs.clone()),
                SameWrapper(rhs.clone()),
                &SameWrapper(expected.clone()),
                |SameWrapper(a), SameWrapper(b)| a.mul_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.mul_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
            );
            test_op_helper(
                SameWrapper(rhs),
                SameWrapper(lhs),
                &SameWrapper(expected),
                |SameWrapper(a), SameWrapper(b)| a.mul_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.mul_assign(b),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
                |SameWrapper(a), SameWrapper(b)| SameWrapper(a.mul(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(51), bi(485), 0),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-291), bi(485), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-485), bi(291), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 0),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(-485), bi(-51), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(-17), bi(97), 0),
            DFI::new(bi(-85), bi(485), 0),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 0),
            DFI::new(bi(-17), bi(97), 0),
            DFI::new(bi(-291), bi(485), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 0),
            DFI::new(bi(-17), bi(97), 0),
            DFI::new(bi(-485), bi(291), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 0),
            DFI::new(bi(-17), bi(97), 0),
            DFI::new(bi(-485), bi(85), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(-97), bi(17), 0),
            DFI::new(bi(-485), bi(85), 0),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 0),
            DFI::new(bi(-97), bi(17), 0),
            DFI::new(bi(-485), bi(291), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 0),
            DFI::new(bi(-97), bi(17), 0),
            DFI::new(bi(-291), bi(485), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 0),
            DFI::new(bi(-97), bi(17), 0),
            DFI::new(bi(-85), bi(485), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(-97), bi(-17), 0),
            DFI::new(bi(-485), bi(-51), 0),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 0),
            DFI::new(bi(-97), bi(-17), 0),
            DFI::new(bi(-485), bi(291), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 0),
            DFI::new(bi(-97), bi(-17), 0),
            DFI::new(bi(-291), bi(485), 0),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 0),
            DFI::new(bi(-97), bi(-17), 0),
            DFI::new(bi(51), bi(485), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 0),
            DFI::new(bi(51), bi(485), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(51), bi(485), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            DFI::new(bi(17), bi(97), 1),
            DFI::new(bi(25), bi(243), 1),
        );
    }

    #[test]
    fn test_mul_int() {
        fn test_case(lhs: DFI, rhs: BigInt, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.mul_assign(b),
                |SameWrapper(a), b| a.mul_assign(b),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            bi(23),
            DFI::new(bi(69), bi(115), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            bi(23),
            DFI::new(bi(69), bi(115), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            bi(-23),
            DFI::new(bi(-115), bi(-69), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            bi(-23),
            DFI::new(bi(-115), bi(-69), 1),
        );
    }

    #[test]
    fn test_mul_ratio() {
        fn test_case(lhs: DFI, rhs: Ratio<BigInt>, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.mul_assign(b),
                |SameWrapper(a), b| a.mul_assign(b),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
                |SameWrapper(a), b| SameWrapper(a.mul(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(23, 7),
            DFI::new(bi(9), bi(17), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            r(23, 7),
            DFI::new(bi(9), bi(17), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(-23, 7),
            DFI::new(bi(-17), bi(-9), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            r(-23, 7),
            DFI::new(bi(-17), bi(-9), 1),
        );
        test_case(DFI::new(bi(3), bi(5), 0), ri(3), DFI::new(bi(9), bi(15), 0));
        test_case(
            DFI::new(bi(3), bi(5), 0),
            ri(-3),
            DFI::new(bi(-15), bi(-9), 0),
        );
    }

    #[test]
    fn test_div() {
        fn test_case(lhs: DFI, rhs: DFI, expected: Option<DFI>) {
            test_checked_op_helper(
                SameWrapper(lhs),
                SameWrapper(rhs),
                &expected.map(SameWrapper),
                |SameWrapper(a), SameWrapper(b)| a.checked_exact_div_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.checked_exact_div_assign(b),
                |SameWrapper(a), SameWrapper(b)| a.checked_exact_div(b).map(SameWrapper),
                |SameWrapper(a), SameWrapper(b)| a.checked_exact_div(b).map(SameWrapper),
                |SameWrapper(a), SameWrapper(b)| a.checked_exact_div(b).map(SameWrapper),
                |SameWrapper(a), SameWrapper(b)| a.checked_exact_div(b).map(SameWrapper),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 8),
            DFI::new(bi(17), bi(97), 8),
            Some(DFI::new(bi(7), bi(76), 8)),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 8),
            DFI::new(bi(17), bi(97), 8),
            Some(DFI::new(bi(-46), bi(76), 8)),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 8),
            DFI::new(bi(17), bi(97), 8),
            Some(DFI::new(bi(-76), bi(46), 8)),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 8),
            DFI::new(bi(17), bi(97), 8),
            Some(DFI::new(bi(-76), bi(-7), 8)),
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            DFI::new(bi(-17), bi(97), 8),
            None,
        );
        test_case(
            DFI::new(bi(-3), bi(5), 8),
            DFI::new(bi(-17), bi(97), 8),
            None,
        );
        test_case(
            DFI::new(bi(-5), bi(3), 8),
            DFI::new(bi(-17), bi(97), 8),
            None,
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 8),
            DFI::new(bi(-17), bi(97), 8),
            None,
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            DFI::new(bi(-97), bi(17), 8),
            None,
        );
        test_case(
            DFI::new(bi(-3), bi(5), 8),
            DFI::new(bi(-97), bi(17), 8),
            None,
        );
        test_case(
            DFI::new(bi(-5), bi(3), 8),
            DFI::new(bi(-97), bi(17), 8),
            None,
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 8),
            DFI::new(bi(-97), bi(17), 8),
            None,
        );
        test_case(
            DFI::new(bi(3), bi(5), 8),
            DFI::new(bi(-97), bi(-17), 8),
            Some(DFI::new(bi(-76), bi(-7), 8)),
        );
        test_case(
            DFI::new(bi(-3), bi(5), 8),
            DFI::new(bi(-97), bi(-17), 8),
            Some(DFI::new(bi(-76), bi(46), 8)),
        );
        test_case(
            DFI::new(bi(-5), bi(3), 8),
            DFI::new(bi(-97), bi(-17), 8),
            Some(DFI::new(bi(-46), bi(76), 8)),
        );
        test_case(
            DFI::new(bi(-5), bi(-3), 8),
            DFI::new(bi(-97), bi(-17), 8),
            Some(DFI::new(bi(7), bi(76), 8)),
        );
        test_case(
            DFI::from_int(bi(1), 64),
            DFI::from_int(bi(3), 64),
            Some(DFI::new(
                bi(6_148_914_691_236_517_205),
                bi(6_148_914_691_236_517_206),
                64,
            )),
        );
    }

    #[test]
    fn test_div_int() {
        fn test_case(lhs: DFI, rhs: BigInt, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.div_assign(b),
                |SameWrapper(a), b| a.div_assign(b),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
            );
        }
        test_case(
            DFI::new(bi(35), bi(72), 0),
            bi(11),
            DFI::new(bi(3), bi(7), 0),
        );
        test_case(
            DFI::new(bi(35), bi(72), 1),
            bi(11),
            DFI::new(bi(3), bi(7), 1),
        );
        test_case(
            DFI::new(bi(35), bi(72), 0),
            bi(-11),
            DFI::new(bi(-7), bi(-3), 0),
        );
        test_case(
            DFI::new(bi(35), bi(72), 1),
            bi(-11),
            DFI::new(bi(-7), bi(-3), 1),
        );
        test_case(
            DFI::new(bi(35), bi(72), 0),
            bi(3),
            DFI::new(bi(11), bi(24), 0),
        );
        test_case(
            DFI::new(bi(35), bi(72), 0),
            bi(5),
            DFI::new(bi(7), bi(15), 0),
        );
    }

    #[test]
    fn test_div_ratio() {
        fn test_case(lhs: DFI, rhs: Ratio<BigInt>, expected: DFI) {
            test_op_helper(
                SameWrapper(lhs),
                rhs,
                &SameWrapper(expected),
                |SameWrapper(a), b| a.div_assign(b),
                |SameWrapper(a), b| a.div_assign(b),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
                |SameWrapper(a), b| SameWrapper(a.div(b)),
            );
        }
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(7, 23),
            DFI::new(bi(9), bi(17), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            r(7, 23),
            DFI::new(bi(9), bi(17), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(-7, 23),
            DFI::new(bi(-17), bi(-9), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 1),
            r(-7, 23),
            DFI::new(bi(-17), bi(-9), 1),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(1, 3),
            DFI::new(bi(9), bi(15), 0),
        );
        test_case(
            DFI::new(bi(3), bi(5), 0),
            r(-1, 3),
            DFI::new(bi(-15), bi(-9), 0),
        );
    }

    #[test]
    fn test_pow() {
        fn test_case(lhs: DFI, rhs: i64, expected: DFI) {
            test_unary_op_helper(
                SameWrapper(lhs),
                &SameWrapper(expected),
                |SameWrapper(a)| SameWrapper(a.pow(rhs)),
                |SameWrapper(a)| SameWrapper(a.pow(rhs)),
            );
        }
        test_case(DFI::new(bi(5), bi(7), 0), 0, DFI::new(bi(1), bi(1), 0));
        test_case(DFI::new(bi(5), bi(7), 0), 1, DFI::new(bi(5), bi(7), 0));
        test_case(DFI::new(bi(5), bi(7), 0), 2, DFI::new(bi(25), bi(49), 0));
        test_case(DFI::new(bi(5), bi(7), 0), 3, DFI::new(bi(125), bi(343), 0));
        test_case(DFI::new(bi(5), bi(7), 0), 4, DFI::new(bi(625), bi(2401), 0));
        test_case(
            DFI::new(bi(5), bi(7), 0),
            5,
            DFI::new(bi(3125), bi(16807), 0),
        );
        test_case(
            DFI::new(bi(255), bi(257), 8),
            0,
            DFI::new(bi(256), bi(256), 8),
        );
        test_case(
            DFI::new(bi(255), bi(257), 8),
            1,
            DFI::new(bi(255), bi(257), 8),
        );
        test_case(
            DFI::new(bi(255), bi(257), 8),
            2,
            DFI::new(bi(254), bi(259), 8),
        );
        test_case(
            DFI::new(bi(255), bi(257), 8),
            3,
            DFI::new(bi(253), bi(261), 8),
        );
        test_case(DFI::new(bi(-5), bi(7), 0), 0, DFI::new(bi(1), bi(1), 0));
        test_case(DFI::new(bi(-5), bi(7), 0), 1, DFI::new(bi(-5), bi(7), 0));
        test_case(DFI::new(bi(-5), bi(7), 0), 2, DFI::new(bi(0), bi(49), 0));
        test_case(
            DFI::new(bi(-5), bi(7), 0),
            3,
            DFI::new(bi(-125), bi(343), 0),
        );
        test_case(DFI::new(bi(-5), bi(7), 0), 4, DFI::new(bi(0), bi(2401), 0));
        test_case(
            DFI::new(bi(-5), bi(7), 0),
            5,
            DFI::new(bi(-3125), bi(16807), 0),
        );
        test_case(DFI::new(bi(-7), bi(5), 0), 0, DFI::new(bi(1), bi(1), 0));
        test_case(DFI::new(bi(-7), bi(5), 0), 1, DFI::new(bi(-7), bi(5), 0));
        test_case(DFI::new(bi(-7), bi(5), 0), 2, DFI::new(bi(0), bi(49), 0));
        test_case(
            DFI::new(bi(-7), bi(5), 0),
            3,
            DFI::new(bi(-343), bi(125), 0),
        );
        test_case(DFI::new(bi(-7), bi(5), 0), 4, DFI::new(bi(0), bi(2401), 0));
        test_case(
            DFI::new(bi(-7), bi(5), 0),
            5,
            DFI::new(bi(-16807), bi(3125), 0),
        );
        test_case(DFI::new(bi(-7), bi(-5), 0), 0, DFI::new(bi(1), bi(1), 0));
        test_case(DFI::new(bi(-7), bi(-5), 0), 1, DFI::new(bi(-7), bi(-5), 0));
        test_case(DFI::new(bi(-7), bi(-5), 0), 2, DFI::new(bi(25), bi(49), 0));
        test_case(
            DFI::new(bi(-7), bi(-5), 0),
            3,
            DFI::new(bi(-343), bi(-125), 0),
        );
        test_case(
            DFI::new(bi(-7), bi(-5), 0),
            4,
            DFI::new(bi(625), bi(2401), 0),
        );
        test_case(
            DFI::new(bi(-7), bi(-5), 0),
            5,
            DFI::new(bi(-16807), bi(-3125), 0),
        );
        test_case(DFI::from_int(bi(3), 8), -1, DFI::new(bi(85), bi(86), 8));
        test_case(DFI::from_int(bi(3), 8), -2, DFI::new(bi(28), bi(29), 8));
        test_case(DFI::from_int(bi(3), 8), -3, DFI::new(bi(9), bi(10), 8));
        test_case(DFI::from_int(bi(3), 8), -4, DFI::new(bi(3), bi(4), 8));
        test_case(DFI::from_int(bi(3), 8), -5, DFI::new(bi(0), bi(2), 8));
        test_case(DFI::from_int(bi(3), 8), -6, DFI::new(bi(0), bi(1), 8));
    }

    #[test]
    fn test_natural_log_of_2() {
        for _ in 0..5 {
            assert_same!(
                DFI::natural_log_of_2(64),
                DFI::new(
                    bi(12_786_308_645_202_655_659),
                    bi(12_786_308_645_202_655_660),
                    64
                )
            );
            assert_same!(
                DFI::natural_log_of_2(128),
                DFI::new(
                    BigInt::from(235_865_763_225_513_294_137_944_142_764_154_484_399u128),
                    BigInt::from(235_865_763_225_513_294_137_944_142_764_154_484_400u128),
                    128
                )
            );
        }
    }

    #[test]
    fn test_log_core() {
        assert_same!(
            DFI::from_ratio(ri(2), 64).log_core(), // calculate log(3)
            DFI::new(
                bi(20_265_819_725_292_939_638),
                bi(20_265_819_725_292_939_639),
                64
            )
        );
        assert_same!(
            DFI::from_ratio(ri(2), 128).log_core(), // calculate log(3)
            DFI::new(
                "373838389916413667603494184660470824117".parse().unwrap(),
                "373838389916413667603494184660470824118".parse().unwrap(),
                128
            )
        );
        assert_same!(
            DFI::from_ratio(ri(3), 64).log_core(), // calculate log(2)
            DFI::new(
                bi(12_786_308_645_202_655_659),
                bi(12_786_308_645_202_655_660),
                64
            )
        );
        assert_same!(
            DFI::from_ratio(ri(3), 128).log_core(), // calculate log(2)
            DFI::new(
                BigInt::from(235_865_763_225_513_294_137_944_142_764_154_484_399u128),
                BigInt::from(235_865_763_225_513_294_137_944_142_764_154_484_400u128),
                128
            )
        );
        assert_same!(
            DFI::from_ratio(ri(9), 64).log_core(), // calculate log(5 / 4)
            DFI::new(
                bi(4_116_271_982_791_902_040),
                bi(4_116_271_982_791_902_041),
                64
            )
        );
        assert_same!(
            DFI::from_ratio(ri(9), 128).log_core(), // calculate log(5 / 4)
            DFI::new(
                BigInt::from(75_931_815_804_343_184_391_506_054_410_983_916_693u128),
                BigInt::from(75_931_815_804_343_184_391_506_054_410_983_916_694u128),
                128
            )
        );
        assert_same!(
            DFI::from_ratio(r(13, 3), 64).log_core(), // calculate log(8 / 5)
            DFI::new(
                bi(8_670_036_662_410_753_619),
                bi(8_670_036_662_410_753_620),
                64
            )
        );
        assert_same!(
            DFI::from_ratio(r(13, 3), 80).log_core(), // calculate log(8 / 5)
            DFI::new(
                bi(568_199_522_707_751_149_207_091),
                bi(568_199_522_707_751_149_207_092),
                80
            )
        );
        assert_same!(
            DFI::from_ratio(r(13, 3), 128).log_core(), // calculate log(8 / 5)
            DFI::new(
                BigInt::from(159_933_947_421_170_109_746_438_088_353_170_567_705u128),
                BigInt::from(159_933_947_421_170_109_746_438_088_353_170_567_706u128),
                128
            )
        );
    }

    #[test]
    fn test_log() {
        assert_same!(
            DFI::from_ratio_range(r(4, 5), r(123, 45), 64).log(),
            DFI::new(
                bi(-4_116_271_982_791_902_042),
                bi(18_548_604_515_280_868_688),
                64
            )
        );
        assert_same!(
            DFI::from_ratio_range(r(4, 5), r(123, 45), 127).log(),
            DFI::new(
                bi(-37_965_907_902_171_592_195_753_027_205_491_958_348),
                BigInt::from(171_080_680_208_919_797_346_165_683_845_098_625_899u128),
                127
            )
        );
        assert_same!(
            DFI::from_ratio(r(12345, 2), 64).log(),
            DFI::new(
                bi(161_000_585_365_199_022_398),
                bi(161_000_585_365_199_022_399),
                64
            )
        );
        for i in 2..30 {
            fn do_test(i: usize, input: DFI) {
                assert!(input.log2_denom < 50);
                println!("i = {}", i);
                dbg!(&input);
                let input_denom = 2.0f64.powi(input.log2_denom.try_into().unwrap());
                let input_lower_bound = input.lower_bound_numer.to_f64().unwrap() / input_denom;
                let input_upper_bound = input.upper_bound_numer.to_f64().unwrap() / input_denom;
                let expected = DFI::from_ratio_range(
                    Ratio::<BigInt>::from_float(input_lower_bound.ln()).unwrap(),
                    Ratio::<BigInt>::from_float(input_upper_bound.ln()).unwrap(),
                    input.log2_denom,
                );
                assert_same!(input.log(), expected);
            }
            do_test(i, DFI::from_int(BigInt::from(i), 32));
            do_test(
                i,
                DFI::from_ratio(Ratio::new(BigInt::one(), BigInt::from(i)), 32),
            );
        }
    }

    #[test]
    fn test_exp() {
        assert_same!(
            DFI::from_int_range(bi(0), bi(0), 64).exp(),
            DFI::new(
                bi(18_446_744_073_709_551_616),
                bi(18_446_744_073_709_551_616),
                64
            )
        );
        assert_same!(
            DFI::from_int_range(bi(0), bi(1), 64).exp(),
            DFI::new(
                bi(18_446_744_073_709_551_616),
                bi(50_143_449_209_799_256_683),
                64
            )
        );
        assert_same!(
            DFI::from_int_range(bi(1), bi(1), 64).exp(),
            DFI::new(
                bi(50_143_449_209_799_256_682),
                bi(50_143_449_209_799_256_683),
                64
            )
        );
        assert_same!(
            DFI::from_int_range(bi(1), bi(1), 120).exp(),
            DFI::new(
                bi(3_613_216_306_821_173_191_995_746_233_763_034_355),
                bi(3_613_216_306_821_173_191_995_746_233_763_034_356),
                120
            )
        );
        assert_same!(
            DFI::from_ratio_range(r(1, 16), r(1, 16), 64).exp(),
            DFI::new(
                bi(19_636_456_851_539_679_189),
                bi(19_636_456_851_539_679_190),
                64
            )
        );
        assert_same!(
            DFI::from_ratio_range(r(1, 16), r(5, 11), 64).exp(),
            DFI::new(
                bi(19_636_456_851_539_679_189),
                bi(29_062_053_985_348_969_808),
                64
            )
        );
        assert_same!(
            DFI::from_ratio(r(12345, 20), 120).exp(),
            DFI::new(
                "15554943374427623479586295616005556713817814660873673636717540447365020\
                 241010687483038422716174364856604938959636391301874371790367372240576361413166\
                 945168943074910853869056633171038088299306405677231299055607307283566273703681\
                 161420276716135018812123397822555186980209038935457373851383684897298980152385"
                    .parse()
                    .unwrap(),
                "15554943374427623479586295616005556713817814660873673636717540447365020\
                 241010687483038422716174364856604938959636391301874371790367372240576361413166\
                 945168943074910853869056633171038088299306405677231299055607307283566273703681\
                 161420276716135018812123397822555186980209038935457373851383684897298980152386"
                    .parse()
                    .unwrap(),
                120
            )
        );

        // check that we don't overflow where we don't need to
        assert_same!(
            DFI::from_int(bi(-99_999_999_999_999_999_999_999_999), 120).exp(),
            DFI::new(bi(0), bi(1), 120)
        );

        for i in (1..30).rev() {
            fn do_test(i: i64, input: DFI) {
                assert!(input.log2_denom < 50);
                println!("i = {}", i);
                dbg!(&input);
                let input_denom = 2.0f64.powi(input.log2_denom.try_into().unwrap());
                let input_lower_bound = input.lower_bound_numer.to_f64().unwrap() / input_denom;
                let input_upper_bound = input.upper_bound_numer.to_f64().unwrap() / input_denom;
                let expected = DFI::from_ratio_range(
                    Ratio::<BigInt>::from_float(input_lower_bound.exp()).unwrap(),
                    Ratio::<BigInt>::from_float(input_upper_bound.exp()).unwrap(),
                    input.log2_denom,
                );
                assert_same!(input.exp(), expected);
            }
            if i <= 3 {
                // f64::exp loses precision really fast, skip in cases where f64::exp is not precise enough
                do_test(i, DFI::from_int(BigInt::from(i), 32));
            }
            do_test(
                i,
                DFI::from_ratio(Ratio::new(BigInt::one(), BigInt::from(i)), 32),
            );
            do_test(i, DFI::from_int(BigInt::from(-i), 32));
            do_test(
                i,
                DFI::from_ratio(Ratio::new(BigInt::one(), BigInt::from(-i)), 32),
            );
        }
    }
}
