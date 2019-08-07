// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use num_bigint::BigInt;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::CheckedAdd;
use num_traits::CheckedMul;
use num_traits::CheckedSub;
use num_traits::FromPrimitive;
use num_traits::One;
use num_traits::Zero;
use std::ops::Add;
use std::ops::AddAssign;
use std::ops::Mul;
use std::ops::MulAssign;
use std::ops::Neg;
use std::ops::Sub;
use std::ops::SubAssign;

pub trait ModularReduce<V: Clone + Eq = Self>: Clone {
    fn modular_reduce_assign<M: Modulus<Value = V>>(&mut self, modulus: M);
    fn modular_reduce<M: Modulus<Value = V>>(mut self, modulus: M) -> Self {
        self.modular_reduce_assign(modulus);
        self
    }
}

pub trait ModularReducePow<E = Self, V: Clone + Eq = Self>: ModularReduce<V> {
    fn pow_modular_reduce<M: Modulus<Value = V>>(&self, exponent: &E, modulus: M) -> Self;
}

pub trait Modulus: Clone + Eq {
    type Value: Clone + Eq;
    fn to_modulus(&self) -> &Self::Value;
    fn into_modulus(self) -> Self::Value {
        self.to_modulus().clone()
    }
}

impl<T: Modulus> Modulus for &'_ T {
    type Value = T::Value;
    fn to_modulus(&self) -> &Self::Value {
        (**self).to_modulus()
    }
}

pub trait StaticModulus: Modulus + 'static + Copy {
    fn get_modulus() -> Self::Value;
}

macro_rules! impl_int_modulus {
    ($t:ty) => {
        impl Modulus for $t {
            type Value = Self;
            fn to_modulus(&self) -> &Self::Value {
                self
            }
            fn into_modulus(self) -> Self::Value {
                self
            }
        }

        impl ModularReduce for $t {
            fn modular_reduce_assign<M: Modulus<Value = Self>>(&mut self, modulus: M) {
                let modulus = modulus.to_modulus();
                if !modulus.is_zero() {
                    *self = self.mod_floor(modulus);
                }
            }
            fn modular_reduce<M: Modulus<Value = Self>>(self, modulus: M) -> Self {
                let modulus = modulus.to_modulus();
                if !modulus.is_zero() {
                    self.mod_floor(modulus)
                } else {
                    self
                }
            }
        }
    };
}

macro_rules! impl_prim_int_modulus {
    ($t:ty) => {
        impl_int_modulus!($t);

        impl<E: Integer + Clone + FromPrimitive> ModularReducePow<E> for $t {
            fn pow_modular_reduce<M: Modulus<Value = Self>>(
                &self,
                exponent: &E,
                modulus: M,
            ) -> Self {
                if exponent.is_zero() {
                    return One::one();
                }
                let modulus = *modulus.to_modulus();
                let mut base = *self;
                base.modular_reduce_assign(modulus);
                if exponent.is_one() {
                    return base;
                }
                let mut exponent = exponent.clone();
                let mut retval = None;
                loop {
                    if exponent.is_odd() {
                        match &mut retval {
                            None => retval = Some(base.clone()),
                            Some(retval) => {
                                *retval *= base; // FIXME: switch to use modular mul to avoid overflow
                                retval.modular_reduce_assign(modulus)
                            }
                        }
                    }
                    exponent = exponent / E::from_u8(2).expect("2 doesn't fit in exponent type");
                    if exponent.is_zero() {
                        break;
                    }
                    base *= base; // FIXME: switch to use modular mul to avoid overflow
                    base.modular_reduce_assign(modulus);
                }
                retval.unwrap_or_else(|| unreachable!())
            }
        }
    };
}

macro_rules! impl_bigint_modulus {
    ($t:ty) => {
        impl_int_modulus!($t);

        impl ModularReducePow for $t {
            fn pow_modular_reduce<M: Modulus<Value = Self>>(
                &self,
                exponent: &Self,
                modulus: M,
            ) -> Self {
                self.modpow(exponent, modulus.to_modulus())
            }
        }
    };
}

impl_prim_int_modulus!(i8);
impl_prim_int_modulus!(u8);
impl_prim_int_modulus!(i16);
impl_prim_int_modulus!(u16);
impl_prim_int_modulus!(i32);
impl_prim_int_modulus!(u32);
impl_prim_int_modulus!(i64);
impl_prim_int_modulus!(u64);
impl_prim_int_modulus!(i128);
impl_prim_int_modulus!(u128);
impl_prim_int_modulus!(isize);
impl_prim_int_modulus!(usize);
impl_bigint_modulus!(BigInt);
impl_bigint_modulus!(BigUint);

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct ModularInteger<V, M> {
    value: V,
    modulus: M,
}

impl<V, M> ModularInteger<V, M> {
    pub fn value(&self) -> &V {
        &self.value
    }
    pub fn modulus(&self) -> &M {
        &self.modulus
    }
}

impl<V: ModularReduce + Eq, M: Modulus<Value = V>> ModularInteger<V, M> {
    fn reduce(&mut self) {
        self.value.modular_reduce_assign(&self.modulus);
    }
}

impl<V, M: PartialEq> ModularInteger<V, M> {
    pub fn has_matching_moduli(&self, rhs: &Self) -> bool {
        self.modulus == rhs.modulus
    }
    fn require_matching_moduli(&self, rhs: &Self) {
        assert!(self.has_matching_moduli(rhs), "moduli don't match");
    }
}

impl<V, M> Into<(V, M)> for ModularInteger<V, M> {
    fn into(self) -> (V, M) {
        (self.value, self.modulus)
    }
}

impl<V: ModularReduce + Eq, M: Modulus<Value = V>> ModularInteger<V, M> {
    pub fn new<T: Into<V>>(value: T, modulus: M) -> Self {
        let value = value.into().modular_reduce(&modulus);
        Self { value, modulus }
    }
}

impl<V: ModularReduce + Eq, M: Modulus<Value = V>> From<(V, M)> for ModularInteger<V, M> {
    fn from((value, modulus): (V, M)) -> Self {
        Self::new(value, modulus)
    }
}

impl<V: ModularReduce + Eq + Add<Output = V>, M: Modulus<Value = V>> Add for ModularInteger<V, M> {
    type Output = ModularInteger<V, M>;
    fn add(self, rhs: Self) -> Self::Output {
        self.require_matching_moduli(&rhs);
        ModularInteger::new(self.value.add(rhs.value), self.modulus)
    }
}

impl<V: ModularReduce + Eq + AddAssign, M: Modulus<Value = V>> AddAssign for ModularInteger<V, M> {
    fn add_assign(&mut self, rhs: Self) {
        self.require_matching_moduli(&rhs);
        self.value.add_assign(rhs.value);
        self.reduce();
    }
}

impl<'r, V: ModularReduce + Eq + for<'a> AddAssign<&'a V>, M: Modulus<Value = V>>
    AddAssign<&'r ModularInteger<V, M>> for ModularInteger<V, M>
{
    fn add_assign(&mut self, rhs: &Self) {
        self.require_matching_moduli(&rhs);
        self.value.add_assign(&rhs.value);
        self.reduce();
    }
}

impl<'r, V: 'r + ModularReduce + Eq, M: Modulus<Value = V>> Add<&'r ModularInteger<V, M>>
    for ModularInteger<V, M>
where
    for<'a> V: Add<&'a V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn add(self, rhs: &ModularInteger<V, M>) -> Self::Output {
        self.require_matching_moduli(rhs);
        ModularInteger::new(self.value.add(&rhs.value), self.modulus)
    }
}

impl<'l, V: ModularReduce + Eq, M: Modulus<Value = V>> Add<ModularInteger<V, M>>
    for &'l ModularInteger<V, M>
where
    for<'a> &'a V: Add<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn add(self, rhs: ModularInteger<V, M>) -> Self::Output {
        self.require_matching_moduli(&rhs);
        ModularInteger::new(self.value.add(rhs.value), rhs.modulus)
    }
}

impl<'l, 'r, V: 'r + ModularReduce + Eq, M: Modulus<Value = V>> Add<&'r ModularInteger<V, M>>
    for &'l ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Add<&'b V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn add(self, rhs: &ModularInteger<V, M>) -> Self::Output {
        self.require_matching_moduli(rhs);
        ModularInteger::new(self.value.add(&rhs.value), self.modulus.clone())
    }
}

impl<V: ModularReduce + Eq + Add<Output = V>, M: Modulus<Value = V>> CheckedAdd
    for ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Add<&'b V, Output = V>,
{
    fn checked_add(&self, rhs: &Self) -> Option<Self> {
        if !self.has_matching_moduli(rhs) {
            return None;
        }
        Some(ModularInteger::new(
            (&self.value).add(&rhs.value),
            self.modulus.clone(),
        ))
    }
}

impl<V: ModularReduce + Eq, M: Modulus<Value = V>> Neg for ModularInteger<V, M>
where
    for<'a> &'a V: Sub<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn neg(self) -> Self::Output {
        let ModularInteger { mut value, modulus } = self;
        value = modulus.to_modulus().sub(value);
        ModularInteger::new(value, modulus)
    }
}

impl<'a, V: ModularReduce + Eq, M: Modulus<Value = V>> Neg for &'a ModularInteger<V, M>
where
    for<'l, 'r> &'l V: Sub<&'r V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn neg(self) -> Self::Output {
        let value = self.modulus.to_modulus().sub(&self.value);
        ModularInteger::new(value, self.modulus.clone())
    }
}

impl<V: ModularReduce + Eq, M: Modulus<Value = V>> Sub<ModularInteger<V, M>>
    for ModularInteger<V, M>
where
    for<'a> &'a V: Sub<V, Output = V>,
    V: Add<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn sub(self, rhs: ModularInteger<V, M>) -> Self::Output {
        self.add(rhs.neg())
    }
}

impl<'r, V: ModularReduce + Eq, M: Modulus<Value = V>> Sub<&'r ModularInteger<V, M>>
    for ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Sub<&'b V, Output = V>,
    V: Add<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn sub(self, rhs: &ModularInteger<V, M>) -> Self::Output {
        self.add(rhs.neg())
    }
}

impl<'l, V: ModularReduce + Eq, M: Modulus<Value = V>> Sub<ModularInteger<V, M>>
    for &'l ModularInteger<V, M>
where
    for<'a> &'a V: Sub<V, Output = V>,
    for<'a> &'a V: Add<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn sub(self, rhs: ModularInteger<V, M>) -> Self::Output {
        self.add(rhs.neg())
    }
}

impl<'l, 'r, V: ModularReduce + Eq, M: Modulus<Value = V>> Sub<&'r ModularInteger<V, M>>
    for &'l ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Sub<&'b V, Output = V>,
    for<'a> &'a V: Add<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn sub(self, rhs: &ModularInteger<V, M>) -> Self::Output {
        self.add(rhs.neg())
    }
}

impl<V: ModularReduce + Eq + AddAssign, M: Modulus<Value = V>> SubAssign<ModularInteger<V, M>>
    for ModularInteger<V, M>
where
    for<'a> &'a V: Sub<V, Output = V>,
{
    fn sub_assign(&mut self, rhs: Self) {
        self.add_assign(rhs.neg());
    }
}

impl<'r, V: ModularReduce + Eq + AddAssign, M: Modulus<Value = V>>
    SubAssign<&'r ModularInteger<V, M>> for ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Sub<&'b V, Output = V>,
{
    fn sub_assign(&mut self, rhs: &Self) {
        self.add_assign(rhs.neg());
    }
}

impl<V: ModularReduce + Eq, M: Modulus<Value = V>> CheckedSub for ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Sub<&'b V, Output = V>,
    for<'a, 'b> &'a V: Add<&'b V, Output = V>,
    for<'a> &'a V: Sub<V, Output = V>,
    V: Add<V, Output = V>,
{
    fn checked_sub(&self, rhs: &Self) -> Option<Self> {
        self.checked_add(&rhs.neg())
    }
}

impl<V: ModularReduce + Eq + Mul<Output = V>, M: Modulus<Value = V>> Mul for ModularInteger<V, M> {
    type Output = ModularInteger<V, M>;
    fn mul(self, rhs: Self) -> Self::Output {
        self.require_matching_moduli(&rhs);
        ModularInteger::new(self.value.mul(rhs.value), self.modulus)
    }
}

impl<V: ModularReduce + Eq + MulAssign, M: Modulus<Value = V>> MulAssign for ModularInteger<V, M> {
    fn mul_assign(&mut self, rhs: Self) {
        self.require_matching_moduli(&rhs);
        self.value.mul_assign(rhs.value);
        self.reduce();
    }
}

impl<'r, V: ModularReduce + Eq + for<'a> MulAssign<&'a V>, M: Modulus<Value = V>>
    MulAssign<&'r ModularInteger<V, M>> for ModularInteger<V, M>
{
    fn mul_assign(&mut self, rhs: &Self) {
        self.require_matching_moduli(&rhs);
        self.value.mul_assign(&rhs.value);
        self.reduce();
    }
}

impl<'r, V: 'r + ModularReduce + Eq, M: Modulus<Value = V>> Mul<&'r ModularInteger<V, M>>
    for ModularInteger<V, M>
where
    for<'a> V: Mul<&'a V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn mul(self, rhs: &ModularInteger<V, M>) -> Self::Output {
        self.require_matching_moduli(rhs);
        ModularInteger::new(self.value.mul(&rhs.value), self.modulus)
    }
}

impl<'l, V: ModularReduce + Eq, M: Modulus<Value = V>> Mul<ModularInteger<V, M>>
    for &'l ModularInteger<V, M>
where
    for<'a> &'a V: Mul<V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn mul(self, rhs: ModularInteger<V, M>) -> Self::Output {
        self.require_matching_moduli(&rhs);
        ModularInteger::new(self.value.mul(rhs.value), rhs.modulus)
    }
}

impl<'l, 'r, V: 'r + ModularReduce + Eq, M: Modulus<Value = V>> Mul<&'r ModularInteger<V, M>>
    for &'l ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Mul<&'b V, Output = V>,
{
    type Output = ModularInteger<V, M>;
    fn mul(self, rhs: &ModularInteger<V, M>) -> Self::Output {
        self.require_matching_moduli(rhs);
        ModularInteger::new(self.value.mul(&rhs.value), self.modulus.clone())
    }
}

impl<V: ModularReduce + Eq + Mul<Output = V>, M: Modulus<Value = V>> CheckedMul
    for ModularInteger<V, M>
where
    for<'a, 'b> &'a V: Mul<&'b V, Output = V>,
{
    fn checked_mul(&self, rhs: &Self) -> Option<Self> {
        if !self.has_matching_moduli(rhs) {
            return None;
        }
        Some(ModularInteger::new(
            (&self.value).mul(&rhs.value),
            self.modulus.clone(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::tests::test_op_helper;

    #[test]
    fn test_add() {
        let test = |l: ModularInteger<i32, i32>,
                    r: ModularInteger<i32, i32>,
                    expected: &ModularInteger<i32, i32>| {
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

        for m in 0..10 {
            for a in 0..m {
                for b in 0..m {
                    let mut expected = a + b;
                    if m != 0 {
                        expected %= m;
                    }
                    test((a, m).into(), (b, m).into(), &(expected, m).into());
                }
            }
        }
    }

    #[test]
    fn test_sub() {
        let test = |l: ModularInteger<i32, i32>,
                    r: ModularInteger<i32, i32>,
                    expected: &ModularInteger<i32, i32>| {
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

        for m in 0..10 {
            for a in 0..m {
                for b in 0..m {
                    let mut expected = a - b;
                    if m != 0 {
                        expected %= m;
                        if expected < 0 {
                            expected += m;
                        }
                    }
                    test((a, m).into(), (b, m).into(), &(expected, m).into());
                }
            }
        }
    }

    #[test]
    fn test_mul() {
        let test = |l: ModularInteger<i32, i32>,
                    r: ModularInteger<i32, i32>,
                    expected: &ModularInteger<i32, i32>| {
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

        for m in 0..10 {
            for a in 0..m {
                for b in 0..m {
                    let mut expected = a * b;
                    if m != 0 {
                        expected %= m;
                    }
                    test((a, m).into(), (b, m).into(), &(expected, m).into());
                }
            }
        }
    }
}
