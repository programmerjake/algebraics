// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use num_bigint::BigInt;
use num_bigint::BigUint;
use num_integer::Integer;
use num_traits::FromPrimitive;
use num_traits::One;
use num_traits::Zero;

pub trait ModularReduce<V: Clone = Self>: Clone {
    fn modular_reduce_assign<M: Modulus<Value = V>>(&mut self, modulus: M);
    fn modular_reduce<M: Modulus<Value = V>>(mut self, modulus: M) -> Self {
        self.modular_reduce_assign(modulus);
        self
    }
}

pub trait ModularReducePow<E = Self, V: Clone = Self>: ModularReduce<V> {
    fn pow_modular_reduce<M: Modulus<Value = V>>(&self, exponent: &E, modulus: M) -> Self;
}

pub trait Modulus: Clone {
    type Value: Clone;
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

impl<V, M> Into<(V, M)> for ModularInteger<V, M> {
    fn into(self) -> (V, M) {
        (self.value, self.modulus)
    }
}

impl<V: Integer + Clone, M: Modulus<Value = V>> ModularInteger<V, M> {
    pub fn new<T: Into<V>>(value: T, modulus: M) -> Self {
        assert!(*modulus.to_modulus() > Zero::zero());
        let value = value.into();
        Self {
            value: Integer::mod_floor(&value, modulus.to_modulus()),
            modulus,
        }
    }
}

impl<V: Integer + Clone, M: Modulus<Value = V>> From<(V, M)> for ModularInteger<V, M> {
    fn from((value, modulus): (V, M)) -> Self {
        Self::new(value, modulus)
    }
}

// TODO: implement add, sub, mul, div
