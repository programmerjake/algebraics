// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::mod_int::ModularInteger;
use crate::mod_int::ModularReducePow;
use crate::mod_int::Modulus;
use crate::mod_int::PrimeModulus;
use crate::polynomial::Polynomial;
use crate::traits::ExtendedGCD;
use crate::traits::GCD;
use num_integer::Integer;
use std::fmt;
use std::hash::Hash;

impl<V, M> Polynomial<ModularInteger<V, M>>
where
    V: ModularReducePow<usize> + Integer + GCD<Output = V> + ExtendedGCD + fmt::Debug + Hash,
    M: Modulus<Value = V> + PrimeModulus + fmt::Debug + Hash,
{
    pub(crate) fn distinct_degree_factorization(mut self) -> Vec<Polynomial<ModularInteger<V, M>>> {
        let nonzero_highest_power_coefficient = match self.nonzero_highest_power_coefficient() {
            None => return Vec::new(),
            Some(v) => v,
        };
        let modulus = nonzero_highest_power_coefficient.modulus().into_modulus();
        self /= &nonzero_highest_power_coefficient; // convert to monic
        let mut retval = vec![nonzero_highest_power_coefficient.into()];
        unimplemented!();
        retval
    }
}
