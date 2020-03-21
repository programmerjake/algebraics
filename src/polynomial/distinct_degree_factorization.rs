// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::{
    mod_int::{ModularInteger, ModularReducePow, Modulus, PrimeModulus},
    polynomial::Polynomial,
    traits::{ExtendedGCD, GCD},
};
use num_integer::Integer;
use num_traits::Zero;
use std::{fmt, hash::Hash};

impl<V, M> Polynomial<ModularInteger<V, M>>
where
    V: ModularReducePow<usize> + Integer + GCD<Output = V> + ExtendedGCD + fmt::Debug + Hash,
    M: PrimeModulus<V> + fmt::Debug + Hash,
{
    pub(crate) fn distinct_degree_factorization(mut self) -> Vec<Polynomial<ModularInteger<V, M>>> {
        let nonzero_highest_power_coefficient = match self.nonzero_highest_power_coefficient() {
            None => return vec![Polynomial::zero()],
            Some(v) => v,
        };
        let one_coefficient = ModularInteger::new(
            V::one(),
            nonzero_highest_power_coefficient.modulus().clone(),
        );
        let x = Polynomial::make_monomial(one_coefficient, 1);
        let characteristic = nonzero_highest_power_coefficient.modulus().into_modulus();
        self /= &nonzero_highest_power_coefficient; // convert to monic
        let mut retval = vec![nonzero_highest_power_coefficient.into()];
        let mut power = x.powmod(characteristic.clone(), &self);
        for _ in 0..self.len() {
            if self.len() <= 1 {
                return retval;
            }
            let next_factor = (&power - &x).gcd(&self);
            self /= &next_factor;
            retval.push(next_factor);
            power = power.powmod(characteristic.clone(), &self);
        }
        unreachable!("failed to find all factors")
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mod_int::KnownPrime;

    #[test]
    fn test_distinct_degree_factorization() {
        fn make_poly(
            poly: &[i32],
            modulus: KnownPrime<i32>,
        ) -> Polynomial<ModularInteger<i32, KnownPrime<i32>>> {
            poly.iter()
                .map(|&coefficient| ModularInteger::new(coefficient, modulus))
                .collect()
        }
        fn test_case(poly: &[i32], expected_factors: &[&[i32]], modulus: KnownPrime<i32>) {
            let poly = make_poly(poly, modulus);
            let expected_factors: Vec<_> = expected_factors
                .iter()
                .map(|poly| make_poly(*poly, modulus))
                .collect();
            println!("poly: {}", poly);
            println!("expected_factors:");
            for factor in &expected_factors {
                println!("    {}", factor);
            }
            let factors = poly.distinct_degree_factorization();
            println!("factors:");
            for factor in &factors {
                println!("    {}", factor);
            }
            assert!(expected_factors == factors);
        }
        test_case(
            &[5, 0, 6, 6, 0, 0, 6, 0, 4, 0, 5, 6, 3, 3],
            &[
                &[3],
                &[6, 4, 6, 1],
                &[6, 3, 2, 4, 1],
                &[4, 0, 0, 2, 6, 5, 1],
            ],
            KnownPrime::new_unsafe(7),
        );
        test_case(
            &[4, 2, 0, 0, 2, 2, 4, 6, 0, 5, 1, 3, 6, 3],
            &[
                &[3],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[1],
                &[6, 3, 0, 0, 3, 3, 6, 2, 0, 4, 5, 1, 2, 1],
            ],
            KnownPrime::new_unsafe(7),
        );
    }
}
