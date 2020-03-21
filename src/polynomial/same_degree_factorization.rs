// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::{
    mod_int::{ModularInteger, ModularReducePow, OddPrimeModulus},
    polynomial::Polynomial,
    traits::{ExactDivAssign, ExtendedGCD, GCD},
};
use num_bigint::ToBigInt;
use num_integer::Integer;
use num_traits::Pow;
use rand::{
    distributions::{uniform::SampleUniform, Distribution, Uniform},
    Rng,
};
use std::{fmt, hash::Hash, iter};

impl<V, M> Polynomial<ModularInteger<V, M>>
where
    V: ModularReducePow<usize>
        + Integer
        + GCD<Output = V>
        + ExtendedGCD
        + fmt::Debug
        + fmt::Display
        + Hash
        + SampleUniform
        + ToBigInt,
    M: OddPrimeModulus<V> + fmt::Debug + fmt::Display + Hash,
{
    pub(crate) fn same_degree_factorization<R: Rng + ?Sized>(
        self,
        factor_degree: usize,
        rng: &mut R,
    ) -> Vec<Polynomial<ModularInteger<V, M>>> {
        assert!(factor_degree >= 1);
        assert!(self.len() > 1);
        if self.degree() == Some(factor_degree) {
            return vec![self];
        }
        let nonzero_highest_power_coefficient = match self.nonzero_highest_power_coefficient() {
            None => return Vec::new(),
            Some(v) => v,
        };
        assert!(nonzero_highest_power_coefficient.value().is_one());
        let modulus = nonzero_highest_power_coefficient.modulus();
        let one_coefficient = ModularInteger::new(V::one(), modulus.clone());
        let characteristic = modulus.to_modulus().into_owned();
        let bigint_characteristic = characteristic
            .to_bigint()
            .expect("can't convert modulus/characteristic to BigInt");
        let polynomial_exponent = (bigint_characteristic.pow(factor_degree) - 1u32) / 2u32;
        let coefficient_uniform = Uniform::new(V::zero(), characteristic);
        let mut retval = Vec::new();
        let mut factoring_stack = vec![self.clone()];
        while let Some(mut polynomial) = factoring_stack.pop() {
            assert!(
                polynomial.degree().unwrap_or(0) >= factor_degree,
                "factoring failed: {}",
                self
            );
            if polynomial.degree() == Some(factor_degree) {
                retval.push(polynomial);
                continue;
            }
            let factors = loop {
                let random_polynomial_degree = 2 * factor_degree - 1;
                let random_polynomial: Polynomial<_> = (0..random_polynomial_degree)
                    .map(|_| coefficient_uniform.sample(rng))
                    .chain(iter::once(V::one()))
                    .map(|v| ModularInteger::new(v, modulus.clone()))
                    .collect();
                debug_assert!(random_polynomial.degree().unwrap_or(0) >= 1);
                let gcd = polynomial.gcd(
                    &(random_polynomial.powmod(polynomial_exponent.clone(), &polynomial)
                        - &one_coefficient),
                );
                if gcd.degree().unwrap_or(0) > 0 && gcd.len() < polynomial.len() {
                    polynomial.exact_div_assign(&gcd);
                    break (gcd, polynomial);
                }
            };
            factoring_stack.push(factors.0);
            factoring_stack.push(factors.1);
        }
        retval
    }
}

// TODO: implement same_degree_factorization for modulus 2 (needs different algorithm)

#[cfg(test)]
mod tests {
    use super::*;
    use crate::mod_int::KnownOddPrime;
    use rand::SeedableRng;
    use rand_pcg::Pcg64Mcg;
    use std::collections::HashSet;

    #[test]
    pub(crate) fn test_same_degree_factorization() {
        fn make_poly(
            poly: &[i32],
            modulus: KnownOddPrime<i32>,
        ) -> Polynomial<ModularInteger<i32, KnownOddPrime<i32>>> {
            poly.iter()
                .map(|&coefficient| ModularInteger::new(coefficient, modulus))
                .collect()
        }
        fn test_case(
            poly: &[i32],
            expected_factors: &[&[i32]],
            factor_degree: usize,
            modulus: KnownOddPrime<i32>,
        ) {
            let mut rng = Pcg64Mcg::seed_from_u64(0);
            let poly = make_poly(poly, modulus);
            let expected_factors: HashSet<_> = expected_factors
                .iter()
                .map(|poly| make_poly(*poly, modulus))
                .collect();
            println!("poly: {}", poly);
            println!("factor_degree: {}", factor_degree);
            println!("expected_factors:");
            for factor in &expected_factors {
                println!("    {}", factor);
            }
            let factors = poly.same_degree_factorization(factor_degree, &mut rng);
            let factors: HashSet<_> = factors.into_iter().collect();
            println!("factors:");
            for factor in &factors {
                println!("    {}", factor);
            }
            assert!(expected_factors == factors);
        }
        test_case(
            &[2, 0, 3, 1, 2, 2, 4, 3, 0, 1, 2, 4, 1, 2, 0, 0, 1],
            &[&[2, 3, 3, 4, 0, 0, 4, 4, 1], &[1, 1, 1, 3, 3, 0, 2, 1, 1]],
            8,
            KnownOddPrime::new_odd_prime_unsafe(5),
        );
        test_case(
            &[4, 0, 0, 0, 1],
            &[&[1, 1], &[2, 1], &[3, 1], &[4, 1]],
            1,
            KnownOddPrime::new_odd_prime_unsafe(5),
        );
        test_case(
            &[2, 2, 3, 1, 1],
            &[&[1, 1, 1], &[2, 0, 1]],
            2,
            KnownOddPrime::new_odd_prime_unsafe(5),
        );
    }
}
