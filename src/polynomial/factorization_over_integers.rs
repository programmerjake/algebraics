// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::mod_int::KnownOddPrime;
use crate::mod_int::ModularInteger;
use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use crate::polynomial::PolynomialDivSupported;
use crate::polynomial::PolynomialFactor;
use crate::polynomial::PolynomialFactors;
use crate::polynomial::PolynomialReducingFactorSupported;
use crate::polynomial::SquareFreePolynomialFactors;
use crate::traits::CharacteristicZero;
use crate::traits::ExactDiv;
use crate::traits::RingCharacteristic;
use crate::traits::GCD;
use crate::util::next_prime_i32;
use num_bigint::BigInt;
use num_bigint::ToBigInt;
use num_integer::Integer;
use num_rational::Ratio;
use rand::Rng;
use rand::SeedableRng;
use rand_pcg::Pcg64Mcg;

impl Polynomial<BigInt> {
    pub(crate) fn factor_square_free_polynomial_with_rng<R: Rng + ?Sized>(
        &self,
        rng: &mut R,
    ) -> Vec<Polynomial<BigInt>> {
        let degree = match self.degree() {
            None | Some(0) | Some(1) => return vec![self.clone()],
            Some(degree) => degree,
        };
        let mut prime = 2;
        let (modular_polynomial, modulus) = loop {
            prime =
                next_prime_i32(prime).expect("polynomial too big to factor using this algorithm");
            if self
                .elements
                .iter()
                .last()
                .expect("known to be non-empty")
                .is_multiple_of(&prime.into())
            {
                // highest power coefficient would be zero, reducing the degree
                continue;
            }
            let modulus = KnownOddPrime::new_odd_prime_unsafe(prime);
            let converted_polynomial: Polynomial<_> = self
                .elements
                .iter()
                .map(|coefficient| ModularInteger::<i32, _>::from_bigint(&coefficient, modulus))
                .collect();
            debug_assert_eq!(converted_polynomial.degree(), Some(degree));
            if converted_polynomial.is_square_free() {
                break (converted_polynomial, modulus);
            }
        };
        println!("modulus: {}", modulus);
        println!("modular_polynomial: {}", modular_polynomial);
        let modular_factors: Vec<_> = modular_polynomial
            .distinct_degree_factorization()
            .into_iter()
            .enumerate()
            .flat_map(|(factor_degree, poly)| {
                if factor_degree == 0 {
                    vec![poly]
                } else {
                    poly.same_degree_factorization(factor_degree, rng)
                }
            })
            .collect();
        println!("modular_factors:");
        for factor in &modular_factors {
            println!("    {}", factor);
        }
        unimplemented!()
    }
    pub fn factor_with_rng<R: Rng + ?Sized>(&self, rng: &mut R) -> PolynomialFactors<BigInt> {
        let content = self.content();
        let rational_polynomial: Polynomial<_> = self
            .iter()
            .map(|v| Ratio::from_integer(v.exact_div(&content)))
            .collect();
        let square_free_factors = rational_polynomial
            .square_free_factorization_using_yuns_algorithm()
            .polynomial_factors;
        let mut polynomial_factors = Vec::with_capacity(self.len());
        for (index, square_free_factor) in square_free_factors.into_iter().enumerate() {
            let power = index + 1;
            polynomial_factors.extend(
                Polynomial::<BigInt>::from(square_free_factor.split_out_divisor().0)
                    .factor_square_free_polynomial_with_rng(rng)
                    .into_iter()
                    .map(|polynomial| PolynomialFactor { polynomial, power }),
            );
        }
        PolynomialFactors {
            constant_factor: content,
            polynomial_factors,
        }
    }
    pub fn factor(&self) -> PolynomialFactors<BigInt> {
        let mut rng = Pcg64Mcg::seed_from_u64(0);
        self.factor_with_rng(&mut rng)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_traits::One;
    use std::collections::HashSet;
    use std::ops::Mul;

    #[test]
    fn test_factor_square_free_polynomial_with_rng() {
        fn p(coefficients: Vec<i128>) -> Polynomial<BigInt> {
            coefficients.into_iter().map(BigInt::from).collect()
        }
        fn test_case(expected_factors: Vec<Polynomial<BigInt>>) {
            let mut rng = Pcg64Mcg::seed_from_u64(0);
            let expected_factors: HashSet<_> = expected_factors.into_iter().collect();
            let poly = expected_factors
                .iter()
                .fold(Polynomial::<BigInt>::one(), Mul::mul);
            println!("poly: {}", poly);
            println!("expected_factors:");
            for factor in &expected_factors {
                println!("    {}", factor);
            }
            let factors = poly.factor_square_free_polynomial_with_rng(&mut rng);
            let factors: HashSet<_> = factors.into_iter().collect();
            println!("factors:");
            for factor in &factors {
                println!("    {}", factor);
            }
            assert!(expected_factors == factors);
        }
        test_case(vec![
            p(vec![0, 1]),
            p(vec![4, 4, 1, 3]),
            p(vec![2, 0, 3, 3]),
            p(vec![4, 3, 1, 1, 2]),
            p(vec![4, 0, 2, 3, 3]),
        ])
    }
}
