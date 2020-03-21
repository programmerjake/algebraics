// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::{
    mod_int::{KnownOddPrime, ModularInteger, Modulus},
    polynomial::{
        Polynomial, PolynomialCoefficient, PolynomialDivSupported, PolynomialFactor,
        PolynomialFactors, PolynomialReducingFactorSupported,
    },
    traits::{ExactDiv, ExtendedGCD, ExtendedGCDResult},
    util::{
        for_subsets_of_size, next_prime_i32, ContinueBreak, LeafOrNodePair, PrintTree,
        PrintTreeData,
    },
};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{One, Signed};
use rand::{Rng, SeedableRng};
use rand_pcg::Pcg64Mcg;
use std::{
    cmp::Ordering,
    collections::BinaryHeap,
    fmt, mem,
    ops::{Add, AddAssign},
};

struct FactorTreeInteriorNode<T: PolynomialCoefficient> {
    left: FactorTreeNode<T>,
    right: FactorTreeNode<T>,
    total_degree: usize,
    product: Polynomial<T>,
    left_bezout_coefficient: Polynomial<T>,
    right_bezout_coefficient: Polynomial<T>,
}

impl<T: PolynomialCoefficient> FactorTreeInteriorNode<T> {
    fn new(left: FactorTreeNode<T>, right: FactorTreeNode<T>) -> Self
    where
        T: PolynomialDivSupported + PolynomialReducingFactorSupported,
    {
        let total_degree = left.total_degree() + right.total_degree();
        let left_product = left.product();
        let right_product = right.product();
        let product = left_product * right_product;
        let ExtendedGCDResult {
            gcd,
            x: left_bezout_coefficient,
            y: right_bezout_coefficient,
        } = left_product.extended_gcd(right_product);
        assert!(gcd.is_one());
        assert!(left_bezout_coefficient.len() < right_product.len());
        assert!(right_bezout_coefficient.len() < left_product.len());
        Self {
            left,
            right,
            total_degree,
            product,
            left_bezout_coefficient,
            right_bezout_coefficient,
        }
    }
    fn map_coefficients<O: PolynomialCoefficient, F: FnMut(T) -> O>(
        &self,
        f: &mut F,
    ) -> FactorTreeInteriorNode<O> {
        FactorTreeInteriorNode {
            left: self.left.map_coefficients(f),
            right: self.right.map_coefficients(f),
            total_degree: self.total_degree,
            product: self.product.iter().map(&mut *f).collect(),
            left_bezout_coefficient: self.left_bezout_coefficient.iter().map(&mut *f).collect(),
            right_bezout_coefficient: self.right_bezout_coefficient.iter().map(&mut *f).collect(),
        }
    }
    fn into_leaves(self, leaves: &mut Vec<Polynomial<T>>) {
        self.left.into_leaves(leaves);
        self.right.into_leaves(leaves);
    }
}

struct FactorTreeLeafNode<T: PolynomialCoefficient> {
    factor: Polynomial<T>,
}

impl<T: PolynomialCoefficient> FactorTreeLeafNode<T> {
    fn total_degree(&self) -> usize {
        self.factor.degree().expect("non-zero factor")
    }
    fn map_coefficients<O: PolynomialCoefficient, F: FnMut(T) -> O>(
        &self,
        f: &mut F,
    ) -> FactorTreeLeafNode<O> {
        FactorTreeLeafNode {
            factor: self.factor.iter().map(f).collect(),
        }
    }
    fn into_leaves(self, leaves: &mut Vec<Polynomial<T>>) {
        leaves.push(self.factor);
    }
}

enum FactorTreeNode<T: PolynomialCoefficient> {
    Interior(Box<FactorTreeInteriorNode<T>>),
    Leaf(FactorTreeLeafNode<T>),
}

impl<T: PolynomialCoefficient> FactorTreeNode<T> {
    fn total_degree(&self) -> usize {
        match self {
            Self::Interior(node) => node.total_degree,
            Self::Leaf(node) => node.total_degree(),
        }
    }
    fn product(&self) -> &Polynomial<T> {
        match self {
            Self::Interior(node) => &node.product,
            Self::Leaf(node) => &node.factor,
        }
    }
    fn map_coefficients<O: PolynomialCoefficient, F: FnMut(T) -> O>(
        &self,
        f: &mut F,
    ) -> FactorTreeNode<O> {
        match self {
            FactorTreeNode::Interior(node) => {
                FactorTreeNode::Interior(node.map_coefficients(f).into())
            }
            FactorTreeNode::Leaf(node) => FactorTreeNode::Leaf(node.map_coefficients(f)),
        }
    }
    fn into_leaves(self, leaves: &mut Vec<Polynomial<T>>) {
        match self {
            Self::Interior(node) => node.into_leaves(leaves),
            Self::Leaf(node) => node.into_leaves(leaves),
        }
    }
}

impl<T: PolynomialCoefficient + fmt::Display> fmt::Display for FactorTreeLeafNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let FactorTreeLeafNode { factor } = self;
        write!(f, "({})", factor)
    }
}

impl<T: PolynomialCoefficient + fmt::Display> fmt::Display for FactorTreeInteriorNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let FactorTreeInteriorNode {
            left: _left,
            right: _right,
            total_degree,
            product,
            left_bezout_coefficient,
            right_bezout_coefficient,
        } = self;
        write!(
            f,
            r"FactorTreeInteriorNode {{
    left:.., right:..,
    total_degree:{total_degree},
    product:({product}),
    left_bezout_coefficient:({left_bezout_coefficient}),
    right_bezout_coefficient:({right_bezout_coefficient})
}}",
            total_degree = total_degree,
            product = product,
            left_bezout_coefficient = left_bezout_coefficient,
            right_bezout_coefficient = right_bezout_coefficient,
        )
    }
}

impl<'a, T: 'a + PolynomialCoefficient + fmt::Display> PrintTreeData<'a> for FactorTreeNode<T> {
    type Leaf = &'a FactorTreeLeafNode<T>;
    type NodeData = &'a FactorTreeInteriorNode<T>;
}

impl<T: 'static + PolynomialCoefficient + fmt::Display> PrintTree for FactorTreeNode<T> {
    fn to_leaf_or_node_pair(
        &self,
    ) -> LeafOrNodePair<&FactorTreeLeafNode<T>, &Self, &FactorTreeInteriorNode<T>> {
        match self {
            Self::Interior(node) => LeafOrNodePair::NodePair(&node.left, &**node, &node.right),
            Self::Leaf(node) => LeafOrNodePair::Leaf(node),
        }
    }
}

impl<T: PolynomialCoefficient> Eq for FactorTreeNode<T> {}

impl<T: PolynomialCoefficient> PartialEq for FactorTreeNode<T> {
    fn eq(&self, rhs: &Self) -> bool {
        self.cmp(rhs) == Ordering::Equal
    }
}

impl<T: PolynomialCoefficient> PartialOrd for FactorTreeNode<T> {
    fn partial_cmp(&self, rhs: &Self) -> Option<Ordering> {
        Some(self.cmp(rhs))
    }
}

impl<T: PolynomialCoefficient> Ord for FactorTreeNode<T> {
    fn cmp(&self, rhs: &Self) -> Ordering {
        self.total_degree().cmp(&rhs.total_degree()).reverse()
    }
}

impl FactorTreeLeafNode<ModularInteger<BigInt, BigInt>> {
    fn hensel_lift_step(
        &mut self,
        _old_modulus: &BigInt,
        _new_modulus: &BigInt,
        new_product: Polynomial<ModularInteger<BigInt, BigInt>>,
    ) {
        self.factor = new_product;
    }
}

impl FactorTreeInteriorNode<ModularInteger<BigInt, BigInt>> {
    fn hensel_lift_step(
        &mut self,
        old_modulus: &BigInt,
        new_modulus: &BigInt,
        new_product: Polynomial<ModularInteger<BigInt, BigInt>>,
    ) {
        fn set_modulus<T: IntoIterator<Item = ModularInteger<BigInt, BigInt>>>(
            value: T,
            new_modulus: &BigInt,
        ) -> Polynomial<ModularInteger<BigInt, BigInt>> {
            value
                .into_iter()
                .map(Into::into)
                .map(|(value, _modulus)| ModularInteger::new(value, new_modulus.clone()))
                .collect()
        }
        let old_left_product = set_modulus(self.left.product(), new_modulus);
        let old_right_product = set_modulus(self.right.product(), new_modulus);
        let old_left_bezout_coefficient =
            set_modulus(mem::take(&mut self.left_bezout_coefficient), new_modulus);
        let old_right_bezout_coefficient =
            set_modulus(mem::take(&mut self.right_bezout_coefficient), new_modulus);
        let error = &new_product - &old_left_product * &old_right_product;
        let (quotient, remainder) =
            (&old_left_bezout_coefficient * &error).div_rem(&old_right_product);
        let left_product =
            &old_left_product + &old_right_bezout_coefficient * error + quotient * old_left_product;
        let right_product = old_right_product + remainder;
        let bezout_error = &old_left_bezout_coefficient * &left_product
            + &old_right_bezout_coefficient * &right_product
            - ModularInteger::new(BigInt::one(), new_modulus.clone());
        let (quotient, remainder) =
            (&old_left_bezout_coefficient * &bezout_error).div_rem(&right_product);
        let new_left_bezout_coefficient = old_left_bezout_coefficient - remainder;
        let orbc_mul_bezout_error = &old_right_bezout_coefficient * bezout_error;
        let new_right_bezout_coefficient =
            old_right_bezout_coefficient - orbc_mul_bezout_error - quotient * &left_product;
        // println!("left_product: ({})", left_product);
        // println!("right_product: ({})", right_product);
        // println!("self.left.product(): ({})", self.left.product());
        // println!("self.right.product(): ({})", self.right.product());
        debug_assert!(&set_modulus(left_product.iter(), old_modulus) == self.left.product());
        debug_assert!(&set_modulus(right_product.iter(), old_modulus) == self.right.product());
        let check_bezout_coefficients = || {
            let bezout_identity = &new_left_bezout_coefficient * &left_product
                + &new_right_bezout_coefficient * &right_product;
            // println!("bezout_identity: ({})", bezout_identity);
            bezout_identity.is_one()
        };
        debug_assert!(check_bezout_coefficients());
        debug_assert!(&left_product * &right_product == new_product);
        self.product = new_product;
        self.left_bezout_coefficient = new_left_bezout_coefficient;
        self.right_bezout_coefficient = new_right_bezout_coefficient;
        self.left
            .hensel_lift_step(old_modulus, new_modulus, left_product);
        self.right
            .hensel_lift_step(old_modulus, new_modulus, right_product);
        self.total_degree = self.left.total_degree() + self.right.total_degree();
    }
}

impl FactorTreeNode<ModularInteger<BigInt, BigInt>> {
    fn hensel_lift_step(
        &mut self,
        old_modulus: &BigInt,
        new_modulus: &BigInt,
        new_product: Polynomial<ModularInteger<BigInt, BigInt>>,
    ) {
        match self {
            Self::Leaf(node) => node.hensel_lift_step(old_modulus, new_modulus, new_product),
            Self::Interior(node) => node.hensel_lift_step(old_modulus, new_modulus, new_product),
        }
    }
}

#[derive(Clone, Debug)]
enum ExactInexactInt {
    Exact {
        value: BigInt,
    },

    /// represents the range lower_bound < x < lower_bound + 1
    Inexact {
        lower_bound: BigInt,
    },
}

impl ExactInexactInt {
    fn new(value: BigInt) -> Self {
        Self::Exact { value }
    }
    fn sqrt(&self) -> Self {
        match self {
            Self::Exact { value } => {
                let sqrt = value.sqrt();
                if &sqrt * &sqrt == *value {
                    Self::Exact { value: sqrt }
                } else {
                    Self::Inexact { lower_bound: sqrt }
                }
            }
            Self::Inexact { lower_bound } => Self::Inexact {
                lower_bound: lower_bound.sqrt(),
            },
        }
    }
}

impl AddAssign<i32> for ExactInexactInt {
    fn add_assign(&mut self, rhs: i32) {
        match self {
            Self::Exact { value } => *value += rhs,
            Self::Inexact { lower_bound } => *lower_bound += rhs,
        }
    }
}

impl Add<i32> for ExactInexactInt {
    type Output = ExactInexactInt;
    fn add(mut self, rhs: i32) -> Self::Output {
        self += rhs;
        self
    }
}

impl Add<i32> for &'_ ExactInexactInt {
    type Output = ExactInexactInt;
    fn add(self, rhs: i32) -> Self::Output {
        let mut retval = self.clone();
        retval += rhs;
        retval
    }
}

impl PartialEq<BigInt> for ExactInexactInt {
    fn eq(&self, rhs: &BigInt) -> bool {
        self.partial_cmp(rhs) == Some(Ordering::Equal)
    }
}

impl PartialEq<ExactInexactInt> for BigInt {
    fn eq(&self, rhs: &ExactInexactInt) -> bool {
        self.partial_cmp(rhs) == Some(Ordering::Equal)
    }
}

impl PartialOrd<BigInt> for ExactInexactInt {
    fn partial_cmp(&self, rhs: &BigInt) -> Option<Ordering> {
        match self {
            Self::Exact { value } => Some(value.cmp(rhs)),
            Self::Inexact { lower_bound } => {
                if *lower_bound >= *rhs {
                    Some(Ordering::Greater)
                } else {
                    Some(Ordering::Less)
                }
            }
        }
    }
}

impl PartialOrd<ExactInexactInt> for BigInt {
    fn partial_cmp(&self, rhs: &ExactInexactInt) -> Option<Ordering> {
        rhs.partial_cmp(self).map(Ordering::reverse)
    }
}

impl fmt::Display for ExactInexactInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            ExactInexactInt::Exact { value } => write!(f, "{}", value),
            ExactInexactInt::Inexact { lower_bound } => {
                write!(f, "({}, {})", lower_bound, lower_bound + 1i32)
            }
        }
    }
}

impl Polynomial<BigInt> {
    fn factor_square_free_polynomial_with_rng<R: Rng + ?Sized>(
        &self,
        rng: &mut R,
    ) -> Vec<Polynomial<BigInt>> {
        let degree = match self.degree() {
            None | Some(0) | Some(1) => return vec![self.clone()],
            Some(degree) => degree,
        };
        let content = self.content();
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
        // println!("modulus: {}", modulus);
        // println!("modular_polynomial: {}", modular_polynomial);
        let modular_factors: Vec<_> = modular_polynomial
            .distinct_degree_factorization()
            .into_iter()
            .enumerate()
            .flat_map(|(factor_degree, poly)| {
                if poly.is_one() {
                    vec![]
                } else if factor_degree == 0 {
                    vec![poly]
                } else {
                    poly.same_degree_factorization(factor_degree, rng)
                }
            })
            .map(|factor| FactorTreeNode::Leaf(FactorTreeLeafNode { factor }))
            .collect();

        // println!("modular_factors:");
        // for factor in &modular_factors {
        //     if let FactorTreeNode::Leaf(leaf) = factor {
        //         println!("    {}", leaf.factor);
        //     } else {
        //         unreachable!("known to be all leaf nodes");
        //     }
        // }

        let modular_factors_len = modular_factors.len();

        // construct factor tree
        let mut factor_tree_heap: BinaryHeap<_> = modular_factors.into();

        let factor_tree = loop {
            let smallest_factor_tree = match factor_tree_heap.pop() {
                None => {
                    if content.is_one() {
                        return vec![];
                    } else {
                        return vec![content.into()];
                    }
                }
                Some(v) => v,
            };
            let second_smallest_factor_tree = match factor_tree_heap.pop() {
                None => break smallest_factor_tree,
                Some(v) => v,
            };
            factor_tree_heap.push(FactorTreeNode::Interior(
                FactorTreeInteriorNode::new(smallest_factor_tree, second_smallest_factor_tree)
                    .into(),
            ))
        };
        mem::drop(factor_tree_heap);
        let mut modulus = BigInt::from(modulus.into_modulus());
        let mut factor_tree = factor_tree.map_coefficients(&mut |coefficient: ModularInteger<
            i32,
            KnownOddPrime<i32>,
        >| {
            ModularInteger::<BigInt, BigInt>::new(
                BigInt::from(*coefficient.value()),
                modulus.clone(),
            )
        });

        // factor_limit from (2) in http://web.archive.org/web/20161221120512/https://dms.umontreal.ca/~andrew/PDF/BoundCoeff.pdf
        // original formula:
        // define norm_2(p) = sqrt(sum(p[i]^2, 0 <= i <= n))
        // where p == p[0] + p[1]*x + p[2]*x^2 + ... + p[n]*x^n
        // where n is the degree of p
        //
        // for all polynomials g, p in Z[x] if g divides p then norm_2(g) <= 2^degree(g) * norm_2(p)

        let max_norm = self.max_norm();
        let max_norm_squared = &max_norm * &max_norm;
        let highest_power_coefficient = self.highest_power_coefficient();
        let highest_power_coefficient_squared =
            &highest_power_coefficient * &highest_power_coefficient;

        let factor_limit_squared =
            ((max_norm_squared * highest_power_coefficient_squared) << (degree * 2)) * (degree + 1);
        // let factor_limit = ExactInexactInt::new(factor_limit_squared.clone()).sqrt();
        // println!("factor_limit: {}", factor_limit);
        let needed_modulus = ExactInexactInt::new(factor_limit_squared * 4i32).sqrt() + 1i32;
        // println!("needed_modulus: {}", needed_modulus);
        // println!();
        // factor_tree.print_tree();
        // println!();
        while modulus < needed_modulus {
            let new_modulus = &modulus * &modulus;
            let expected_product: Polynomial<_> = self
                .iter()
                .map(|coefficient| ModularInteger::new(coefficient, new_modulus.clone()))
                .collect();
            factor_tree.hensel_lift_step(&modulus, &new_modulus, expected_product);
            modulus = new_modulus;

            // factor_tree.print_tree();
            // println!();
        }
        // println!();
        // factor_tree.print_tree();
        // println!();

        let mut modular_factors = Vec::with_capacity(modular_factors_len);
        factor_tree.into_leaves(&mut modular_factors);

        modular_factors.retain(|factor| factor.degree() != Some(0));

        debug_assert!(modular_factors
            .iter()
            .position(|factor| match factor.degree() {
                None | Some(0) => true,
                _ => false,
            })
            .is_none());

        // println!("modular_factors:");
        // for factor in &modular_factors {
        //     println!("    {}", factor);
        // }

        let mut factors = Vec::with_capacity(modular_factors.len());

        if !content.is_one() {
            factors.push(content.into());
        }

        let half_modulus = &modulus / 2i32;

        let mut input_polynomial = self.clone();

        // FIXME: replace exponential subset search with LLL reduction

        let mut subset_size = 0;
        let mut found_factors = false;
        loop {
            if found_factors {
                found_factors = false;
            } else {
                subset_size += 1;
            }
            if subset_size * 2 > modular_factors.len() {
                break;
            }
            let range = 0..modular_factors.len();
            for_subsets_of_size(
                |subset_indexes: &[usize]| {
                    // println!("subset_indexes: {:?}", subset_indexes);
                    let mut potential_factor = Polynomial::from(ModularInteger::new(
                        input_polynomial.highest_power_coefficient(),
                        modulus.clone(),
                    ));
                    for &index in subset_indexes {
                        potential_factor *= &modular_factors[index];
                    }
                    // println!("potential_factor: {}", potential_factor);
                    let mut potential_factor: Polynomial<_> = potential_factor
                        .into_iter()
                        .map(Into::into)
                        .map(|(coefficient, _modulus)| {
                            assert!(!coefficient.is_negative());
                            assert!(coefficient < modulus);
                            if coefficient > half_modulus {
                                coefficient - &modulus
                            } else {
                                coefficient
                            }
                        })
                        .collect();
                    // println!("potential_factor: {}", potential_factor);
                    potential_factor.primitive_part_assign();
                    // println!("potential_factor: {}", potential_factor);
                    // println!("input_polynomial: {}", input_polynomial);
                    if let Some((mut quotient, _)) = input_polynomial
                        .clone()
                        .checked_exact_pseudo_div(&potential_factor)
                    {
                        factors.push(potential_factor);
                        // println!("found factor");
                        quotient.primitive_part_assign();
                        // println!("quotient: {}", quotient);
                        input_polynomial = quotient;
                        found_factors = true;
                        for &index in subset_indexes.iter().rev() {
                            modular_factors.remove(index);
                        }
                        ContinueBreak::Break(())
                    } else {
                        ContinueBreak::Continue
                    }
                },
                subset_size,
                range,
            );
        }
        factors.push(input_polynomial);
        factors
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
                    .filter(|polynomial| !polynomial.is_one())
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
    use num_traits::{One, Pow};
    use std::{collections::HashSet, ops::Mul};

    fn p(coefficients: Vec<i128>) -> Polynomial<BigInt> {
        coefficients.into_iter().map(BigInt::from).collect()
    }

    fn test_factor_square_free_polynomial_with_rng_test_case(
        expected_factors: Vec<Polynomial<BigInt>>,
    ) {
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

    #[test]
    fn test_factor_square_free_polynomial_with_rng_0() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![
            p(vec![0, 1]),
            p(vec![4, 4, 1, 3]),
            p(vec![2, 0, 3, 3]),
            p(vec![4, 3, 1, 1, 2]),
            p(vec![4, 0, 2, 3, 3]),
        ]);
    }

    #[test]
    fn test_factor_square_free_polynomial_with_rng_1() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![
            p(vec![-1]),
            p(vec![-0, 1]),
            p(vec![-4, 4, -1, 3]),
            p(vec![-2, 0, -3, 3]),
            p(vec![4, -3, 1, -1, 2]),
            p(vec![4, -0, 2, -3, 3]),
        ]);
    }

    #[test]
    #[ignore = "slow"]
    fn test_factor_square_free_polynomial_with_rng_2() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![
            p(vec![12]),
            p(vec![29, 19]),
            p(vec![185, 174]),
            p(vec![189, 135, 97]),
            p(vec![171, 134, 40, 122, 46]),
            p(vec![118, 103, 175, 39, 172]),
            p(vec![101, 149, 70, 56, 68, 79]),
            p(vec![186, 77, 5, 168, 148, 70, 82, 158]),
            p(vec![171, 146, 23, 181, 116, 106, 74, 168]),
            p(vec![181, 16, 97, 169, 189, 142, 69, 168, 133, 87]),
            p(vec![130, 82, 85, 16, 87, 165, 168, -6, 106, 89]),
            p(vec![152, 23, 189, 50, 21, 142, 43, 146, 106, -5, 106]),
        ]);
    }

    #[test]
    #[ignore = "slow"]
    fn test_factor_square_free_polynomial_with_rng_3() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![
            p(vec![36, 97, 177, 78]),
            p(vec![190, 184, 24, 141]),
            p(vec![105, 57, 21, 161]),
            p(vec![136, 159, 47, 45, 20]),
            p(vec![28, 80, 84, 27, 56]),
            p(vec![173, 118, 123, 108, 118, 36]),
            p(vec![48, -4, 120, 156, 81, 76]),
            p(vec![98, 179, 179, -3, 176, 100]),
            p(vec![104, 83, 68, 123, 166, 125, 62]),
            p(vec![17, 176, 132, 115, 1, 182, 95, 105, 11]),
            p(vec![73, 70, 12, 57, 122, 23, 23, 146, 28]),
        ]);
    }

    #[test]
    #[ignore = "slow"]
    fn test_factor_square_free_polynomial_with_rng_4() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![
            p(vec![286]),
            p(vec![94, 61]),
            p(vec![-37, 13, 16]),
            p(vec![-57, 75, 20]),
            p(vec![98, -43, 27]),
            p(vec![43, -77, -75, 98]),
            p(vec![43, 16, -94, -84, -67, 20]),
            p(vec![-65, -2, -49, -61, -57, 80]),
            p(vec![-30, -52, 54, 21, 21, -56, 3]),
            p(vec![94, 50, 97, -83, 97, -3, -51, -86, 38]),
            p(vec![2, -16, 50, -67, 63, -69, -31, 25, 83]),
            p(vec![-69, 28, -25, -25, 57, -10, -65, -19, 3, -66, 38]),
        ]);
    }

    #[test]
    fn test_factor_square_free_polynomial_with_rng_5() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![p(vec![
            -69, 28, -25, -25, 57, -10, -65, -19, 3, -66, 38,
        ])]);
    }

    #[test]
    fn test_factor_square_free_polynomial_with_rng_6() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![p(vec![1234])]);
    }

    #[test]
    fn test_factor_square_free_polynomial_with_rng_7() {
        test_factor_square_free_polynomial_with_rng_test_case(vec![p(vec![3, 1234])]);
    }

    fn test_factor_test_case(expected: PolynomialFactors<i128>) {
        let expected = PolynomialFactors {
            constant_factor: BigInt::from(expected.constant_factor),
            polynomial_factors: expected
                .polynomial_factors
                .into_iter()
                .map(|PolynomialFactor { polynomial, power }| PolynomialFactor {
                    polynomial: p(polynomial.into_coefficients()),
                    power,
                })
                .collect(),
        };
        let expected_factors: HashSet<_> = expected.polynomial_factors.into_iter().collect();
        let poly = expected_factors.iter().fold(
            Polynomial::from(expected.constant_factor.clone()),
            |poly, PolynomialFactor { polynomial, power }| poly * polynomial.pow(*power),
        );
        println!("poly: {}", poly);
        println!("expected_factors:");
        println!("    {}", expected.constant_factor);
        for factor in &expected_factors {
            println!("    {}", factor);
        }
        let PolynomialFactors {
            constant_factor,
            polynomial_factors,
        } = poly.factor();
        let factors: HashSet<_> = polynomial_factors.into_iter().collect();
        println!("factors:");
        println!("    {}", constant_factor);
        for factor in &factors {
            println!("    {}", factor);
        }
        assert!(expected.constant_factor == constant_factor);
        assert!(expected_factors == factors);
    }

    #[test]
    fn test_factor_0() {
        test_factor_test_case(PolynomialFactors {
            constant_factor: -6,
            polynomial_factors: vec![
                PolynomialFactor {
                    polynomial: vec![-9, 13].into(),
                    power: 1,
                },
                PolynomialFactor {
                    polynomial: vec![-88, -53, 55].into(),
                    power: 4,
                },
                PolynomialFactor {
                    polynomial: vec![-39, -7, 62].into(),
                    power: 5,
                },
                PolynomialFactor {
                    polynomial: vec![-4, 26, -72, 91].into(),
                    power: 1,
                },
                PolynomialFactor {
                    polynomial: vec![-74, 9, -68, 92].into(),
                    power: 1,
                },
                PolynomialFactor {
                    polynomial: vec![-74, 5, -46, 82, -19, 63].into(),
                    power: 6,
                },
            ],
        });
    }

    #[test]
    fn test_factor_1() {
        test_factor_test_case(PolynomialFactors {
            constant_factor: -128,
            polynomial_factors: vec![
                PolynomialFactor {
                    polynomial: vec![-1, 25].into(),
                    power: 3,
                },
                PolynomialFactor {
                    polynomial: vec![2, 37].into(),
                    power: 1,
                },
                PolynomialFactor {
                    polynomial: vec![99, -19, 76, 3].into(),
                    power: 5,
                },
                PolynomialFactor {
                    polynomial: vec![-43, 82, -13, 35, -22, 18].into(),
                    power: 7,
                },
                PolynomialFactor {
                    polynomial: vec![100, -26, 9, -24, 32, 32].into(),
                    power: 2,
                },
                PolynomialFactor {
                    polynomial: vec![57, 92, 28, -26, 10, 95].into(),
                    power: 2,
                },
            ],
        });
    }
}
