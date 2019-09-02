// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::mod_int::KnownOddPrime;
use crate::mod_int::ModularInteger;
use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use crate::polynomial::PolynomialFactor;
use crate::polynomial::PolynomialFactors;
use crate::traits::ExactDiv;
use crate::util::next_prime_i32;
use crate::util::LeafOrNodePair;
use crate::util::PrintTree;
use crate::util::PrintTreeData;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::Ratio;
use rand::Rng;
use rand::SeedableRng;
use rand_pcg::Pcg64Mcg;
use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::fmt;
use std::mem;

struct FactorTreeInteriorNode<T: PolynomialCoefficient> {
    left: FactorTreeNode<T>,
    right: FactorTreeNode<T>,
    total_degree: usize,
}

impl<T: PolynomialCoefficient> FactorTreeInteriorNode<T> {
    fn new(left: FactorTreeNode<T>, right: FactorTreeNode<T>) -> Self {
        let total_degree = left.total_degree() + right.total_degree();
        Self {
            left,
            right,
            total_degree,
        }
    }
}

struct FactorTreeLeafNode<T: PolynomialCoefficient> {
    factor: Polynomial<T>,
}

impl<T: PolynomialCoefficient> FactorTreeLeafNode<T> {
    fn total_degree(&self) -> usize {
        self.factor.degree().expect("non-zero factor")
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
}

impl<T: PolynomialCoefficient + fmt::Display> fmt::Display for FactorTreeLeafNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "({})", self.factor)
    }
}

impl<T: PolynomialCoefficient + fmt::Display> fmt::Display for FactorTreeInteriorNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "FactorTreeInteriorNode{{left:.., right:.., total_degree:{}}}",
            self.total_degree
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
            .map(|factor| FactorTreeNode::Leaf(FactorTreeLeafNode { factor }))
            .collect();

        println!("modular_factors:");
        for factor in &modular_factors {
            if let FactorTreeNode::Leaf(leaf) = factor {
                println!("    {}", leaf.factor);
            } else {
                unreachable!("known to be all leaf nodes");
            }
        }

        // construct factor tree
        let mut factor_tree_heap: BinaryHeap<_> = modular_factors.into();

        let factor_tree = loop {
            let smallest_factor_tree = match factor_tree_heap.pop() {
                None => return vec![],
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

        factor_tree.print_tree();

        // factor using last portion of Berlekamp-Zassenhaus algorithm
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
