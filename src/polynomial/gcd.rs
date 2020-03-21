// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::{
    polynomial::{
        Polynomial, PolynomialCoefficient, PolynomialDivSupported,
        PolynomialReducingFactorSupported, PseudoDivRem,
    },
    traits::{
        ExactDiv, ExactDivAssign, ExtendedGCD, ExtendedGCDAndLCM, ExtendedGCDResult, GCDAndLCM, GCD,
    },
};
use num_integer::Integer;
use num_traits::Zero;
use std::{borrow::Cow, mem};

/// computes factor * base.pow(exponent_positive_part - exponent_negative_part)
fn exact_mul_by_signed_power<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>(
    factor: T,
    base: T,
    exponent_positive_part: usize,
    exponent_negative_part: usize,
) -> T {
    if exponent_positive_part >= exponent_negative_part {
        factor * T::coefficient_pow_usize(base, exponent_positive_part - exponent_negative_part)
    } else {
        factor.exact_div(&T::coefficient_pow_usize(
            base,
            exponent_negative_part - exponent_positive_part,
        ))
    }
}

impl<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>> Polynomial<T> {
    /// returns the non-reduced GCD computed from the subresultant remainder sequence.
    ///
    /// The algorithm used is derived from the one given in http://web.archive.org/web/20190221040758/https://pdfs.semanticscholar.org/2e6b/95ba84e2160748ba8fc310cdc408fc9bbade.pdf
    pub fn subresultant_gcd(mut self, mut rhs: Self) -> Polynomial<T> {
        let need_negate = if self.len() < rhs.len() {
            mem::swap(&mut self, &mut rhs);
            self.degree().unwrap_or(0).is_odd() && rhs.degree().unwrap_or(0).is_odd()
        } else {
            false
        };
        // now self.len() >= rhs.len()
        if rhs.is_zero() {
            return self;
        }

        assert!(!self.is_zero());
        let one = T::make_one_coefficient_from_element(Cow::Borrowed(&self.elements[0]));

        #[allow(unused_variables)]
        let mut i = 3usize;

        let mut f_i_2 = self; // f[i-2]
        let mut n_i_2 = f_i_2.degree().expect("f_i_2 is known to be non-zero");
        let mut a_i_2 = one.clone();
        let mut c_i_2 = one;

        let mut f_i_1 = rhs; // f[i-1]
        let mut n_i_1 = f_i_1.degree().expect("f_i_1 is known to be non-zero");

        loop {
            let PseudoDivRem { remainder, .. } = f_i_2.pseudo_div_rem(&f_i_1);
            let divisor = -a_i_2 * T::coefficient_pow_usize(-c_i_2.clone(), n_i_2 - n_i_1);
            let f_i = remainder.exact_div(divisor); // f[i]

            let n_i = if let Some(v) = f_i.degree() {
                v
            } else {
                // f_i is zero
                break;
            };

            let a_i_1 = f_i_1
                .nonzero_highest_power_coefficient()
                .expect("f_i_1 is known to be non-zero");

            let c_i_1 = exact_mul_by_signed_power(
                T::coefficient_pow_usize(a_i_1.clone(), n_i_2 - n_i_1),
                c_i_2,
                n_i_1 + 1,
                n_i_2,
            );

            // step to next iteration
            i += 1;
            f_i_2 = f_i_1;
            f_i_1 = f_i;
            n_i_2 = n_i_1;
            n_i_1 = n_i;
            a_i_2 = a_i_1;
            c_i_2 = c_i_1;
        }
        if need_negate {
            -f_i_1
        } else {
            f_i_1
        }
    }
    pub fn nonzero_resultant(self, rhs: Self) -> Option<T> {
        #![allow(clippy::many_single_char_names)]
        // based on algorithm from Computer Algebra and Symbolic Computation: Mathematical Methods by Joel S. Cohen

        // TODO: switch to sharing implementation with subresultant_gcd
        fn recursive_resultant<T: PolynomialCoefficient + for<'a> ExactDiv<&'a T, Output = T>>(
            u: Polynomial<T>,
            v: Polynomial<T>,
            i: usize,
            delta_p: usize,
            psi_p: T,
        ) -> Option<T> {
            let m = u.degree().expect("known to be non-zero");
            let n = v.degree().expect("known to be non-zero");
            if m < n {
                let retval = recursive_resultant(v, u, i, delta_p, psi_p)?;
                if m.is_odd() && n.is_odd() {
                    Some(-retval)
                } else {
                    Some(retval)
                }
            } else if n == 0 {
                Some(T::coefficient_pow_usize(
                    v.into_iter().next().expect("known to be non-zero"),
                    m,
                ))
            } else {
                let r = u.clone().pseudo_div_rem(&v).remainder;
                if r.is_zero() {
                    None
                } else {
                    let delta = m + 1 - n;
                    debug_assert!(delta >= 1);
                    let psi;
                    let beta;
                    if i == 1 {
                        let one =
                            T::make_one_coefficient_from_element(Cow::Borrowed(&v.elements[0]));
                        psi = -one.clone();
                        beta = if delta.is_odd() { -one } else { one };
                    } else {
                        assert!(i > 1);
                        let f = u
                            .nonzero_highest_power_coefficient()
                            .expect("known to be non-zero");
                        psi = match delta_p {
                            0 => unreachable!(),
                            1 => psi_p,
                            _ => T::coefficient_pow_usize(-f.clone(), delta_p - 1)
                                .exact_div(&T::coefficient_pow_usize(psi_p, delta_p - 2)),
                        };
                        beta = f
                            .neg()
                            .mul(T::coefficient_pow_usize(psi.clone(), delta - 1));
                    }
                    let r = r.exact_div(&beta);
                    let l = v
                        .nonzero_highest_power_coefficient()
                        .expect("known to be non-zero");
                    let s = r.degree().expect("known to be non-zero");
                    let mut w = T::coefficient_pow_usize(beta, n);
                    if m.is_odd() && n.is_odd() {
                        w = -w;
                    }
                    w *= recursive_resultant(v, r, i + 1, delta, psi)?;
                    let k = n * delta + s - m;
                    let f = T::coefficient_pow_usize(l, k);
                    Some(w.exact_div(&f))
                }
            }
        }

        if self.is_zero() || rhs.is_zero() {
            None
        } else {
            let zero = T::make_zero_coefficient_from_element(Cow::Borrowed(&self.elements[0]));
            recursive_resultant(self, rhs, 1, 0, zero)
        }
    }
    pub fn resultant(self, rhs: Self) -> T
    where
        T: Zero,
    {
        self.nonzero_resultant(rhs).unwrap_or_else(T::zero)
    }
}

impl<T> GCD for Polynomial<T>
where
    T: PolynomialCoefficient + PolynomialDivSupported + PolynomialReducingFactorSupported,
{
    type Output = Self;
    fn gcd(&self, rhs: &Self) -> Self {
        self.to_reduced()
            .subresultant_gcd(rhs.to_reduced())
            .into_reduced()
    }
    fn gcd_lcm(&self, rhs: &Self) -> GCDAndLCM<Self> {
        let gcd = self.gcd(rhs);
        let lcm = if gcd.is_zero() {
            Zero::zero()
        } else {
            self * rhs.exact_div(&gcd)
        };
        GCDAndLCM { gcd, lcm }
    }
}

impl<T> ExtendedGCD for Polynomial<T>
where
    T: PolynomialCoefficient + PolynomialDivSupported + PolynomialReducingFactorSupported,
{
    fn extended_gcd(&self, rhs: &Self) -> ExtendedGCDResult<Self> {
        let lhs = self;
        let lhs_reducing_factor = if let Some(v) = lhs.nonzero_reducing_factor() {
            v
        } else if let Some(rhs_reducing_factor) = rhs.nonzero_reducing_factor() {
            return ExtendedGCDResult {
                gcd: rhs.exact_div(&rhs_reducing_factor),
                x: Self::zero(),
                y: rhs
                    .to_one_if_nonzero()
                    .expect("known to be nonzero")
                    .exact_div(rhs_reducing_factor),
            };
        } else {
            return ExtendedGCDResult {
                gcd: Self::zero(),
                x: Self::zero(),
                y: Self::zero(),
            };
        };
        struct StateSet<T: PolynomialCoefficient> {
            v: Polynomial<T>,
            x: Polynomial<T>,
            y: Polynomial<T>,
        }
        let mut lhs_state = StateSet {
            v: lhs.exact_div(&lhs_reducing_factor),
            x: lhs
                .to_one_if_nonzero()
                .expect("known to be nonzero")
                .exact_div(lhs_reducing_factor),
            y: Self::zero(),
        };
        let rhs_reducing_factor = if let Some(v) = rhs.nonzero_reducing_factor() {
            v
        } else {
            return ExtendedGCDResult {
                gcd: lhs_state.v,
                x: lhs_state.x,
                y: lhs_state.y,
            };
        };
        let mut rhs_state = StateSet {
            v: rhs.exact_div(&rhs_reducing_factor),
            x: Self::zero(),
            y: rhs
                .to_one_if_nonzero()
                .expect("known to be nonzero")
                .exact_div(rhs_reducing_factor),
        };

        while !rhs_state.v.is_zero() {
            let (quotient, remainder) = lhs_state.v.clone().div_rem(&rhs_state.v);
            let mut new_state = StateSet {
                v: remainder,
                x: lhs_state.x - &rhs_state.x * &quotient,
                y: lhs_state.y - &rhs_state.y * &quotient,
            };
            if let Some(reducing_factor) = new_state.v.nonzero_reducing_factor() {
                new_state.v.exact_div_assign(&reducing_factor);
                new_state.x.exact_div_assign(&reducing_factor);
                new_state.y.exact_div_assign(reducing_factor);
            }
            lhs_state = rhs_state;
            rhs_state = new_state;
        }
        ExtendedGCDResult {
            gcd: lhs_state.v,
            x: lhs_state.x,
            y: lhs_state.y,
        }
    }
    fn extended_gcd_lcm(&self, rhs: &Self) -> ExtendedGCDAndLCM<Self> {
        let ExtendedGCDResult { gcd, x, y } = self.extended_gcd(rhs);
        let lcm = if gcd.is_zero() {
            Zero::zero()
        } else {
            self * rhs.exact_div(&gcd)
        };
        ExtendedGCDAndLCM { gcd, lcm, x, y }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_rational::Ratio;

    #[test]
    fn test_gcd() {
        let r = |n: i64, d: i64| Ratio::<BigInt>::new(n.into(), d.into());
        let ri = |v: i64| Ratio::<BigInt>::from_integer(v.into());
        fn test_case(
            a: Polynomial<Ratio<BigInt>>,
            b: Polynomial<Ratio<BigInt>>,
            gcd: Polynomial<Ratio<BigInt>>,
            lcm: Polynomial<Ratio<BigInt>>,
        ) {
            let results = a.gcd_lcm(&b);
            let extended_results = a.extended_gcd_lcm(&b);
            println!("a=({})  b=({})", a, b);
            println!("gcd=({})  lcm=({})", gcd, lcm);
            println!(
                "results.gcd=({})  results.lcm=({})",
                results.gcd, results.lcm
            );
            println!(
                "extended_results.gcd=({})  extended_results.lcm=({})",
                extended_results.gcd, extended_results.lcm
            );
            println!(
                "extended_results.x=({})  extended_results.y=({})",
                extended_results.x, extended_results.y
            );
            // don't use assert_eq because the debug output is awful
            assert!(gcd == results.gcd);
            assert!(lcm == results.lcm);
            assert!(gcd == extended_results.gcd);
            assert!(lcm == extended_results.lcm);
            assert!(gcd == extended_results.x * a + extended_results.y * b);
        }
        // test cases generated using generate_gcd_test_cases.mac
        test_case(
            vec![ri(2), ri(0), ri(0), ri(2)].into(),
            vec![ri(0), r(1, 3), r(1, 3), r(1, 3)].into(),
            ri(1).into(),
            vec![ri(0), r(2, 3), r(2, 3), r(2, 3), r(2, 3), r(2, 3), r(2, 3)].into(),
        );
        test_case(
            r(1, 3).into(),
            vec![r(1, 3), ri(0), r(1, 3)].into(),
            ri(1).into(),
            vec![r(1, 9), ri(0), r(1, 9)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(1), ri(1)].into(),
            vec![ri(0), ri(0), r(1, 3), r(1, 3)].into(),
            vec![ri(0), ri(0), ri(1), ri(1)].into(),
            vec![ri(0), ri(0), r(1, 3), r(1, 3)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(2)].into(),
            vec![ri(0), r(1, 2), ri(0), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), r(1, 2), ri(1), ri(1), ri(2)].into(),
        );
        test_case(
            Zero::zero(),
            vec![ri(0), ri(0), ri(2), ri(2)].into(),
            vec![ri(0), ri(0), ri(1), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![r(1, 2), ri(1), ri(1)].into(),
            vec![ri(1), ri(0), ri(1), ri(1)].into(),
            ri(1).into(),
            vec![r(1, 2), ri(1), r(3, 2), r(3, 2), ri(2), ri(1)].into(),
        );
        test_case(
            vec![ri(1), ri(0), ri(1), ri(1)].into(),
            vec![ri(0), ri(0), ri(1)].into(),
            ri(1).into(),
            vec![ri(0), ri(0), ri(1), ri(0), ri(1), ri(1)].into(),
        );
        test_case(
            vec![ri(0), r(1, 3), r(2, 3)].into(),
            vec![ri(0), ri(1), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), r(1, 3), ri(1), r(2, 3)].into(),
        );
        test_case(
            vec![r(2, 3), ri(0), r(2, 3), r(2, 3)].into(),
            vec![r(1, 2), ri(0), r(1, 2), r(1, 2)].into(),
            vec![ri(1), ri(0), ri(1), ri(1)].into(),
            vec![r(1, 3), ri(0), r(1, 3), r(1, 3)].into(),
        );
        test_case(
            vec![r(2, 3), r(2, 3), r(2, 3)].into(),
            vec![r(2, 3), r(2, 3), r(2, 3)].into(),
            vec![ri(1), ri(1), ri(1)].into(),
            vec![r(4, 9), r(4, 9), r(4, 9)].into(),
        );
        test_case(
            vec![ri(1), ri(1), r(1, 2), ri(1)].into(),
            r(1, 3).into(),
            ri(1).into(),
            vec![r(1, 3), r(1, 3), r(1, 6), r(1, 3)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(1)].into(),
            vec![ri(0), ri(2), ri(0), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(2), ri(2), ri(1), ri(1)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(1), ri(2)].into(),
            vec![ri(0), r(2, 3)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), r(2, 3), r(2, 3), r(4, 3)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(2)].into(),
            vec![ri(0), ri(2)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(0), ri(4)].into(),
        );
        test_case(
            vec![ri(0), r(1, 3), r(1, 3)].into(),
            vec![ri(1), ri(1), ri(1), ri(1)].into(),
            vec![ri(1), ri(1)].into(),
            vec![ri(0), r(1, 3), r(1, 3), r(1, 3), r(1, 3)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(0), ri(1)].into(),
            vec![ri(0), ri(2), ri(2), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(0), ri(0), ri(2), ri(2), ri(1)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(2), ri(1)].into(),
            vec![ri(1), ri(2)].into(),
            ri(1).into(),
            vec![ri(0), ri(0), ri(2), ri(5), ri(2)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(0), ri(2)].into(),
            vec![ri(1), ri(0), ri(0), ri(2)].into(),
            ri(1).into(),
            vec![ri(0), ri(1), ri(0), ri(2), ri(2), ri(0), ri(4)].into(),
        );
        test_case(
            Zero::zero(),
            vec![ri(1), ri(0), ri(1), r(1, 2)].into(),
            vec![ri(2), ri(0), ri(2), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![ri(1), ri(0), ri(0), ri(1)].into(),
            vec![ri(1), ri(0), ri(1)].into(),
            ri(1).into(),
            vec![ri(1), ri(0), ri(1), ri(1), ri(0), ri(1)].into(),
        );
        test_case(
            vec![r(1, 2), ri(0), ri(0), ri(1)].into(),
            vec![ri(0), r(1, 3), r(2, 3), r(2, 3)].into(),
            ri(1).into(),
            vec![ri(0), r(1, 6), r(1, 3), r(1, 3), r(1, 3), r(2, 3), r(2, 3)].into(),
        );
        test_case(
            Zero::zero(),
            vec![ri(0), ri(0), ri(2)].into(),
            vec![ri(0), ri(0), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![r(1, 2), ri(1), ri(1), ri(1)].into(),
            vec![ri(2), ri(1), ri(1), ri(2)].into(),
            ri(1).into(),
            vec![ri(1), r(5, 2), r(7, 2), ri(5), ri(4), ri(3), ri(2)].into(),
        );
        test_case(
            vec![ri(2), ri(1), ri(1), ri(1)].into(),
            vec![ri(0), r(1, 2), ri(0), ri(1)].into(),
            ri(1).into(),
            vec![ri(0), ri(1), r(1, 2), r(5, 2), r(3, 2), ri(1), ri(1)].into(),
        );
        test_case(
            vec![r(2, 3), ri(0), ri(0), r(2, 3)].into(),
            vec![r(1, 3), ri(0), r(1, 3), r(2, 3)].into(),
            vec![ri(1), ri(1)].into(),
            vec![r(2, 9), r(-2, 9), r(4, 9), r(2, 9), r(-2, 9), r(4, 9)].into(),
        );
        test_case(
            vec![ri(1), ri(1), ri(1), ri(1)].into(),
            vec![ri(0), r(1, 2), ri(1), r(1, 2)].into(),
            vec![ri(1), ri(1)].into(),
            vec![ri(0), r(1, 2), ri(1), ri(1), ri(1), r(1, 2)].into(),
        );
        test_case(
            vec![ri(0), r(1, 2), r(1, 2), ri(1)].into(),
            vec![ri(0), ri(2)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(1), ri(1), ri(2)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(0), ri(1)].into(),
            vec![ri(0), ri(2), ri(0), ri(2)].into(),
            vec![ri(0), ri(1), ri(0), ri(1)].into(),
            vec![ri(0), ri(2), ri(0), ri(2)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(1), ri(2)].into(),
            vec![ri(1), r(1, 2), r(1, 2), r(1, 2)].into(),
            ri(1).into(),
            vec![ri(0), ri(1), r(3, 2), ri(3), ri(2), r(3, 2), ri(1)].into(),
        );
        test_case(
            Zero::zero(),
            vec![ri(0), ri(0), r(2, 3), r(2, 3)].into(),
            vec![ri(0), ri(0), ri(1), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            Zero::zero(),
            vec![ri(2), ri(1), ri(0), ri(1)].into(),
            vec![ri(2), ri(1), ri(0), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![ri(0), ri(0), ri(2)].into(),
            vec![ri(0), ri(1), ri(1), ri(2)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(0), ri(2), ri(2), ri(4)].into(),
        );
        test_case(
            vec![r(2, 3), ri(0), ri(0), r(2, 3)].into(),
            vec![r(1, 3), ri(0), r(1, 3), r(2, 3)].into(),
            vec![ri(1), ri(1)].into(),
            vec![r(2, 9), r(-2, 9), r(4, 9), r(2, 9), r(-2, 9), r(4, 9)].into(),
        );
        test_case(
            vec![r(1, 3), r(1, 3), r(1, 3)].into(),
            Zero::zero(),
            vec![ri(1), ri(1), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![ri(0), r(2, 3), r(2, 3), r(1, 3)].into(),
            vec![ri(0), r(1, 3), r(1, 3), r(1, 3)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), r(2, 9), r(4, 9), r(5, 9), r(1, 3), r(1, 9)].into(),
        );
        test_case(
            vec![r(1, 3), r(2, 3), r(1, 3), r(2, 3)].into(),
            vec![ri(1), ri(1), ri(1), ri(1)].into(),
            vec![ri(1), ri(0), ri(1)].into(),
            vec![r(1, 3), ri(1), ri(1), ri(1), r(2, 3)].into(),
        );
        test_case(
            vec![ri(1), ri(2), ri(2), ri(1)].into(),
            vec![r(1, 3), r(1, 3), r(1, 3)].into(),
            vec![ri(1), ri(1), ri(1)].into(),
            vec![r(1, 3), r(2, 3), r(2, 3), r(1, 3)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(1), ri(1)].into(),
            vec![ri(0), ri(2), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(2), ri(3), ri(3), ri(1)].into(),
        );
        test_case(
            vec![ri(1), r(1, 2), ri(0), r(1, 2)].into(),
            vec![ri(0), ri(1), ri(1)].into(),
            vec![ri(1), ri(1)].into(),
            vec![ri(0), ri(1), r(1, 2), ri(0), r(1, 2)].into(),
        );
        test_case(
            vec![r(2, 3), r(2, 3), r(1, 3), r(1, 3)].into(),
            r(1, 3).into(),
            ri(1).into(),
            vec![r(2, 9), r(2, 9), r(1, 9), r(1, 9)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(2)].into(),
            vec![ri(0), ri(1), r(1, 2), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(0), ri(2), ri(1), ri(2)].into(),
        );
        test_case(
            vec![ri(0), r(1, 3), r(1, 3), r(1, 3)].into(),
            Zero::zero(),
            vec![ri(0), ri(1), ri(1), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![ri(0), ri(0), r(1, 2)].into(),
            vec![ri(0), r(1, 3), r(2, 3), r(2, 3)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(0), r(1, 6), r(1, 3), r(1, 3)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(1)].into(),
            vec![ri(0), ri(1), ri(1), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), ri(0), ri(1), ri(1), ri(1)].into(),
        );
        test_case(
            vec![ri(1), ri(1), ri(2), ri(1)].into(),
            vec![ri(1), ri(1), ri(2), ri(1)].into(),
            vec![ri(1), ri(1), ri(2), ri(1)].into(),
            vec![ri(1), ri(1), ri(2), ri(1)].into(),
        );
        test_case(
            vec![ri(0), ri(0), ri(0), r(1, 2)].into(),
            vec![r(2, 3), r(1, 3), r(2, 3), r(2, 3)].into(),
            ri(1).into(),
            vec![ri(0), ri(0), ri(0), r(1, 3), r(1, 6), r(1, 3), r(1, 3)].into(),
        );
        test_case(
            vec![ri(2), ri(2)].into(),
            vec![r(2, 3), ri(0), ri(0), r(2, 3)].into(),
            vec![ri(1), ri(1)].into(),
            vec![r(4, 3), ri(0), ri(0), r(4, 3)].into(),
        );
        test_case(
            Zero::zero(),
            vec![ri(2), ri(0), ri(0), ri(1)].into(),
            vec![ri(2), ri(0), ri(0), ri(1)].into(),
            Zero::zero(),
        );
        test_case(
            vec![ri(0), ri(1), ri(2), ri(2)].into(),
            vec![ri(0), r(1, 2), ri(0), ri(1)].into(),
            vec![ri(0), ri(1)].into(),
            vec![ri(0), r(1, 2), ri(1), ri(2), ri(2), ri(2)].into(),
        );
        test_case(
            vec![ri(0), ri(1), ri(2), ri(2)].into(),
            vec![ri(0), r(1, 3), r(2, 3), r(2, 3)].into(),
            vec![ri(0), r(1, 2), ri(1), ri(1)].into(),
            vec![ri(0), r(2, 3), r(4, 3), r(4, 3)].into(),
        );
        test_case(
            vec![ri(0), r(1, 2), r(1, 2), ri(1)].into(),
            vec![ri(0), r(1, 3), r(1, 3), r(2, 3)].into(),
            vec![ri(0), r(1, 2), r(1, 2), ri(1)].into(),
            vec![ri(0), r(1, 3), r(1, 3), r(2, 3)].into(),
        );
        test_case(Zero::zero(), Zero::zero(), Zero::zero(), Zero::zero());
    }

    #[test]
    fn test_resultant() {
        fn test_case(lhs: &[i32], rhs: &[i32], expected: i128) {
            let lhs: Polynomial<_> = lhs.iter().copied().map(BigInt::from).collect();
            let rhs: Polynomial<_> = rhs.iter().copied().map(BigInt::from).collect();
            let expected = BigInt::from(expected);
            println!("lhs: {}", lhs);
            println!("rhs: {}", rhs);
            println!("expected: {}", expected);
            let resultant = lhs.resultant(rhs);
            println!("resultant: {}", resultant);
            assert!(expected == resultant);
        }
        test_case(&[], &[], 0);
        test_case(&[], &[0, 0, 1], 0);
        test_case(&[], &[0, 0, 2], 0);
        test_case(&[], &[0, 1], 0);
        test_case(&[], &[0, 1, 1], 0);
        test_case(&[], &[0, 1, 2], 0);
        test_case(&[], &[0, 2], 0);
        test_case(&[], &[0, 2, 1], 0);
        test_case(&[], &[0, 2, 2], 0);
        test_case(&[], &[1], 0);
        test_case(&[], &[1, 0, 1], 0);
        test_case(&[], &[1, 0, 2], 0);
        test_case(&[], &[1, 1], 0);
        test_case(&[], &[1, 1, 1], 0);
        test_case(&[], &[1, 1, 2], 0);
        test_case(&[], &[1, 2], 0);
        test_case(&[], &[1, 2, 1], 0);
        test_case(&[], &[1, 2, 2], 0);
        test_case(&[], &[2], 0);
        test_case(&[], &[2, 0, 1], 0);
        test_case(&[], &[2, 0, 2], 0);
        test_case(&[], &[2, 1], 0);
        test_case(&[], &[2, 1, 1], 0);
        test_case(&[], &[2, 1, 2], 0);
        test_case(&[], &[2, 2], 0);
        test_case(&[], &[2, 2, 1], 0);
        test_case(&[], &[2, 2, 2], 0);
        test_case(&[0, 0, 1], &[], 0);
        test_case(&[0, 0, 1], &[0, 0, 1], 0);
        test_case(&[0, 0, 1], &[0, 0, 2], 0);
        test_case(&[0, 0, 1], &[0, 1], 0);
        test_case(&[0, 0, 1], &[0, 1, 1], 0);
        test_case(&[0, 0, 1], &[0, 1, 2], 0);
        test_case(&[0, 0, 1], &[0, 2], 0);
        test_case(&[0, 0, 1], &[0, 2, 1], 0);
        test_case(&[0, 0, 1], &[0, 2, 2], 0);
        test_case(&[0, 0, 1], &[1], 1);
        test_case(&[0, 0, 1], &[1, 0, 1], 1);
        test_case(&[0, 0, 1], &[1, 0, 2], 1);
        test_case(&[0, 0, 1], &[1, 1], 1);
        test_case(&[0, 0, 1], &[1, 1, 1], 1);
        test_case(&[0, 0, 1], &[1, 1, 2], 1);
        test_case(&[0, 0, 1], &[1, 2], 1);
        test_case(&[0, 0, 1], &[1, 2, 1], 1);
        test_case(&[0, 0, 1], &[1, 2, 2], 1);
        test_case(&[0, 0, 1], &[2], 4);
        test_case(&[0, 0, 1], &[2, 0, 1], 4);
        test_case(&[0, 0, 1], &[2, 0, 2], 4);
        test_case(&[0, 0, 1], &[2, 1], 4);
        test_case(&[0, 0, 1], &[2, 1, 1], 4);
        test_case(&[0, 0, 1], &[2, 1, 2], 4);
        test_case(&[0, 0, 1], &[2, 2], 4);
        test_case(&[0, 0, 1], &[2, 2, 1], 4);
        test_case(&[0, 0, 1], &[2, 2, 2], 4);
        test_case(&[0, 0, 2], &[], 0);
        test_case(&[0, 0, 2], &[0, 0, 1], 0);
        test_case(&[0, 0, 2], &[0, 0, 2], 0);
        test_case(&[0, 0, 2], &[0, 1], 0);
        test_case(&[0, 0, 2], &[0, 1, 1], 0);
        test_case(&[0, 0, 2], &[0, 1, 2], 0);
        test_case(&[0, 0, 2], &[0, 2], 0);
        test_case(&[0, 0, 2], &[0, 2, 1], 0);
        test_case(&[0, 0, 2], &[0, 2, 2], 0);
        test_case(&[0, 0, 2], &[1], 1);
        test_case(&[0, 0, 2], &[1, 0, 1], 4);
        test_case(&[0, 0, 2], &[1, 0, 2], 4);
        test_case(&[0, 0, 2], &[1, 1], 2);
        test_case(&[0, 0, 2], &[1, 1, 1], 4);
        test_case(&[0, 0, 2], &[1, 1, 2], 4);
        test_case(&[0, 0, 2], &[1, 2], 2);
        test_case(&[0, 0, 2], &[1, 2, 1], 4);
        test_case(&[0, 0, 2], &[1, 2, 2], 4);
        test_case(&[0, 0, 2], &[2], 4);
        test_case(&[0, 0, 2], &[2, 0, 1], 16);
        test_case(&[0, 0, 2], &[2, 0, 2], 16);
        test_case(&[0, 0, 2], &[2, 1], 8);
        test_case(&[0, 0, 2], &[2, 1, 1], 16);
        test_case(&[0, 0, 2], &[2, 1, 2], 16);
        test_case(&[0, 0, 2], &[2, 2], 8);
        test_case(&[0, 0, 2], &[2, 2, 1], 16);
        test_case(&[0, 0, 2], &[2, 2, 2], 16);
        test_case(&[0, 1], &[], 0);
        test_case(&[0, 1], &[0, 0, 1], 0);
        test_case(&[0, 1], &[0, 0, 2], 0);
        test_case(&[0, 1], &[0, 1], 0);
        test_case(&[0, 1], &[0, 1, 1], 0);
        test_case(&[0, 1], &[0, 1, 2], 0);
        test_case(&[0, 1], &[0, 2], 0);
        test_case(&[0, 1], &[0, 2, 1], 0);
        test_case(&[0, 1], &[0, 2, 2], 0);
        test_case(&[0, 1], &[1], 1);
        test_case(&[0, 1], &[1, 0, 1], 1);
        test_case(&[0, 1], &[1, 0, 2], 1);
        test_case(&[0, 1], &[1, 1], 1);
        test_case(&[0, 1], &[1, 1, 1], 1);
        test_case(&[0, 1], &[1, 1, 2], 1);
        test_case(&[0, 1], &[1, 2], 1);
        test_case(&[0, 1], &[1, 2, 1], 1);
        test_case(&[0, 1], &[1, 2, 2], 1);
        test_case(&[0, 1], &[2], 2);
        test_case(&[0, 1], &[2, 0, 1], 2);
        test_case(&[0, 1], &[2, 0, 2], 2);
        test_case(&[0, 1], &[2, 1], 2);
        test_case(&[0, 1], &[2, 1, 1], 2);
        test_case(&[0, 1], &[2, 1, 2], 2);
        test_case(&[0, 1], &[2, 2], 2);
        test_case(&[0, 1], &[2, 2, 1], 2);
        test_case(&[0, 1], &[2, 2, 2], 2);
        test_case(&[0, 1, 1], &[], 0);
        test_case(&[0, 1, 1], &[0, 0, 1], 0);
        test_case(&[0, 1, 1], &[0, 0, 2], 0);
        test_case(&[0, 1, 1], &[0, 1], 0);
        test_case(&[0, 1, 1], &[0, 1, 1], 0);
        test_case(&[0, 1, 1], &[0, 1, 2], 0);
        test_case(&[0, 1, 1], &[0, 2], 0);
        test_case(&[0, 1, 1], &[0, 2, 1], 0);
        test_case(&[0, 1, 1], &[0, 2, 2], 0);
        test_case(&[0, 1, 1], &[1], 1);
        test_case(&[0, 1, 1], &[1, 0, 1], 2);
        test_case(&[0, 1, 1], &[1, 0, 2], 3);
        test_case(&[0, 1, 1], &[1, 1], 0);
        test_case(&[0, 1, 1], &[1, 1, 1], 1);
        test_case(&[0, 1, 1], &[1, 1, 2], 2);
        test_case(&[0, 1, 1], &[1, 2], -1);
        test_case(&[0, 1, 1], &[1, 2, 1], 0);
        test_case(&[0, 1, 1], &[1, 2, 2], 1);
        test_case(&[0, 1, 1], &[2], 4);
        test_case(&[0, 1, 1], &[2, 0, 1], 6);
        test_case(&[0, 1, 1], &[2, 0, 2], 8);
        test_case(&[0, 1, 1], &[2, 1], 2);
        test_case(&[0, 1, 1], &[2, 1, 1], 4);
        test_case(&[0, 1, 1], &[2, 1, 2], 6);
        test_case(&[0, 1, 1], &[2, 2], 0);
        test_case(&[0, 1, 1], &[2, 2, 1], 2);
        test_case(&[0, 1, 1], &[2, 2, 2], 4);
        test_case(&[0, 1, 2], &[], 0);
        test_case(&[0, 1, 2], &[0, 0, 1], 0);
        test_case(&[0, 1, 2], &[0, 0, 2], 0);
        test_case(&[0, 1, 2], &[0, 1], 0);
        test_case(&[0, 1, 2], &[0, 1, 1], 0);
        test_case(&[0, 1, 2], &[0, 1, 2], 0);
        test_case(&[0, 1, 2], &[0, 2], 0);
        test_case(&[0, 1, 2], &[0, 2, 1], 0);
        test_case(&[0, 1, 2], &[0, 2, 2], 0);
        test_case(&[0, 1, 2], &[1], 1);
        test_case(&[0, 1, 2], &[1, 0, 1], 5);
        test_case(&[0, 1, 2], &[1, 0, 2], 6);
        test_case(&[0, 1, 2], &[1, 1], 1);
        test_case(&[0, 1, 2], &[1, 1, 1], 3);
        test_case(&[0, 1, 2], &[1, 1, 2], 4);
        test_case(&[0, 1, 2], &[1, 2], 0);
        test_case(&[0, 1, 2], &[1, 2, 1], 1);
        test_case(&[0, 1, 2], &[1, 2, 2], 2);
        test_case(&[0, 1, 2], &[2], 4);
        test_case(&[0, 1, 2], &[2, 0, 1], 18);
        test_case(&[0, 1, 2], &[2, 0, 2], 20);
        test_case(&[0, 1, 2], &[2, 1], 6);
        test_case(&[0, 1, 2], &[2, 1, 1], 14);
        test_case(&[0, 1, 2], &[2, 1, 2], 16);
        test_case(&[0, 1, 2], &[2, 2], 4);
        test_case(&[0, 1, 2], &[2, 2, 1], 10);
        test_case(&[0, 1, 2], &[2, 2, 2], 12);
        test_case(&[0, 2], &[], 0);
        test_case(&[0, 2], &[0, 0, 1], 0);
        test_case(&[0, 2], &[0, 0, 2], 0);
        test_case(&[0, 2], &[0, 1], 0);
        test_case(&[0, 2], &[0, 1, 1], 0);
        test_case(&[0, 2], &[0, 1, 2], 0);
        test_case(&[0, 2], &[0, 2], 0);
        test_case(&[0, 2], &[0, 2, 1], 0);
        test_case(&[0, 2], &[0, 2, 2], 0);
        test_case(&[0, 2], &[1], 1);
        test_case(&[0, 2], &[1, 0, 1], 4);
        test_case(&[0, 2], &[1, 0, 2], 4);
        test_case(&[0, 2], &[1, 1], 2);
        test_case(&[0, 2], &[1, 1, 1], 4);
        test_case(&[0, 2], &[1, 1, 2], 4);
        test_case(&[0, 2], &[1, 2], 2);
        test_case(&[0, 2], &[1, 2, 1], 4);
        test_case(&[0, 2], &[1, 2, 2], 4);
        test_case(&[0, 2], &[2], 2);
        test_case(&[0, 2], &[2, 0, 1], 8);
        test_case(&[0, 2], &[2, 0, 2], 8);
        test_case(&[0, 2], &[2, 1], 4);
        test_case(&[0, 2], &[2, 1, 1], 8);
        test_case(&[0, 2], &[2, 1, 2], 8);
        test_case(&[0, 2], &[2, 2], 4);
        test_case(&[0, 2], &[2, 2, 1], 8);
        test_case(&[0, 2], &[2, 2, 2], 8);
        test_case(&[0, 2, 1], &[], 0);
        test_case(&[0, 2, 1], &[0, 0, 1], 0);
        test_case(&[0, 2, 1], &[0, 0, 2], 0);
        test_case(&[0, 2, 1], &[0, 1], 0);
        test_case(&[0, 2, 1], &[0, 1, 1], 0);
        test_case(&[0, 2, 1], &[0, 1, 2], 0);
        test_case(&[0, 2, 1], &[0, 2], 0);
        test_case(&[0, 2, 1], &[0, 2, 1], 0);
        test_case(&[0, 2, 1], &[0, 2, 2], 0);
        test_case(&[0, 2, 1], &[1], 1);
        test_case(&[0, 2, 1], &[1, 0, 1], 5);
        test_case(&[0, 2, 1], &[1, 0, 2], 9);
        test_case(&[0, 2, 1], &[1, 1], -1);
        test_case(&[0, 2, 1], &[1, 1, 1], 3);
        test_case(&[0, 2, 1], &[1, 1, 2], 7);
        test_case(&[0, 2, 1], &[1, 2], -3);
        test_case(&[0, 2, 1], &[1, 2, 1], 1);
        test_case(&[0, 2, 1], &[1, 2, 2], 5);
        test_case(&[0, 2, 1], &[2], 4);
        test_case(&[0, 2, 1], &[2, 0, 1], 12);
        test_case(&[0, 2, 1], &[2, 0, 2], 20);
        test_case(&[0, 2, 1], &[2, 1], 0);
        test_case(&[0, 2, 1], &[2, 1, 1], 8);
        test_case(&[0, 2, 1], &[2, 1, 2], 16);
        test_case(&[0, 2, 1], &[2, 2], -4);
        test_case(&[0, 2, 1], &[2, 2, 1], 4);
        test_case(&[0, 2, 1], &[2, 2, 2], 12);
        test_case(&[0, 2, 2], &[], 0);
        test_case(&[0, 2, 2], &[0, 0, 1], 0);
        test_case(&[0, 2, 2], &[0, 0, 2], 0);
        test_case(&[0, 2, 2], &[0, 1], 0);
        test_case(&[0, 2, 2], &[0, 1, 1], 0);
        test_case(&[0, 2, 2], &[0, 1, 2], 0);
        test_case(&[0, 2, 2], &[0, 2], 0);
        test_case(&[0, 2, 2], &[0, 2, 1], 0);
        test_case(&[0, 2, 2], &[0, 2, 2], 0);
        test_case(&[0, 2, 2], &[1], 1);
        test_case(&[0, 2, 2], &[1, 0, 1], 8);
        test_case(&[0, 2, 2], &[1, 0, 2], 12);
        test_case(&[0, 2, 2], &[1, 1], 0);
        test_case(&[0, 2, 2], &[1, 1, 1], 4);
        test_case(&[0, 2, 2], &[1, 1, 2], 8);
        test_case(&[0, 2, 2], &[1, 2], -2);
        test_case(&[0, 2, 2], &[1, 2, 1], 0);
        test_case(&[0, 2, 2], &[1, 2, 2], 4);
        test_case(&[0, 2, 2], &[2], 4);
        test_case(&[0, 2, 2], &[2, 0, 1], 24);
        test_case(&[0, 2, 2], &[2, 0, 2], 32);
        test_case(&[0, 2, 2], &[2, 1], 4);
        test_case(&[0, 2, 2], &[2, 1, 1], 16);
        test_case(&[0, 2, 2], &[2, 1, 2], 24);
        test_case(&[0, 2, 2], &[2, 2], 0);
        test_case(&[0, 2, 2], &[2, 2, 1], 8);
        test_case(&[0, 2, 2], &[2, 2, 2], 16);
        test_case(&[1], &[], 0);
        test_case(&[1], &[0, 0, 1], 1);
        test_case(&[1], &[0, 0, 2], 1);
        test_case(&[1], &[0, 1], 1);
        test_case(&[1], &[0, 1, 1], 1);
        test_case(&[1], &[0, 1, 2], 1);
        test_case(&[1], &[0, 2], 1);
        test_case(&[1], &[0, 2, 1], 1);
        test_case(&[1], &[0, 2, 2], 1);
        test_case(&[1], &[1], 1);
        test_case(&[1], &[1, 0, 1], 1);
        test_case(&[1], &[1, 0, 2], 1);
        test_case(&[1], &[1, 1], 1);
        test_case(&[1], &[1, 1, 1], 1);
        test_case(&[1], &[1, 1, 2], 1);
        test_case(&[1], &[1, 2], 1);
        test_case(&[1], &[1, 2, 1], 1);
        test_case(&[1], &[1, 2, 2], 1);
        test_case(&[1], &[2], 1);
        test_case(&[1], &[2, 0, 1], 1);
        test_case(&[1], &[2, 0, 2], 1);
        test_case(&[1], &[2, 1], 1);
        test_case(&[1], &[2, 1, 1], 1);
        test_case(&[1], &[2, 1, 2], 1);
        test_case(&[1], &[2, 2], 1);
        test_case(&[1], &[2, 2, 1], 1);
        test_case(&[1], &[2, 2, 2], 1);
        test_case(&[1, 0, 1], &[], 0);
        test_case(&[1, 0, 1], &[0, 0, 1], 1);
        test_case(&[1, 0, 1], &[0, 0, 2], 4);
        test_case(&[1, 0, 1], &[0, 1], 1);
        test_case(&[1, 0, 1], &[0, 1, 1], 2);
        test_case(&[1, 0, 1], &[0, 1, 2], 5);
        test_case(&[1, 0, 1], &[0, 2], 4);
        test_case(&[1, 0, 1], &[0, 2, 1], 5);
        test_case(&[1, 0, 1], &[0, 2, 2], 8);
        test_case(&[1, 0, 1], &[1], 1);
        test_case(&[1, 0, 1], &[1, 0, 1], 0);
        test_case(&[1, 0, 1], &[1, 0, 2], 1);
        test_case(&[1, 0, 1], &[1, 1], 2);
        test_case(&[1, 0, 1], &[1, 1, 1], 1);
        test_case(&[1, 0, 1], &[1, 1, 2], 2);
        test_case(&[1, 0, 1], &[1, 2], 5);
        test_case(&[1, 0, 1], &[1, 2, 1], 4);
        test_case(&[1, 0, 1], &[1, 2, 2], 5);
        test_case(&[1, 0, 1], &[2], 4);
        test_case(&[1, 0, 1], &[2, 0, 1], 1);
        test_case(&[1, 0, 1], &[2, 0, 2], 0);
        test_case(&[1, 0, 1], &[2, 1], 5);
        test_case(&[1, 0, 1], &[2, 1, 1], 2);
        test_case(&[1, 0, 1], &[2, 1, 2], 1);
        test_case(&[1, 0, 1], &[2, 2], 8);
        test_case(&[1, 0, 1], &[2, 2, 1], 5);
        test_case(&[1, 0, 1], &[2, 2, 2], 4);
        test_case(&[1, 0, 2], &[], 0);
        test_case(&[1, 0, 2], &[0, 0, 1], 1);
        test_case(&[1, 0, 2], &[0, 0, 2], 4);
        test_case(&[1, 0, 2], &[0, 1], 1);
        test_case(&[1, 0, 2], &[0, 1, 1], 3);
        test_case(&[1, 0, 2], &[0, 1, 2], 6);
        test_case(&[1, 0, 2], &[0, 2], 4);
        test_case(&[1, 0, 2], &[0, 2, 1], 9);
        test_case(&[1, 0, 2], &[0, 2, 2], 12);
        test_case(&[1, 0, 2], &[1], 1);
        test_case(&[1, 0, 2], &[1, 0, 1], 1);
        test_case(&[1, 0, 2], &[1, 0, 2], 0);
        test_case(&[1, 0, 2], &[1, 1], 3);
        test_case(&[1, 0, 2], &[1, 1, 1], 3);
        test_case(&[1, 0, 2], &[1, 1, 2], 2);
        test_case(&[1, 0, 2], &[1, 2], 6);
        test_case(&[1, 0, 2], &[1, 2, 1], 9);
        test_case(&[1, 0, 2], &[1, 2, 2], 8);
        test_case(&[1, 0, 2], &[2], 4);
        test_case(&[1, 0, 2], &[2, 0, 1], 9);
        test_case(&[1, 0, 2], &[2, 0, 2], 4);
        test_case(&[1, 0, 2], &[2, 1], 9);
        test_case(&[1, 0, 2], &[2, 1, 1], 11);
        test_case(&[1, 0, 2], &[2, 1, 2], 6);
        test_case(&[1, 0, 2], &[2, 2], 12);
        test_case(&[1, 0, 2], &[2, 2, 1], 17);
        test_case(&[1, 0, 2], &[2, 2, 2], 12);
        test_case(&[1, 1], &[], 0);
        test_case(&[1, 1], &[0, 0, 1], 1);
        test_case(&[1, 1], &[0, 0, 2], 2);
        test_case(&[1, 1], &[0, 1], -1);
        test_case(&[1, 1], &[0, 1, 1], 0);
        test_case(&[1, 1], &[0, 1, 2], 1);
        test_case(&[1, 1], &[0, 2], -2);
        test_case(&[1, 1], &[0, 2, 1], -1);
        test_case(&[1, 1], &[0, 2, 2], 0);
        test_case(&[1, 1], &[1], 1);
        test_case(&[1, 1], &[1, 0, 1], 2);
        test_case(&[1, 1], &[1, 0, 2], 3);
        test_case(&[1, 1], &[1, 1], 0);
        test_case(&[1, 1], &[1, 1, 1], 1);
        test_case(&[1, 1], &[1, 1, 2], 2);
        test_case(&[1, 1], &[1, 2], -1);
        test_case(&[1, 1], &[1, 2, 1], 0);
        test_case(&[1, 1], &[1, 2, 2], 1);
        test_case(&[1, 1], &[2], 2);
        test_case(&[1, 1], &[2, 0, 1], 3);
        test_case(&[1, 1], &[2, 0, 2], 4);
        test_case(&[1, 1], &[2, 1], 1);
        test_case(&[1, 1], &[2, 1, 1], 2);
        test_case(&[1, 1], &[2, 1, 2], 3);
        test_case(&[1, 1], &[2, 2], 0);
        test_case(&[1, 1], &[2, 2, 1], 1);
        test_case(&[1, 1], &[2, 2, 2], 2);
        test_case(&[1, 1, 1], &[], 0);
        test_case(&[1, 1, 1], &[0, 0, 1], 1);
        test_case(&[1, 1, 1], &[0, 0, 2], 4);
        test_case(&[1, 1, 1], &[0, 1], 1);
        test_case(&[1, 1, 1], &[0, 1, 1], 1);
        test_case(&[1, 1, 1], &[0, 1, 2], 3);
        test_case(&[1, 1, 1], &[0, 2], 4);
        test_case(&[1, 1, 1], &[0, 2, 1], 3);
        test_case(&[1, 1, 1], &[0, 2, 2], 4);
        test_case(&[1, 1, 1], &[1], 1);
        test_case(&[1, 1, 1], &[1, 0, 1], 1);
        test_case(&[1, 1, 1], &[1, 0, 2], 3);
        test_case(&[1, 1, 1], &[1, 1], 1);
        test_case(&[1, 1, 1], &[1, 1, 1], 0);
        test_case(&[1, 1, 1], &[1, 1, 2], 1);
        test_case(&[1, 1, 1], &[1, 2], 3);
        test_case(&[1, 1, 1], &[1, 2, 1], 1);
        test_case(&[1, 1, 1], &[1, 2, 2], 1);
        test_case(&[1, 1, 1], &[2], 4);
        test_case(&[1, 1, 1], &[2, 0, 1], 3);
        test_case(&[1, 1, 1], &[2, 0, 2], 4);
        test_case(&[1, 1, 1], &[2, 1], 3);
        test_case(&[1, 1, 1], &[2, 1, 1], 1);
        test_case(&[1, 1, 1], &[2, 1, 2], 1);
        test_case(&[1, 1, 1], &[2, 2], 4);
        test_case(&[1, 1, 1], &[2, 2, 1], 1);
        test_case(&[1, 1, 1], &[2, 2, 2], 0);
        test_case(&[1, 1, 2], &[], 0);
        test_case(&[1, 1, 2], &[0, 0, 1], 1);
        test_case(&[1, 1, 2], &[0, 0, 2], 4);
        test_case(&[1, 1, 2], &[0, 1], 1);
        test_case(&[1, 1, 2], &[0, 1, 1], 2);
        test_case(&[1, 1, 2], &[0, 1, 2], 4);
        test_case(&[1, 1, 2], &[0, 2], 4);
        test_case(&[1, 1, 2], &[0, 2, 1], 7);
        test_case(&[1, 1, 2], &[0, 2, 2], 8);
        test_case(&[1, 1, 2], &[1], 1);
        test_case(&[1, 1, 2], &[1, 0, 1], 2);
        test_case(&[1, 1, 2], &[1, 0, 2], 2);
        test_case(&[1, 1, 2], &[1, 1], 2);
        test_case(&[1, 1, 2], &[1, 1, 1], 1);
        test_case(&[1, 1, 2], &[1, 1, 2], 0);
        test_case(&[1, 1, 2], &[1, 2], 4);
        test_case(&[1, 1, 2], &[1, 2, 1], 4);
        test_case(&[1, 1, 2], &[1, 2, 2], 2);
        test_case(&[1, 1, 2], &[2], 4);
        test_case(&[1, 1, 2], &[2, 0, 1], 11);
        test_case(&[1, 1, 2], &[2, 0, 2], 8);
        test_case(&[1, 1, 2], &[2, 1], 7);
        test_case(&[1, 1, 2], &[2, 1, 1], 8);
        test_case(&[1, 1, 2], &[2, 1, 2], 4);
        test_case(&[1, 1, 2], &[2, 2], 8);
        test_case(&[1, 1, 2], &[2, 2, 1], 9);
        test_case(&[1, 1, 2], &[2, 2, 2], 4);
        test_case(&[1, 2], &[], 0);
        test_case(&[1, 2], &[0, 0, 1], 1);
        test_case(&[1, 2], &[0, 0, 2], 2);
        test_case(&[1, 2], &[0, 1], -1);
        test_case(&[1, 2], &[0, 1, 1], -1);
        test_case(&[1, 2], &[0, 1, 2], 0);
        test_case(&[1, 2], &[0, 2], -2);
        test_case(&[1, 2], &[0, 2, 1], -3);
        test_case(&[1, 2], &[0, 2, 2], -2);
        test_case(&[1, 2], &[1], 1);
        test_case(&[1, 2], &[1, 0, 1], 5);
        test_case(&[1, 2], &[1, 0, 2], 6);
        test_case(&[1, 2], &[1, 1], 1);
        test_case(&[1, 2], &[1, 1, 1], 3);
        test_case(&[1, 2], &[1, 1, 2], 4);
        test_case(&[1, 2], &[1, 2], 0);
        test_case(&[1, 2], &[1, 2, 1], 1);
        test_case(&[1, 2], &[1, 2, 2], 2);
        test_case(&[1, 2], &[2], 2);
        test_case(&[1, 2], &[2, 0, 1], 9);
        test_case(&[1, 2], &[2, 0, 2], 10);
        test_case(&[1, 2], &[2, 1], 3);
        test_case(&[1, 2], &[2, 1, 1], 7);
        test_case(&[1, 2], &[2, 1, 2], 8);
        test_case(&[1, 2], &[2, 2], 2);
        test_case(&[1, 2], &[2, 2, 1], 5);
        test_case(&[1, 2], &[2, 2, 2], 6);
        test_case(&[1, 2, 1], &[], 0);
        test_case(&[1, 2, 1], &[0, 0, 1], 1);
        test_case(&[1, 2, 1], &[0, 0, 2], 4);
        test_case(&[1, 2, 1], &[0, 1], 1);
        test_case(&[1, 2, 1], &[0, 1, 1], 0);
        test_case(&[1, 2, 1], &[0, 1, 2], 1);
        test_case(&[1, 2, 1], &[0, 2], 4);
        test_case(&[1, 2, 1], &[0, 2, 1], 1);
        test_case(&[1, 2, 1], &[0, 2, 2], 0);
        test_case(&[1, 2, 1], &[1], 1);
        test_case(&[1, 2, 1], &[1, 0, 1], 4);
        test_case(&[1, 2, 1], &[1, 0, 2], 9);
        test_case(&[1, 2, 1], &[1, 1], 0);
        test_case(&[1, 2, 1], &[1, 1, 1], 1);
        test_case(&[1, 2, 1], &[1, 1, 2], 4);
        test_case(&[1, 2, 1], &[1, 2], 1);
        test_case(&[1, 2, 1], &[1, 2, 1], 0);
        test_case(&[1, 2, 1], &[1, 2, 2], 1);
        test_case(&[1, 2, 1], &[2], 4);
        test_case(&[1, 2, 1], &[2, 0, 1], 9);
        test_case(&[1, 2, 1], &[2, 0, 2], 16);
        test_case(&[1, 2, 1], &[2, 1], 1);
        test_case(&[1, 2, 1], &[2, 1, 1], 4);
        test_case(&[1, 2, 1], &[2, 1, 2], 9);
        test_case(&[1, 2, 1], &[2, 2], 0);
        test_case(&[1, 2, 1], &[2, 2, 1], 1);
        test_case(&[1, 2, 1], &[2, 2, 2], 4);
        test_case(&[1, 2, 2], &[], 0);
        test_case(&[1, 2, 2], &[0, 0, 1], 1);
        test_case(&[1, 2, 2], &[0, 0, 2], 4);
        test_case(&[1, 2, 2], &[0, 1], 1);
        test_case(&[1, 2, 2], &[0, 1, 1], 1);
        test_case(&[1, 2, 2], &[0, 1, 2], 2);
        test_case(&[1, 2, 2], &[0, 2], 4);
        test_case(&[1, 2, 2], &[0, 2, 1], 5);
        test_case(&[1, 2, 2], &[0, 2, 2], 4);
        test_case(&[1, 2, 2], &[1], 1);
        test_case(&[1, 2, 2], &[1, 0, 1], 5);
        test_case(&[1, 2, 2], &[1, 0, 2], 8);
        test_case(&[1, 2, 2], &[1, 1], 1);
        test_case(&[1, 2, 2], &[1, 1, 1], 1);
        test_case(&[1, 2, 2], &[1, 1, 2], 2);
        test_case(&[1, 2, 2], &[1, 2], 2);
        test_case(&[1, 2, 2], &[1, 2, 1], 1);
        test_case(&[1, 2, 2], &[1, 2, 2], 0);
        test_case(&[1, 2, 2], &[2], 4);
        test_case(&[1, 2, 2], &[2, 0, 1], 17);
        test_case(&[1, 2, 2], &[2, 0, 2], 20);
        test_case(&[1, 2, 2], &[2, 1], 5);
        test_case(&[1, 2, 2], &[2, 1, 1], 9);
        test_case(&[1, 2, 2], &[2, 1, 2], 10);
        test_case(&[1, 2, 2], &[2, 2], 4);
        test_case(&[1, 2, 2], &[2, 2, 1], 5);
        test_case(&[1, 2, 2], &[2, 2, 2], 4);
        test_case(&[2], &[], 0);
        test_case(&[2], &[0, 0, 1], 4);
        test_case(&[2], &[0, 0, 2], 4);
        test_case(&[2], &[0, 1], 2);
        test_case(&[2], &[0, 1, 1], 4);
        test_case(&[2], &[0, 1, 2], 4);
        test_case(&[2], &[0, 2], 2);
        test_case(&[2], &[0, 2, 1], 4);
        test_case(&[2], &[0, 2, 2], 4);
        test_case(&[2], &[1], 1);
        test_case(&[2], &[1, 0, 1], 4);
        test_case(&[2], &[1, 0, 2], 4);
        test_case(&[2], &[1, 1], 2);
        test_case(&[2], &[1, 1, 1], 4);
        test_case(&[2], &[1, 1, 2], 4);
        test_case(&[2], &[1, 2], 2);
        test_case(&[2], &[1, 2, 1], 4);
        test_case(&[2], &[1, 2, 2], 4);
        test_case(&[2], &[2], 1);
        test_case(&[2], &[2, 0, 1], 4);
        test_case(&[2], &[2, 0, 2], 4);
        test_case(&[2], &[2, 1], 2);
        test_case(&[2], &[2, 1, 1], 4);
        test_case(&[2], &[2, 1, 2], 4);
        test_case(&[2], &[2, 2], 2);
        test_case(&[2], &[2, 2, 1], 4);
        test_case(&[2], &[2, 2, 2], 4);
        test_case(&[2, 0, 1], &[], 0);
        test_case(&[2, 0, 1], &[0, 0, 1], 4);
        test_case(&[2, 0, 1], &[0, 0, 2], 16);
        test_case(&[2, 0, 1], &[0, 1], 2);
        test_case(&[2, 0, 1], &[0, 1, 1], 6);
        test_case(&[2, 0, 1], &[0, 1, 2], 18);
        test_case(&[2, 0, 1], &[0, 2], 8);
        test_case(&[2, 0, 1], &[0, 2, 1], 12);
        test_case(&[2, 0, 1], &[0, 2, 2], 24);
        test_case(&[2, 0, 1], &[1], 1);
        test_case(&[2, 0, 1], &[1, 0, 1], 1);
        test_case(&[2, 0, 1], &[1, 0, 2], 9);
        test_case(&[2, 0, 1], &[1, 1], 3);
        test_case(&[2, 0, 1], &[1, 1, 1], 3);
        test_case(&[2, 0, 1], &[1, 1, 2], 11);
        test_case(&[2, 0, 1], &[1, 2], 9);
        test_case(&[2, 0, 1], &[1, 2, 1], 9);
        test_case(&[2, 0, 1], &[1, 2, 2], 17);
        test_case(&[2, 0, 1], &[2], 4);
        test_case(&[2, 0, 1], &[2, 0, 1], 0);
        test_case(&[2, 0, 1], &[2, 0, 2], 4);
        test_case(&[2, 0, 1], &[2, 1], 6);
        test_case(&[2, 0, 1], &[2, 1, 1], 2);
        test_case(&[2, 0, 1], &[2, 1, 2], 6);
        test_case(&[2, 0, 1], &[2, 2], 12);
        test_case(&[2, 0, 1], &[2, 2, 1], 8);
        test_case(&[2, 0, 1], &[2, 2, 2], 12);
        test_case(&[2, 0, 2], &[], 0);
        test_case(&[2, 0, 2], &[0, 0, 1], 4);
        test_case(&[2, 0, 2], &[0, 0, 2], 16);
        test_case(&[2, 0, 2], &[0, 1], 2);
        test_case(&[2, 0, 2], &[0, 1, 1], 8);
        test_case(&[2, 0, 2], &[0, 1, 2], 20);
        test_case(&[2, 0, 2], &[0, 2], 8);
        test_case(&[2, 0, 2], &[0, 2, 1], 20);
        test_case(&[2, 0, 2], &[0, 2, 2], 32);
        test_case(&[2, 0, 2], &[1], 1);
        test_case(&[2, 0, 2], &[1, 0, 1], 0);
        test_case(&[2, 0, 2], &[1, 0, 2], 4);
        test_case(&[2, 0, 2], &[1, 1], 4);
        test_case(&[2, 0, 2], &[1, 1, 1], 4);
        test_case(&[2, 0, 2], &[1, 1, 2], 8);
        test_case(&[2, 0, 2], &[1, 2], 10);
        test_case(&[2, 0, 2], &[1, 2, 1], 16);
        test_case(&[2, 0, 2], &[1, 2, 2], 20);
        test_case(&[2, 0, 2], &[2], 4);
        test_case(&[2, 0, 2], &[2, 0, 1], 4);
        test_case(&[2, 0, 2], &[2, 0, 2], 0);
        test_case(&[2, 0, 2], &[2, 1], 10);
        test_case(&[2, 0, 2], &[2, 1, 1], 8);
        test_case(&[2, 0, 2], &[2, 1, 2], 4);
        test_case(&[2, 0, 2], &[2, 2], 16);
        test_case(&[2, 0, 2], &[2, 2, 1], 20);
        test_case(&[2, 0, 2], &[2, 2, 2], 16);
        test_case(&[2, 1], &[], 0);
        test_case(&[2, 1], &[0, 0, 1], 4);
        test_case(&[2, 1], &[0, 0, 2], 8);
        test_case(&[2, 1], &[0, 1], -2);
        test_case(&[2, 1], &[0, 1, 1], 2);
        test_case(&[2, 1], &[0, 1, 2], 6);
        test_case(&[2, 1], &[0, 2], -4);
        test_case(&[2, 1], &[0, 2, 1], 0);
        test_case(&[2, 1], &[0, 2, 2], 4);
        test_case(&[2, 1], &[1], 1);
        test_case(&[2, 1], &[1, 0, 1], 5);
        test_case(&[2, 1], &[1, 0, 2], 9);
        test_case(&[2, 1], &[1, 1], -1);
        test_case(&[2, 1], &[1, 1, 1], 3);
        test_case(&[2, 1], &[1, 1, 2], 7);
        test_case(&[2, 1], &[1, 2], -3);
        test_case(&[2, 1], &[1, 2, 1], 1);
        test_case(&[2, 1], &[1, 2, 2], 5);
        test_case(&[2, 1], &[2], 2);
        test_case(&[2, 1], &[2, 0, 1], 6);
        test_case(&[2, 1], &[2, 0, 2], 10);
        test_case(&[2, 1], &[2, 1], 0);
        test_case(&[2, 1], &[2, 1, 1], 4);
        test_case(&[2, 1], &[2, 1, 2], 8);
        test_case(&[2, 1], &[2, 2], -2);
        test_case(&[2, 1], &[2, 2, 1], 2);
        test_case(&[2, 1], &[2, 2, 2], 6);
        test_case(&[2, 1, 1], &[], 0);
        test_case(&[2, 1, 1], &[0, 0, 1], 4);
        test_case(&[2, 1, 1], &[0, 0, 2], 16);
        test_case(&[2, 1, 1], &[0, 1], 2);
        test_case(&[2, 1, 1], &[0, 1, 1], 4);
        test_case(&[2, 1, 1], &[0, 1, 2], 14);
        test_case(&[2, 1, 1], &[0, 2], 8);
        test_case(&[2, 1, 1], &[0, 2, 1], 8);
        test_case(&[2, 1, 1], &[0, 2, 2], 16);
        test_case(&[2, 1, 1], &[1], 1);
        test_case(&[2, 1, 1], &[1, 0, 1], 2);
        test_case(&[2, 1, 1], &[1, 0, 2], 11);
        test_case(&[2, 1, 1], &[1, 1], 2);
        test_case(&[2, 1, 1], &[1, 1, 1], 1);
        test_case(&[2, 1, 1], &[1, 1, 2], 8);
        test_case(&[2, 1, 1], &[1, 2], 7);
        test_case(&[2, 1, 1], &[1, 2, 1], 4);
        test_case(&[2, 1, 1], &[1, 2, 2], 9);
        test_case(&[2, 1, 1], &[2], 4);
        test_case(&[2, 1, 1], &[2, 0, 1], 2);
        test_case(&[2, 1, 1], &[2, 0, 2], 8);
        test_case(&[2, 1, 1], &[2, 1], 4);
        test_case(&[2, 1, 1], &[2, 1, 1], 0);
        test_case(&[2, 1, 1], &[2, 1, 2], 4);
        test_case(&[2, 1, 1], &[2, 2], 8);
        test_case(&[2, 1, 1], &[2, 2, 1], 2);
        test_case(&[2, 1, 1], &[2, 2, 2], 4);
        test_case(&[2, 1, 2], &[], 0);
        test_case(&[2, 1, 2], &[0, 0, 1], 4);
        test_case(&[2, 1, 2], &[0, 0, 2], 16);
        test_case(&[2, 1, 2], &[0, 1], 2);
        test_case(&[2, 1, 2], &[0, 1, 1], 6);
        test_case(&[2, 1, 2], &[0, 1, 2], 16);
        test_case(&[2, 1, 2], &[0, 2], 8);
        test_case(&[2, 1, 2], &[0, 2, 1], 16);
        test_case(&[2, 1, 2], &[0, 2, 2], 24);
        test_case(&[2, 1, 2], &[1], 1);
        test_case(&[2, 1, 2], &[1, 0, 1], 1);
        test_case(&[2, 1, 2], &[1, 0, 2], 6);
        test_case(&[2, 1, 2], &[1, 1], 3);
        test_case(&[2, 1, 2], &[1, 1, 1], 1);
        test_case(&[2, 1, 2], &[1, 1, 2], 4);
        test_case(&[2, 1, 2], &[1, 2], 8);
        test_case(&[2, 1, 2], &[1, 2, 1], 9);
        test_case(&[2, 1, 2], &[1, 2, 2], 10);
        test_case(&[2, 1, 2], &[2], 4);
        test_case(&[2, 1, 2], &[2, 0, 1], 6);
        test_case(&[2, 1, 2], &[2, 0, 2], 4);
        test_case(&[2, 1, 2], &[2, 1], 8);
        test_case(&[2, 1, 2], &[2, 1, 1], 4);
        test_case(&[2, 1, 2], &[2, 1, 2], 0);
        test_case(&[2, 1, 2], &[2, 2], 12);
        test_case(&[2, 1, 2], &[2, 2, 1], 10);
        test_case(&[2, 1, 2], &[2, 2, 2], 4);
        test_case(&[2, 2], &[], 0);
        test_case(&[2, 2], &[0, 0, 1], 4);
        test_case(&[2, 2], &[0, 0, 2], 8);
        test_case(&[2, 2], &[0, 1], -2);
        test_case(&[2, 2], &[0, 1, 1], 0);
        test_case(&[2, 2], &[0, 1, 2], 4);
        test_case(&[2, 2], &[0, 2], -4);
        test_case(&[2, 2], &[0, 2, 1], -4);
        test_case(&[2, 2], &[0, 2, 2], 0);
        test_case(&[2, 2], &[1], 1);
        test_case(&[2, 2], &[1, 0, 1], 8);
        test_case(&[2, 2], &[1, 0, 2], 12);
        test_case(&[2, 2], &[1, 1], 0);
        test_case(&[2, 2], &[1, 1, 1], 4);
        test_case(&[2, 2], &[1, 1, 2], 8);
        test_case(&[2, 2], &[1, 2], -2);
        test_case(&[2, 2], &[1, 2, 1], 0);
        test_case(&[2, 2], &[1, 2, 2], 4);
        test_case(&[2, 2], &[2], 2);
        test_case(&[2, 2], &[2, 0, 1], 12);
        test_case(&[2, 2], &[2, 0, 2], 16);
        test_case(&[2, 2], &[2, 1], 2);
        test_case(&[2, 2], &[2, 1, 1], 8);
        test_case(&[2, 2], &[2, 1, 2], 12);
        test_case(&[2, 2], &[2, 2], 0);
        test_case(&[2, 2], &[2, 2, 1], 4);
        test_case(&[2, 2], &[2, 2, 2], 8);
        test_case(&[2, 2, 1], &[], 0);
        test_case(&[2, 2, 1], &[0, 0, 1], 4);
        test_case(&[2, 2, 1], &[0, 0, 2], 16);
        test_case(&[2, 2, 1], &[0, 1], 2);
        test_case(&[2, 2, 1], &[0, 1, 1], 2);
        test_case(&[2, 2, 1], &[0, 1, 2], 10);
        test_case(&[2, 2, 1], &[0, 2], 8);
        test_case(&[2, 2, 1], &[0, 2, 1], 4);
        test_case(&[2, 2, 1], &[0, 2, 2], 8);
        test_case(&[2, 2, 1], &[1], 1);
        test_case(&[2, 2, 1], &[1, 0, 1], 5);
        test_case(&[2, 2, 1], &[1, 0, 2], 17);
        test_case(&[2, 2, 1], &[1, 1], 1);
        test_case(&[2, 2, 1], &[1, 1, 1], 1);
        test_case(&[2, 2, 1], &[1, 1, 2], 9);
        test_case(&[2, 2, 1], &[1, 2], 5);
        test_case(&[2, 2, 1], &[1, 2, 1], 1);
        test_case(&[2, 2, 1], &[1, 2, 2], 5);
        test_case(&[2, 2, 1], &[2], 4);
        test_case(&[2, 2, 1], &[2, 0, 1], 8);
        test_case(&[2, 2, 1], &[2, 0, 2], 20);
        test_case(&[2, 2, 1], &[2, 1], 2);
        test_case(&[2, 2, 1], &[2, 1, 1], 2);
        test_case(&[2, 2, 1], &[2, 1, 2], 10);
        test_case(&[2, 2, 1], &[2, 2], 4);
        test_case(&[2, 2, 1], &[2, 2, 1], 0);
        test_case(&[2, 2, 1], &[2, 2, 2], 4);
        test_case(&[2, 2, 2], &[], 0);
        test_case(&[2, 2, 2], &[0, 0, 1], 4);
        test_case(&[2, 2, 2], &[0, 0, 2], 16);
        test_case(&[2, 2, 2], &[0, 1], 2);
        test_case(&[2, 2, 2], &[0, 1, 1], 4);
        test_case(&[2, 2, 2], &[0, 1, 2], 12);
        test_case(&[2, 2, 2], &[0, 2], 8);
        test_case(&[2, 2, 2], &[0, 2, 1], 12);
        test_case(&[2, 2, 2], &[0, 2, 2], 16);
        test_case(&[2, 2, 2], &[1], 1);
        test_case(&[2, 2, 2], &[1, 0, 1], 4);
        test_case(&[2, 2, 2], &[1, 0, 2], 12);
        test_case(&[2, 2, 2], &[1, 1], 2);
        test_case(&[2, 2, 2], &[1, 1, 1], 0);
        test_case(&[2, 2, 2], &[1, 1, 2], 4);
        test_case(&[2, 2, 2], &[1, 2], 6);
        test_case(&[2, 2, 2], &[1, 2, 1], 4);
        test_case(&[2, 2, 2], &[1, 2, 2], 4);
        test_case(&[2, 2, 2], &[2], 4);
        test_case(&[2, 2, 2], &[2, 0, 1], 12);
        test_case(&[2, 2, 2], &[2, 0, 2], 16);
        test_case(&[2, 2, 2], &[2, 1], 6);
        test_case(&[2, 2, 2], &[2, 1, 1], 4);
        test_case(&[2, 2, 2], &[2, 1, 2], 4);
        test_case(&[2, 2, 2], &[2, 2], 8);
        test_case(&[2, 2, 2], &[2, 2, 1], 4);
        test_case(&[2, 2, 2], &[2, 2, 2], 0);
    }

    #[test]
    fn test_multivariable_resultant() {
        let bi = |v: i64| BigInt::from(v);
        let lhs: Polynomial<Polynomial<BigInt>> =
            vec![bi(-2).into(), bi(0).into(), bi(1).into()].into();
        let rhs: Polynomial<Polynomial<BigInt>> = vec![
            vec![bi(-2), bi(0), bi(1)].into(),
            vec![bi(0), bi(-2)].into(),
            bi(1).into(),
        ]
        .into();
        let expected: Polynomial<BigInt> = vec![bi(0), bi(0), bi(-8), bi(0), bi(1)].into();
        println!("lhs = {}", lhs);
        println!("rhs = {}", rhs);
        println!("expected = {}", expected);
        let resultant = lhs.resultant(rhs);
        println!("resultant = {}", resultant);
        assert!(expected == resultant);
    }
}
