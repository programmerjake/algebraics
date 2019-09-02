// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use crate::polynomial::PolynomialDivSupported;
use crate::polynomial::PolynomialReducingFactorSupported;
use crate::polynomial::PseudoDivRem;
use crate::traits::ExactDiv;
use crate::traits::ExactDivAssign;
use crate::traits::ExtendedGCD;
use crate::traits::ExtendedGCDAndLCM;
use crate::traits::ExtendedGCDResult;
use crate::traits::GCDAndLCM;
use crate::traits::GCD;
use num_traits::Zero;
use std::fmt;

impl<T> GCD for Polynomial<T>
where
    T: PolynomialCoefficient + PolynomialDivSupported + PolynomialReducingFactorSupported,
{
    type Output = Self;
    fn gcd(&self, rhs: &Self) -> Self {
        let mut l = self.to_reduced();
        let mut r = rhs.to_reduced();
        if l.is_zero() {
            return r;
        }
        while !r.is_zero() {
            let PseudoDivRem { remainder, .. } = l.pseudo_div_rem(&r);
            l = r;
            r = remainder.into_reduced();
        }
        l
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
    // FIXME: remove
    T: fmt::Display,
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
        macro_rules! validate_state {
            ($state:ident) => {
                dbg!();
                println!("{}.v: ({})", stringify!($state), $state.v);
                println!("{}.x: ({})", stringify!($state), $state.x);
                println!("{}.y: ({})", stringify!($state), $state.y);
                let product = &$state.x * lhs + &$state.y * rhs;
                println!("lhs: ({})", lhs);
                println!("rhs: ({})", rhs);
                println!("product: ({})", product);
                assert!($state.v == product);
            };
        }
        let mut lhs_state = StateSet {
            v: lhs.exact_div(&lhs_reducing_factor),
            x: lhs
                .to_one_if_nonzero()
                .expect("known to be nonzero")
                .exact_div(lhs_reducing_factor),
            y: Self::zero(),
        };
        validate_state!(lhs_state);
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
        validate_state!(rhs_state);

        while !rhs_state.v.is_zero() {
            let (quotient, remainder) = lhs_state.v.clone().div_rem(&rhs_state.v);
            println!("quotient = ({})", quotient);
            println!("remainder = ({})", remainder);
            assert!(&lhs_state.v - &rhs_state.v * &quotient == remainder);
            let mut new_state = StateSet {
                v: &lhs_state.v - &rhs_state.v * &quotient, // TODO: switch back to remainder
                x: dbg!(&lhs_state.x - dbg!(&rhs_state.x * &quotient)),
                y: &lhs_state.y - &rhs_state.y * &quotient,
            };
            validate_state!(new_state);
            if let Some(reducing_factor) = new_state.v.nonzero_reducing_factor() {
                new_state.v.exact_div_assign(&reducing_factor);
                new_state.x.exact_div_assign(&reducing_factor);
                new_state.y.exact_div_assign(reducing_factor);
            }
            validate_state!(new_state);
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
}
