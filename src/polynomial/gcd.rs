// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::polynomial::Polynomial;
use crate::polynomial::PolynomialCoefficient;
use crate::polynomial::PolynomialDivSupported;
use crate::polynomial::PolynomialReducingFactorSupported;
use crate::polynomial::PseudoDivRem;
use crate::traits::ExactDiv;
use crate::traits::GCDAndLCM;
use crate::traits::GCD;
use num_traits::Zero;

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
            println!("a=({})  b=({})", a, b);
            println!("gcd=({})  lcm=({})", gcd, lcm);
            println!(
                "results.gcd=({})  results.lcm=({})",
                results.gcd, results.lcm
            );
            // don't use assert_eq because the debug output is awful
            assert!(gcd == results.gcd);
            assert!(lcm == results.lcm);
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
