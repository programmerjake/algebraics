// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

// FIXME: remove when module made public again
#![allow(dead_code)]

use crate::array2d::{Array2DOwned, Array2DSlice};
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::{FromPrimitive, NumAssign, NumRef, Signed, Zero};
use std::{
    cmp::Ordering,
    ops::{Add, Mul, RangeTo},
};

pub(crate) fn inner_product<'a, L, R, T>(a: Array2DSlice<'a, L>, b: Array2DSlice<'a, R>) -> T
where
    T: Zero + Add<Output = T>,
    for<'l, 'r> &'l L: Mul<&'r R, Output = T>,
{
    assert_eq!(a.size(), b.size());
    let mut retval = None;
    for (a, b) in a.into_iter().zip(b) {
        let product = a * b;
        retval = Some(match retval {
            None => product,
            Some(v) => v + product,
        });
    }
    retval.unwrap_or_else(Zero::zero)
}

pub(crate) fn gram_schmidt_calculate_column<T>(
    input_basis: Array2DSlice<T>,
    basis: &mut Array2DOwned<Ratio<T>>,
    column: usize,
) where
    T: Clone + Integer + NumAssign,
{
    assert_eq!(input_basis.size(), basis.size());
    assert!(column < basis.x_size());
    for y in 0..basis.y_size() {
        basis[(column, y)] = Ratio::from_integer(input_basis[(column, y)].clone());
    }
    for j in 0..column {
        let n = inner_product(basis.slice(column, ..), input_basis.slice(j, ..));
        let d = inner_product(basis.slice(j, ..), basis.slice(j, ..));
        if d.is_zero() {
            assert!(n.is_zero());
            continue;
        }
        let factor = n / d;
        for y in 0..basis.y_size() {
            let v = &basis[(j, y)] * &factor;
            basis[(column, y)] -= v;
        }
    }
}

pub(crate) fn gram_schmidt<T>(input_basis: Array2DSlice<T>) -> Array2DOwned<Ratio<T>>
where
    T: Clone + Integer + NumAssign,
{
    let mut basis = Array2DOwned::new_with(input_basis.x_size(), input_basis.y_size(), Zero::zero);
    for i in 0..basis.x_size() {
        gram_schmidt_calculate_column(input_basis, &mut basis, i);
    }
    basis
}

struct LLLState<T> {
    basis: Array2DOwned<T>,
    orthogonal_basis: Array2DOwned<Ratio<T>>,
    orthogonal_basis_valid_columns: RangeTo<usize>,
}

impl<T> LLLState<T>
where
    T: Clone + Integer + NumAssign,
{
    fn new(basis: Array2DOwned<T>) -> Self {
        LLLState {
            orthogonal_basis: Array2DOwned::new_with(basis.x_size(), basis.y_size(), Zero::zero),
            basis,
            orthogonal_basis_valid_columns: ..0,
        }
    }
    fn invalidate_column(&mut self, column: usize) {
        self.orthogonal_basis_valid_columns =
            ..(self.orthogonal_basis_valid_columns.end.min(column));
    }
    fn calculate_column(&mut self, column: usize) {
        while !self.orthogonal_basis_valid_columns.contains(&column) {
            gram_schmidt_calculate_column(
                self.basis.slice(.., ..),
                &mut self.orthogonal_basis,
                self.orthogonal_basis_valid_columns.end,
            );
            self.orthogonal_basis_valid_columns.end += 1;
        }
    }
    fn mu(&mut self, i: usize, j: usize) -> Ratio<T> {
        self.calculate_column(j);
        inner_product(self.orthogonal_basis.slice(j, ..), self.basis.slice(i, ..))
            / inner_product(
                self.orthogonal_basis.slice(j, ..),
                self.orthogonal_basis.slice(j, ..),
            )
    }
}

pub(crate) fn lll_reduce_with_delta<T>(basis: Array2DOwned<T>, delta: Ratio<T>) -> Array2DOwned<T>
where
    T: Clone + Integer + NumAssign + NumRef + FromPrimitive + Signed,
{
    // algorithm from https://en.wikipedia.org/wiki/Lenstra–Lenstra–Lovász_lattice_basis_reduction_algorithm#LLL_algorithm

    let one_half = Ratio::new(T::one(), T::from_i32(2).expect("can't convert 2 to T"));
    let mut state = LLLState::new(basis);
    let mut k = 1;
    while k < state.basis.x_size() {
        for j in (0..k).rev() {
            let mu_k_j = state.mu(k, j);
            if mu_k_j.clone().abs() > one_half {
                let mut rounded_mu_k_j = mu_k_j.clone().floor().to_integer();
                match (mu_k_j - rounded_mu_k_j.clone()).cmp(&one_half) {
                    Ordering::Equal => {
                        if rounded_mu_k_j.is_odd() {
                            rounded_mu_k_j += T::one();
                        }
                    }
                    Ordering::Greater => rounded_mu_k_j += T::one(),
                    Ordering::Less => {}
                }
                state.invalidate_column(k);
                for y in 0..state.basis.y_size() {
                    let v = state.basis[(j, y)].clone() * &rounded_mu_k_j;
                    state.basis[(k, y)] -= v;
                }
            }
        }
        let mu_k_km1 = state.mu(k, k - 1);
        state.calculate_column(k - 1);
        let km1_inner_product = inner_product(
            state.orthogonal_basis.slice(k - 1, ..),
            state.orthogonal_basis.slice(k - 1, ..),
        );
        state.calculate_column(k);
        let k_inner_product = inner_product(
            state.orthogonal_basis.slice(k, ..),
            state.orthogonal_basis.slice(k, ..),
        );
        if k_inner_product >= (delta.clone() - mu_k_km1.clone() * mu_k_km1) * km1_inner_product {
            k += 1;
        } else {
            state.invalidate_column(k);
            state.invalidate_column(k - 1);
            for y in 0..state.basis.y_size() {
                state.basis.swap_elements((k, y), (k - 1, y));
            }
            k = 1.max(k - 1);
        }
    }
    state.basis
}

pub(crate) fn lll_reduce<T>(basis: Array2DOwned<T>) -> Array2DOwned<T>
where
    T: Clone + Integer + NumAssign + NumRef + FromPrimitive + Signed,
{
    lll_reduce_with_delta(
        basis,
        Ratio::new(
            T::from_i32(3).expect("can't convert 3 to T"),
            T::from_i32(4).expect("can't convert 4 to T"),
        ),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;
    use num_traits::{One, Pow};

    #[test]
    fn test_gram_schmidt() {
        let i = |v: i64| BigInt::from(v);
        let r = |n: i64, d: i64| Ratio::<BigInt>::new(n.into(), d.into());

        let input = Array2DOwned::from_array(
            3,
            4,
            vec![
                i(1),
                i(2),
                i(3),
                i(4),
                i(23),
                i(34),
                i(456),
                i(0),
                i(23),
                i(36),
                i(15),
                i(2),
            ],
        );
        println!("input:\n{:#}", input);
        let expected = Array2DOwned::from_array(
            3,
            4,
            vec![
                r(1, 1),
                r(2, 1),
                r(3, 1),
                r(4, 1),
                r(-769, 30),
                r(-949, 15),
                r(3101, 10),
                r(-2918, 15),
                r(76_229_372, 4_159_949),
                r(111_361_550, 4_159_949),
                r(-12_148_176, 4_159_949),
                r(-65_626_986, 4_159_949),
            ],
        );
        println!("expected:\n{:#}", expected);
        let output = gram_schmidt(input.slice(.., ..));
        println!("output:\n{:#}", output);
        assert!(output == expected);

        let input = Array2DOwned::from_array(
            4,
            4,
            vec![
                i(-243),
                i(-234),
                i(-2),
                i(-5),
                i(235),
                i(2),
                i(4),
                i(6),
                i(0),
                i(36),
                i(-5),
                i(2),
                i(1),
                i(-1),
                i(1),
                i(-1),
            ],
        );
        println!("input:\n{:#}", input);
        let expected = Array2DOwned::from_array(
            4,
            4,
            vec![
                r(-243, 1),
                r(-234, 1),
                r(-2, 1),
                r(-5, 1),
                r(12_751_517, 113_834),
                r(-6_626_653, 56917),
                r(170_057, 56917),
                r(394_949, 113_834),
                r(70_966_960, 2_973_830_033),
                r(-94_068_796, 2_973_830_033),
                r(-13_881_031_493, 2_973_830_033),
                r(6_505_837_994, 2_973_830_033),
                r(1_249_570_482, 79_030_356_797),
                r(-353_698_923, 79_030_356_797),
                r(-2_489_783_076, 11_290_050_971),
                r(-1_958_138_064, 4_159_492_463),
            ],
        );
        println!("expected:\n{:#}", expected);
        let output = gram_schmidt(input.slice(.., ..));
        println!("output:\n{:#}", output);
        assert!(output == expected);
    }

    // workaround for https://github.com/rust-num/num-bigint/issues/106
    fn pow<'a, T>(base: &'a Ratio<BigInt>, exponent: &'a T) -> Ratio<BigInt>
    where
        &'a BigInt: Pow<&'a T, Output = BigInt>,
    {
        let numer = base.numer().pow(exponent);
        let denom = base.denom().pow(exponent);
        Ratio::new(numer, denom)
    }

    #[test]
    fn test_lll_reduce() {
        let ints = |v: &[i64]| -> Vec<BigInt> { v.iter().copied().map(BigInt::from).collect() };

        let input = Array2DOwned::from_array(
            4,
            4,
            ints(&[1, 99, 91, 8, 12, 91, 87, 85, 69, 74, 96, 31, 56, 35, 13, 60]),
        );
        println!("input:\n{:#}", input);
        let expected = Array2DOwned::from_array(
            4,
            4,
            ints(&[
                11, -8, -4, 77, 68, -25, 5, 23, 45, 43, 17, -17, -32, -4, 66, -12,
            ]),
        );
        println!("expected:\n{:#}", expected);
        let output = lll_reduce(input);
        println!("output:\n{:#}", output);
        assert!(output == expected);

        let input =
            Array2DOwned::from_array(3, 3, ints(&[27, 301, 408, 926, 155, 210, 814, 336, 94]));
        println!("input:\n{:#}", input);
        let expected =
            Array2DOwned::from_array(3, 3, ints(&[-112, 181, -116, 27, 301, 408, 675, 216, -430]));
        println!("expected:\n{:#}", expected);
        let output = lll_reduce(input);
        println!("output:\n{:#}", output);
        assert!(output == expected);

        // find the minimal polynomial of sin(pi / 7)
        let multiplier = BigInt::from(1) << 48;
        // approximation to 1024 fractional bits
        let sin_pi_7_approximation: Ratio<BigInt> =
            "97498727392503287796421964844598099607650972550809391824625445149289352\
             685085470974709559364481363509368111361275396392010311843690916990724483522132\
             640931028212023467353916861241362846244259728556581827622758966595936283678031\
             989009141225359110201687206674081123626214905851516178176527528516219901977479\
             11\
             /\
             224711641857789488466163148848628091702247122367788321591787601447165844756\
             876203915885596653009420026400142349839241697073487211018020778116059288299342\
             655472209866781081856595377774501557617649316353690106257211047688352928078601\
             84239138817603404645418813835573287279993405742309964538104419541203028017152"
                .parse()
                .unwrap();
        let degree = 7;
        let input = Array2DOwned::new_with_positions(degree, degree + 1, |x, y| {
            if y < degree {
                if x == y {
                    BigInt::one()
                } else {
                    BigInt::zero()
                }
            } else {
                -pow(&sin_pi_7_approximation, &x)
                    .mul(&multiplier)
                    .round()
                    .to_integer()
            }
        });
        println!("input:\n{:#}", input);
        let expected = Array2DOwned::from_array(
            7,
            8,
            ints(&[
                5, -5, 1, -40, -1, 51, -75, -11, //
                -20, 41, 44, -31, -57, -98, -2, 8, //
                3, 49, -106, -45, -8, -16, -15, 2, //
                //
                // basis vector with the minimal polynomial:
                // -7 + 56*x^2 - 112*x^4 + 64*x^6
                7, 0, -56, 0, 112, 0, -64, 40, //
                -17, 26, 3, 89, -28, -47, -60, 10, //
                -6, 20, -12, 11, -6, -51, -48, -103, //
                -55, 94, 71, -19, 65, -8, 33, -33, //
            ]),
        );
        println!("expected:\n{:#}", expected);
        let output = lll_reduce(input);
        println!("output:\n{:#}", output);
        assert!(output == expected);
    }
}
