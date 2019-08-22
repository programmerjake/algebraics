// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use crate::array2d::Array2DOwned;
use crate::array2d::Array2DSlice;
use num_integer::Integer;
use num_rational::Ratio;
use num_traits::FromPrimitive;
use num_traits::NumAssign;
use num_traits::NumRef;
use num_traits::Signed;
use num_traits::Zero;
use std::cmp::Ordering;
use std::ops::Add;
use std::ops::Mul;

pub fn inner_product<'a, L, R, T>(a: Array2DSlice<'a, L>, b: Array2DSlice<'a, R>) -> T
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

pub fn gram_schmidt<T>(input_basis: Array2DSlice<T>) -> Array2DOwned<Ratio<T>>
where
    T: Clone + Integer + NumAssign,
{
    let mut basis =
        Array2DOwned::new_with_positions(input_basis.x_size(), input_basis.y_size(), |x, y| {
            Ratio::from_integer(input_basis[(x, y)].clone())
        });
    for i in 0..basis.x_size() {
        for j in 0..i {
            let n = inner_product(basis.slice(i, ..), input_basis.slice(j, ..));
            let d = inner_product(basis.slice(j, ..), basis.slice(j, ..));
            if d.is_zero() {
                assert!(n.is_zero());
                continue;
            }
            let factor = n / d;
            for y in 0..basis.y_size() {
                let v = &basis[(j, y)] * &factor;
                basis[(i, y)] -= v;
            }
        }
    }
    basis
}

pub fn lll_reduce_with_delta<T>(mut basis: Array2DOwned<T>, delta: Ratio<T>) -> Array2DOwned<T>
where
    T: Clone + Integer + NumAssign + NumRef + FromPrimitive + Signed,
{
    // algorithm from https://en.wikipedia.org/wiki/Lenstra–Lenstra–Lovász_lattice_basis_reduction_algorithm#LLL_algorithm

    let one_half = Ratio::new(T::one(), T::from_i32(2).expect("can't convert 2 to T"));
    let mut orthogonal_basis = gram_schmidt(basis.slice(.., ..));
    let mu =
        |i: usize, j: usize, basis: &Array2DOwned<T>, orthogonal_basis: &Array2DOwned<Ratio<T>>| {
            inner_product(orthogonal_basis.slice(j, ..), basis.slice(i, ..))
                / inner_product(orthogonal_basis.slice(j, ..), orthogonal_basis.slice(j, ..))
        };
    let mut k = 1;
    while k < basis.x_size() {
        for j in (0..k).rev() {
            let mu_k_j = mu(k, j, &basis, &orthogonal_basis);
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
                for y in 0..basis.y_size() {
                    let v = basis[(j, y)].clone() * &rounded_mu_k_j;
                    basis[(k, y)] -= v;
                }
                orthogonal_basis = gram_schmidt(basis.slice(.., ..));
            }
            let mu_k_km1 = mu(k, k - 1, &basis, &orthogonal_basis);
            if inner_product(orthogonal_basis.slice(k, ..), orthogonal_basis.slice(k, ..))
                >= (delta.clone() - mu_k_km1.clone() * mu_k_km1)
                    * inner_product(
                        orthogonal_basis.slice(k - 1, ..),
                        orthogonal_basis.slice(k - 1, ..),
                    )
            {
                k += 1;
            } else {
                for y in 0..basis.y_size() {
                    basis.swap_elements((k, y), (k - 1, y));
                }
                orthogonal_basis = gram_schmidt(basis.slice(.., ..));
                k = 1.max(k - 1);
            }
        }
    }
    basis
}

pub fn lll_reduce<T>(basis: Array2DOwned<T>) -> Array2DOwned<T>
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
                11, -8, -4, 77, 68, -25, 5, 23, 45, 43, 17, -17, 1, 99, 91, 8,
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
    }
}
