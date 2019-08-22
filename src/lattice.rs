// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

use std::ops::AddAssign;
use num_traits::Zero;
use crate::array2d::Array2DOwned;
use crate::array2d::Array2DSlice;
use num_bigint::BigInt;
use std::ops::Add;
use std::ops::Div;
use std::ops::Mul;
use std::ops::Sub;

pub fn inner_product<'a, T>(
    a: Array2DSlice<'a, T>,
    b: Array2DSlice<'a, T>,
) -> T
where
    T:Zero+AddAssign,
    for<'l, 'r> &'l T: Mul<&'r T, Output=T>,
{
    assert_eq!(a.size(), b.size());
    let mut retval = Zero::zero();
    for (a, b) in a.into_iter().zip(b) {
        retval += a * b;
    }
    retval
}

pub fn gram_schmidt<
    T: Clone + Add<Output = T> + Mul<Output = T> + Sub<Output = T> + Div<Output = T>,
>(
    mut basis: Array2DOwned<T>,
) -> Array2DOwned<T> {
    for i in 0..basis.x_size() {
        for j in 0..i {}
    }
    unimplemented!()
}

#[allow(dead_code)]
fn allow_dead_code() {
    let _ = gram_schmidt::<i32>;
    let _ = gram_schmidt::<BigInt>;
}
