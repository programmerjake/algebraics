// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
use crate::polynomial::Polynomial;
use num_traits::Zero;

pub(crate) fn pairwise_op_ref_ref<
    'l,
    'r,
    L,
    R,
    O: Zero,
    Op: FnMut(&'l L, &'r R) -> O,
    OpL: FnMut(&'l L) -> O,
    OpR: FnMut(&'r R) -> O,
>(
    l: &'l Polynomial<L>,
    r: &'r Polynomial<R>,
    mut op: Op,
    mut op_l: OpL,
    mut op_r: OpR,
) -> Polynomial<O> {
    let mut coefficients = Vec::with_capacity(l.len().max(r.len()));
    let mut l_iter = l.iter();
    let mut r_iter = r.iter();
    loop {
        match (l_iter.next(), r_iter.next()) {
            (Some(l), Some(r)) => coefficients.push(op(l, r)),
            (Some(l), None) => coefficients.push(op_l(l)),
            (None, Some(r)) => coefficients.push(op_r(r)),
            (None, None) => break,
        }
    }
    coefficients.into()
}

pub(crate) fn pairwise_op_eq_move<
    L: Zero,
    R,
    Op: FnMut(&mut L, R),
    OpL: FnMut(&mut L),
    OpR: FnMut(R) -> L,
>(
    l: &mut Polynomial<L>,
    r: Polynomial<R>,
    mut op: Op,
    mut op_l: OpL,
    op_r: OpR,
) {
    let mut r_iter = r.into_iter();
    for l in l.coefficients.iter_mut() {
        match r_iter.next() {
            Some(r) => op(l, r),
            None => op_l(l),
        }
    }
    l.coefficients.extend(r_iter.map(op_r));
    l.remove_extra_zeros()
}

pub(crate) fn pairwise_op_eq_ref<
    'r,
    L: Zero,
    R,
    Op: FnMut(&mut L, &'r R),
    OpL: FnMut(&mut L),
    OpR: FnMut(&'r R) -> L,
>(
    l: &mut Polynomial<L>,
    r: &'r Polynomial<R>,
    mut op: Op,
    mut op_l: OpL,
    op_r: OpR,
) {
    let mut r_iter = r.into_iter();
    for l in l.iter_mut() {
        match r_iter.next() {
            Some(r) => op(l, r),
            None => op_l(l),
        }
    }
    l.coefficients.extend(r_iter.map(op_r));
    l.remove_extra_zeros()
}

#[cfg(test)]
pub(crate) mod tests {
    use std::fmt::Debug;

    #[allow(clippy::too_many_arguments)]
    pub(crate) fn test_op_helper<
        T: Clone + PartialEq + Debug,
        OpEqMove: Fn(&mut T, T),
        OpEqRef: Fn(&mut T, &T),
        OpRefRef: Fn(&T, &T) -> T,
        OpMoveRef: Fn(T, &T) -> T,
        OpRefMove: Fn(&T, T) -> T,
        OpMoveMove: Fn(T, T) -> T,
    >(
        l: T,
        r: T,
        expected: &T,
        op_eq_move: OpEqMove,
        op_eq_ref: OpEqRef,
        op_ref_ref: OpRefRef,
        op_move_ref: OpMoveRef,
        op_ref_move: OpRefMove,
        op_move_move: OpMoveMove,
    ) {
        let mut eq_move_result = l.clone();
        op_eq_move(&mut eq_move_result, r.clone());
        assert_eq!(eq_move_result, *expected);
        let mut eq_ref_result = l.clone();
        op_eq_ref(&mut eq_ref_result, &r);
        assert_eq!(eq_ref_result, *expected);
        assert_eq!(op_ref_ref(&l, &r), *expected);
        assert_eq!(op_ref_move(&l, r.clone()), *expected);
        assert_eq!(op_move_ref(l.clone(), &r), *expected);
        assert_eq!(op_move_move(l, r), *expected);
    }
}
