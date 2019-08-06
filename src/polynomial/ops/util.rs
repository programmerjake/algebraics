// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

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
