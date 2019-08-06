// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information
pub mod polynomial;
pub mod prelude;
pub mod traits;
pub mod quadratic_numbers;
pub mod mod_int;

pub mod util {
    use num_traits::Zero;
    use std::cmp::Ordering;
    use std::ops::{BitAnd, BitAndAssign, BitOr, BitOrAssign, BitXor, BitXorAssign, Neg, Not};
    #[derive(Copy, Clone, Eq, PartialEq, Debug, Hash)]
    pub enum Sign {
        Negative,
        Positive,
    }

    impl Sign {
        pub fn new<T: PartialOrd + Zero>(v: &T) -> Option<Sign> {
            match v.partial_cmp(&Zero::zero()) {
                Some(Ordering::Less) => Some(Sign::Negative),
                Some(Ordering::Greater) => Some(Sign::Positive),
                _ => None,
            }
        }
    }

    impl Default for Sign {
        fn default() -> Sign {
            Sign::Positive
        }
    }

    impl Neg for Sign {
        type Output = Sign;
        fn neg(self) -> Sign {
            match self {
                Sign::Negative => Sign::Positive,
                Sign::Positive => Sign::Negative,
            }
        }
    }

    impl Neg for &'_ Sign {
        type Output = Sign;
        fn neg(self) -> Sign {
            -*self
        }
    }

    impl Not for Sign {
        type Output = Sign;
        fn not(self) -> Sign {
            -self
        }
    }

    impl Not for &'_ Sign {
        type Output = Sign;
        fn not(self) -> Sign {
            -self
        }
    }

    impl From<bool> for Sign {
        fn from(is_negative: bool) -> Sign {
            if is_negative {
                Sign::Negative
            } else {
                Sign::Positive
            }
        }
    }

    impl From<Sign> for bool {
        fn from(sign: Sign) -> bool {
            match sign {
                Sign::Negative => true,
                Sign::Positive => false,
            }
        }
    }

    macro_rules! impl_sign_op {
        ($trait_name:ident, $fn_name:ident) => {
            impl $trait_name<Sign> for Sign {
                type Output = Sign;
                fn $fn_name(self, rhs: Sign) -> Sign {
                    bool::from(self).$fn_name(bool::from(rhs)).into()
                }
            }

            impl $trait_name<Sign> for &'_ Sign {
                type Output = Sign;
                fn $fn_name(self, rhs: Sign) -> Sign {
                    bool::from(*self).$fn_name(bool::from(rhs)).into()
                }
            }

            impl $trait_name<&'_ Sign> for Sign {
                type Output = Sign;
                fn $fn_name(self, rhs: &Sign) -> Sign {
                    bool::from(self).$fn_name(bool::from(*rhs)).into()
                }
            }

            impl<'a, 'b> $trait_name<&'a Sign> for &'b Sign {
                type Output = Sign;
                fn $fn_name(self, rhs: &Sign) -> Sign {
                    bool::from(*self).$fn_name(bool::from(*rhs)).into()
                }
            }
        };
    }

    impl_sign_op!(BitAnd, bitand);
    impl_sign_op!(BitOr, bitor);
    impl_sign_op!(BitXor, bitxor);

    macro_rules! impl_sign_op_eq {
        ($trait_name:ident, $fn_name:ident) => {
            impl $trait_name<Sign> for Sign {
                fn $fn_name(&mut self, rhs: Sign) {
                    let mut l = bool::from(*self);
                    l.$fn_name(bool::from(rhs));
                    *self = l.into();
                }
            }

            impl $trait_name<&'_ Sign> for Sign {
                fn $fn_name(&mut self, rhs: &Sign) {
                    let mut l = bool::from(*self);
                    l.$fn_name(bool::from(*rhs));
                    *self = l.into();
                }
            }
        };
    }

    impl_sign_op_eq!(BitAndAssign, bitand_assign);
    impl_sign_op_eq!(BitOrAssign, bitor_assign);
    impl_sign_op_eq!(BitXorAssign, bitxor_assign);

    impl PartialOrd for Sign {
        fn partial_cmp(&self, rhs: &Sign) -> Option<Ordering> {
            Some(self.cmp(rhs))
        }
    }

    impl Ord for Sign {
        fn cmp(&self, rhs: &Sign) -> Ordering {
            match (self, rhs) {
                (Sign::Positive, Sign::Negative) => Ordering::Greater,
                (Sign::Negative, Sign::Positive) => Ordering::Less,
                _ => Ordering::Equal,
            }
        }
    }
}
