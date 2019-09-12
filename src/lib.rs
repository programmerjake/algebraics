// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#[macro_use]
extern crate lazy_static;

pub mod algebraic_numbers;
pub mod array2d;
pub mod interval_arithmetic;
pub mod lattice;
pub mod mod_int;
pub mod polynomial;
pub mod prelude;
pub mod quadratic_numbers;
pub mod traits;
pub mod util;

pub use algebraic_numbers::RealAlgebraicNumber;
