// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#![cfg(feature = "python")]

use crate::{algebraic_numbers::RealAlgebraicNumber, traits::ExactDiv};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use pyo3::{
    basic::CompareOp,
    exceptions::{PyTypeError, PyValueError, PyZeroDivisionError},
    prelude::*,
    types::PyAny,
};
use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

#[derive(Clone)]
struct SharedNumber(Arc<RealAlgebraicNumber>);

impl Deref for SharedNumber {
    type Target = Arc<RealAlgebraicNumber>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for SharedNumber {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl From<RealAlgebraicNumber> for SharedNumber {
    fn from(v: RealAlgebraicNumber) -> Self {
        SharedNumber(v.into())
    }
}

impl IntoPy<PyObject> for SharedNumber {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberPy2 { value: self }.into_py(py)
    }
}

impl FromPyObject<'_> for SharedNumber {
    fn extract(value: &PyAny) -> PyResult<Self> {
        if let Ok(value) = value.extract::<PyRef<RealAlgebraicNumberPy2>>() {
            return Ok(value.value.clone());
        }
        let value = value.extract::<BigInt>()?;
        Ok(RealAlgebraicNumber::from(value).into())
    }
}

#[pyclass(name = "RealAlgebraicNumber", module = "algebraics")]
struct RealAlgebraicNumberPy2 {
    value: SharedNumber,
}

impl From<&'_ PyCell<RealAlgebraicNumberPy2>> for SharedNumber {
    fn from(v: &PyCell<RealAlgebraicNumberPy2>) -> Self {
        v.borrow().value.clone()
    }
}

#[pymethods]
impl RealAlgebraicNumberPy2 {
    #[new]
    fn pynew(value: Option<SharedNumber>) -> Self {
        let value = value.unwrap_or_else(|| RealAlgebraicNumber::zero().into());
        RealAlgebraicNumberPy2 { value }
    }
    fn __trunc__(&self, py: Python) -> BigInt {
        py.allow_threads(|| self.value.to_integer_trunc())
    }
    fn __floor__(&self, py: Python) -> BigInt {
        py.allow_threads(|| self.value.to_integer_floor())
    }
    fn __ceil__(&self, py: Python) -> BigInt {
        py.allow_threads(|| self.value.to_integer_ceil())
    }
    fn to_integer(&self) -> Option<BigInt> {
        self.value.to_integer()
    }
    fn to_rational(&self) -> Option<(BigInt, BigInt)> {
        self.value.to_rational().map(Into::into)
    }
    #[getter]
    fn minimal_polynomial(&self) -> Vec<BigInt> {
        self.value.minimal_polynomial().iter().collect()
    }
    #[getter]
    fn degree(&self) -> usize {
        self.value.degree()
    }
    fn is_rational(&self) -> bool {
        self.value.is_rational()
    }
    fn is_integer(&self) -> bool {
        self.value.is_integer()
    }
    fn recip(&self, py: Python) -> PyResult<SharedNumber> {
        py.allow_threads(|| Some(self.value.checked_recip()?.into()))
            .ok_or_else(get_div_by_zero_error)
    }
    /// returns `floor(log2(self))`
    fn floor_log2(&self, py: Python) -> PyResult<i64> {
        py.allow_threads(|| self.value.checked_floor_log2())
            .ok_or_else(get_floor_ceil_log2_error)
    }
    /// returns `ceil(log2(self))`
    fn ceil_log2(&self, py: Python) -> PyResult<i64> {
        py.allow_threads(|| self.value.checked_ceil_log2())
            .ok_or_else(get_floor_ceil_log2_error)
    }

    // Basic object methods
    fn __repr__(&self) -> PyResult<String> {
        Ok(format!("<{:?}>", *self.value))
    }
    fn __richcmp__(&self, py: Python, other: SharedNumber, op: CompareOp) -> PyResult<bool> {
        Ok(py.allow_threads(|| match op {
            CompareOp::Lt => *self.value < *other,
            CompareOp::Le => *self.value <= *other,
            CompareOp::Eq => *self.value == *other,
            CompareOp::Ne => *self.value != *other,
            CompareOp::Gt => *self.value > *other,
            CompareOp::Ge => *self.value >= *other,
        }))
    }

    // Numeric methods
    fn __add__(lhs: SharedNumber, py: Python, rhs: SharedNumber) -> PyResult<SharedNumber> {
        arithmetic_helper(py, lhs, rhs, |lhs, rhs| lhs + rhs)
    }
    fn __radd__(rhs: SharedNumber, py: Python, lhs: SharedNumber) -> PyResult<SharedNumber> {
        Self::__add__(lhs, py, rhs)
    }
    fn __sub__(lhs: SharedNumber, py: Python, rhs: SharedNumber) -> PyResult<SharedNumber> {
        arithmetic_helper(py, lhs, rhs, |lhs, rhs| lhs - rhs)
    }
    fn __rsub__(rhs: SharedNumber, py: Python, lhs: SharedNumber) -> PyResult<SharedNumber> {
        Self::__sub__(lhs, py, rhs)
    }
    fn __mul__(lhs: SharedNumber, py: Python, rhs: SharedNumber) -> PyResult<SharedNumber> {
        arithmetic_helper(py, lhs, rhs, |lhs, rhs| lhs * rhs)
    }
    fn __rmul__(rhs: SharedNumber, py: Python, lhs: SharedNumber) -> PyResult<SharedNumber> {
        Self::__mul__(lhs, py, rhs)
    }
    fn __truediv__(lhs: SharedNumber, py: Python, rhs: SharedNumber) -> PyResult<SharedNumber> {
        try_arithmetic_helper(
            py,
            lhs,
            rhs,
            |lhs, rhs| lhs.checked_exact_div(rhs).ok_or(()),
            |_| get_div_by_zero_error(),
        )
    }
    fn __rtruediv__(rhs: SharedNumber, py: Python, lhs: SharedNumber) -> PyResult<SharedNumber> {
        Self::__truediv__(lhs, py, rhs)
    }
    fn __pow__(
        lhs: SharedNumber,
        py: Python,
        rhs: SharedNumber,
        modulus: &PyAny,
    ) -> PyResult<SharedNumber> {
        if !modulus.is_none() {
            return Err(PyTypeError::new_err(
                "3 argument pow() not allowed for RealAlgebraicNumber",
            ));
        }
        try_arithmetic_helper(
            py,
            lhs,
            rhs,
            |lhs, rhs| {
                if let Some(rhs) = rhs.to_rational() {
                    lhs.checked_pow(rhs)
                        .ok_or("pow() failed for RealAlgebraicNumber")
                } else {
                    Err("exponent must be rational for RealAlgebraicNumber")
                }
            },
            PyValueError::new_err,
        )
    }
    fn __rpow__(
        rhs: SharedNumber,
        py: Python,
        lhs: SharedNumber,
        modulus: &PyAny,
    ) -> PyResult<SharedNumber> {
        Self::__pow__(lhs, py, rhs, modulus)
    }

    // Unary arithmetic
    fn __neg__(&self, py: Python) -> PyResult<SharedNumber> {
        Ok(py.allow_threads(|| (-&**self.value).into()))
    }
    fn __abs__(&self, py: Python) -> PyResult<SharedNumber> {
        Ok(py.allow_threads(|| self.value.abs().into()))
    }
}

fn get_div_by_zero_error() -> PyErr {
    PyZeroDivisionError::new_err("can't divide RealAlgebraicNumber by zero")
}

fn get_floor_ceil_log2_error() -> PyErr {
    PyValueError::new_err("can't extract base-2 logarithm of zero or negative RealAlgebraicNumber")
}

fn try_arithmetic_helper<
    E: Send,
    F: Send + FnOnce(&RealAlgebraicNumber, &RealAlgebraicNumber) -> Result<RealAlgebraicNumber, E>,
    MapErr: FnOnce(E) -> PyErr,
>(
    py: Python,
    lhs: SharedNumber,
    rhs: SharedNumber,
    f: F,
    map_err: MapErr,
) -> PyResult<SharedNumber> {
    py.allow_threads(|| Ok(f(&lhs, &rhs)?.into()))
        .map_err(map_err)
}

fn arithmetic_helper<
    F: Send + FnOnce(&RealAlgebraicNumber, &RealAlgebraicNumber) -> RealAlgebraicNumber,
>(
    py: Python,
    lhs: SharedNumber,
    rhs: SharedNumber,
    f: F,
) -> PyResult<SharedNumber> {
    enum Uninhabited {}
    try_arithmetic_helper(
        py,
        lhs,
        rhs,
        |lhs, rhs| Ok(f(lhs, rhs)),
        |v: Uninhabited| match v {},
    )
}

#[pymodule]
fn algebraics(_py: Python, m: &PyModule) -> PyResult<()> {
    m.add_class::<RealAlgebraicNumberPy2>()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conversion_compile_test() {
        #![allow(dead_code)]

        #[pyfunction]
        fn identity_result(v: SharedNumber) -> PyResult<SharedNumber> {
            Ok(v)
        }

        #[pyfunction]
        fn identity(v: SharedNumber) -> SharedNumber {
            v
        }
    }
}
