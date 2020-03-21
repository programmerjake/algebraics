// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#![cfg(feature = "python")]

use crate::{algebraic_numbers::RealAlgebraicNumber, traits::ExactDivAssign};
use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use pyo3::{
    basic::CompareOp,
    exceptions::{TypeError, ValueError, ZeroDivisionError},
    prelude::*,
    types::PyAny,
    PyNativeType, PyNumberProtocol, PyObjectProtocol,
};
use std::{
    ops::{Deref, DerefMut},
    sync::Arc,
};

impl FromPyObject<'_> for RealAlgebraicNumber {
    fn extract(value: &PyAny) -> PyResult<Self> {
        Ok(RealAlgebraicNumberWrapper::extract(value)?.into())
    }
}

impl<'a> FromPyObject<'a> for &'a RealAlgebraicNumber {
    fn extract(value: &'a PyAny) -> PyResult<Self> {
        let wrapper: RealAlgebraicNumberWrapper = value.extract()?;
        Ok(&value.py().register_any(wrapper))
    }
}

impl IntoPy<PyObject> for RealAlgebraicNumber {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberWrapper::from(self).into_py(py)
    }
}

impl IntoPy<PyObject> for &'_ RealAlgebraicNumber {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberWrapper::from(self).into_py(py)
    }
}

impl ToPyObject for RealAlgebraicNumber {
    fn to_object(&self, py: Python) -> PyObject {
        self.into_py(py)
    }
}

#[derive(Clone)]
struct RealAlgebraicNumberWrapper(Arc<RealAlgebraicNumber>);

impl Deref for RealAlgebraicNumberWrapper {
    type Target = Arc<RealAlgebraicNumber>;
    fn deref(&self) -> &Self::Target {
        &self.0
    }
}

impl DerefMut for RealAlgebraicNumberWrapper {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.0
    }
}

impl FromPyObject<'_> for RealAlgebraicNumberWrapper {
    fn extract(value: &PyAny) -> PyResult<Self> {
        if let Ok(value) = value.extract::<PyRef<RealAlgebraicNumberPy2>>() {
            return Ok(value.value.clone());
        }
        let value = value.extract::<BigInt>()?;
        Ok(RealAlgebraicNumber::from(value).into())
    }
}

impl From<Arc<RealAlgebraicNumber>> for RealAlgebraicNumberWrapper {
    fn from(v: Arc<RealAlgebraicNumber>) -> Self {
        RealAlgebraicNumberWrapper(v)
    }
}

impl From<RealAlgebraicNumber> for RealAlgebraicNumberWrapper {
    fn from(v: RealAlgebraicNumber) -> Self {
        RealAlgebraicNumberWrapper(v.into())
    }
}

impl From<&'_ RealAlgebraicNumber> for RealAlgebraicNumberWrapper {
    fn from(v: &RealAlgebraicNumber) -> Self {
        RealAlgebraicNumber::clone(v).into()
    }
}

impl Into<Arc<RealAlgebraicNumber>> for RealAlgebraicNumberWrapper {
    fn into(self) -> Arc<RealAlgebraicNumber> {
        self.0
    }
}

impl From<RealAlgebraicNumberWrapper> for RealAlgebraicNumber {
    fn from(v: RealAlgebraicNumberWrapper) -> Self {
        match Arc::try_unwrap(v.0) {
            Ok(v) => v,
            Err(v) => (*v).clone(),
        }
    }
}

impl IntoPy<PyObject> for RealAlgebraicNumberWrapper {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberPy2 { value: self }.into_py(py)
    }
}

impl IntoPy<PyObject> for &'_ RealAlgebraicNumberWrapper {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberWrapper::clone(self).into_py(py)
    }
}

impl ToPyObject for RealAlgebraicNumberWrapper {
    fn to_object(&self, py: Python) -> PyObject {
        self.into_py(py)
    }
}

#[pyclass(name=RealAlgebraicNumber, module="algebraics")]
struct RealAlgebraicNumberPy2 {
    value: RealAlgebraicNumberWrapper,
}

#[pymethods(PyObjectProtocol, PyNumberProtocol)]
impl RealAlgebraicNumberPy2 {
    #[new]
    fn pynew(value: Option<RealAlgebraicNumberWrapper>) -> Self {
        let value = value.unwrap_or_else(|| RealAlgebraicNumber::zero().into());
        RealAlgebraicNumberPy2 { value }
    }
    fn __trunc__(&self, py: Python<'_>) -> BigInt {
        py.allow_threads(|| self.value.to_integer_trunc())
    }
    fn __floor__(&self, py: Python<'_>) -> BigInt {
        py.allow_threads(|| self.value.to_integer_floor())
    }
    fn __ceil__(&self, py: Python<'_>) -> BigInt {
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
    fn recip(&self, py: Python<'_>) -> PyResult<RealAlgebraicNumberWrapper> {
        py.allow_threads(|| Some(self.value.checked_recip()?.into()))
            .ok_or_else(get_div_by_zero_error)
    }
    /// returns `floor(log2(self))`
    fn floor_log2(&self, py: Python<'_>) -> PyResult<i64> {
        py.allow_threads(|| self.value.checked_floor_log2())
            .ok_or_else(get_floor_ceil_log2_error)
    }
    /// returns `ceil(log2(self))`
    fn ceil_log2(&self, py: Python<'_>) -> PyResult<i64> {
        py.allow_threads(|| self.value.checked_ceil_log2())
            .ok_or_else(get_floor_ceil_log2_error)
    }
}

#[pyproto]
impl PyObjectProtocol for RealAlgebraicNumberPy2 {
    fn __repr__(&self) -> PyResult<String> {
        Ok(format!("<{:?}>", *self.value))
    }
    fn __richcmp__(&self, other: &PyAny, op: CompareOp) -> PyResult<bool> {
        let py = other.py();
        let other = other.extract::<RealAlgebraicNumberWrapper>()?;
        Ok(py.allow_threads(|| match op {
            CompareOp::Lt => *self.value < *other,
            CompareOp::Le => *self.value <= *other,
            CompareOp::Eq => *self.value == *other,
            CompareOp::Ne => *self.value != *other,
            CompareOp::Gt => *self.value > *other,
            CompareOp::Ge => *self.value >= *other,
        }))
    }
}

fn get_div_by_zero_error() -> PyErr {
    ZeroDivisionError::py_err("can't divide RealAlgebraicNumber by zero")
}

fn get_floor_ceil_log2_error() -> PyErr {
    ValueError::py_err("can't extract base-2 logarithm of zero or negative RealAlgebraicNumber")
}

fn try_arithmetic_helper<
    E: Send,
    F: Send + FnOnce(&mut RealAlgebraicNumber, &RealAlgebraicNumber) -> Result<(), E>,
    MapErr: FnOnce(E) -> PyErr,
>(
    lhs: &PyAny,
    rhs: RealAlgebraicNumberWrapper,
    f: F,
    map_err: MapErr,
) -> PyResult<RealAlgebraicNumberWrapper> {
    let py = lhs.py();
    let mut lhs: RealAlgebraicNumberWrapper = lhs.extract()?;
    py.allow_threads(|| {
        f(Arc::make_mut(&mut lhs), &**rhs)?;
        Ok(lhs)
    })
    .map_err(map_err)
}

fn arithmetic_helper<F: Send + FnOnce(&mut RealAlgebraicNumber, &RealAlgebraicNumber)>(
    lhs: &PyAny,
    rhs: RealAlgebraicNumberWrapper,
    f: F,
) -> PyResult<RealAlgebraicNumberWrapper> {
    enum Uninhabited {}
    try_arithmetic_helper(
        lhs,
        rhs,
        |lhs, rhs| {
            f(lhs, rhs);
            Ok(())
        },
        |v: Uninhabited| match v {},
    )
}

#[pyproto]
impl PyNumberProtocol for RealAlgebraicNumberPy2 {
    fn __add__(
        lhs: &PyAny,
        rhs: RealAlgebraicNumberWrapper,
    ) -> PyResult<RealAlgebraicNumberWrapper> {
        arithmetic_helper(lhs, rhs, |lhs, rhs| *lhs += rhs)
    }
    fn __sub__(
        lhs: &PyAny,
        rhs: RealAlgebraicNumberWrapper,
    ) -> PyResult<RealAlgebraicNumberWrapper> {
        arithmetic_helper(lhs, rhs, |lhs, rhs| *lhs -= rhs)
    }
    fn __mul__(
        lhs: &PyAny,
        rhs: RealAlgebraicNumberWrapper,
    ) -> PyResult<RealAlgebraicNumberWrapper> {
        arithmetic_helper(lhs, rhs, |lhs, rhs| *lhs *= rhs)
    }
    fn __truediv__(
        lhs: &PyAny,
        rhs: RealAlgebraicNumberWrapper,
    ) -> PyResult<RealAlgebraicNumberWrapper> {
        try_arithmetic_helper(
            lhs,
            rhs,
            |lhs, rhs| lhs.checked_exact_div_assign(rhs),
            |()| get_div_by_zero_error(),
        )
    }
    fn __pow__(
        lhs: &PyAny,
        rhs: RealAlgebraicNumberWrapper,
        modulus: &PyAny,
    ) -> PyResult<RealAlgebraicNumberWrapper> {
        if !modulus.is_none() {
            return Err(TypeError::py_err(
                "3 argument pow() not allowed for RealAlgebraicNumber",
            ));
        }
        try_arithmetic_helper(
            lhs,
            rhs,
            |lhs, rhs| {
                if let Some(rhs) = rhs.to_rational() {
                    *lhs = lhs
                        .checked_pow(rhs)
                        .ok_or("pow() failed for RealAlgebraicNumber")?;
                    Ok(())
                } else {
                    Err("exponent must be rational for RealAlgebraicNumber")
                }
            },
            ValueError::py_err,
        )
    }

    // Unary arithmetic
    fn __neg__(&self) -> PyResult<RealAlgebraicNumberWrapper> {
        Ok(Python::acquire_gil()
            .python()
            .allow_threads(|| (-&**self.value).into()))
    }
    fn __abs__(&self) -> PyResult<RealAlgebraicNumberWrapper> {
        Ok(Python::acquire_gil()
            .python()
            .allow_threads(|| self.value.abs().into()))
    }
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
        fn identity_ref_result(v: &RealAlgebraicNumber) -> PyResult<&RealAlgebraicNumber> {
            Ok(v)
        }

        #[pyfunction]
        fn identity_result(v: RealAlgebraicNumber) -> PyResult<RealAlgebraicNumber> {
            Ok(v)
        }

        #[pyfunction]
        fn identity_ref(v: &RealAlgebraicNumber) -> &RealAlgebraicNumber {
            v
        }

        #[pyfunction]
        fn identity(v: RealAlgebraicNumber) -> RealAlgebraicNumber {
            v
        }
    }
}
