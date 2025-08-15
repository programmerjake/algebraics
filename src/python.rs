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
    types::{PyAny, PyInt},
};
use std::convert::{TryFrom, TryInto};

#[derive(FromPyObject)]
enum Number<'py> {
    #[pyo3(transparent, annotation = "RealAlgebraicNumber")]
    RealAlgebraicNumber(Bound<'py, RealAlgebraicNumberPy>),
    #[pyo3(transparent, annotation = "int")]
    Int(Bound<'py, PyInt>),
}

impl<'py> From<Bound<'py, RealAlgebraicNumberPy>> for Number<'py> {
    fn from(value: Bound<'py, RealAlgebraicNumberPy>) -> Self {
        Number::RealAlgebraicNumber(value)
    }
}

impl<'py> TryFrom<Number<'py>> for Bound<'py, RealAlgebraicNumberPy> {
    type Error = PyErr;
    fn try_from(value: Number<'py>) -> Result<Self, Self::Error> {
        Ok(match value {
            Number::RealAlgebraicNumber(value) => value,
            Number::Int(value) => Bound::new(
                value.py(),
                RealAlgebraicNumberPy {
                    value: RealAlgebraicNumber::from(value.extract::<BigInt>()?),
                },
            )?,
        })
    }
}

impl<'py> FromPyObject<'py> for RealAlgebraicNumber {
    fn extract_bound(ob: &Bound<'py, PyAny>) -> PyResult<Self> {
        Ok(match ob.extract::<Number<'py>>()? {
            Number::RealAlgebraicNumber(value) => value.get().value.clone(),
            Number::Int(value) => RealAlgebraicNumber::from(value.extract::<BigInt>()?),
        })
    }
}

impl<'py> IntoPyObject<'py> for RealAlgebraicNumber {
    type Target = RealAlgebraicNumberPy;
    type Output = Bound<'py, RealAlgebraicNumberPy>;
    type Error = PyErr;

    fn into_pyobject(self, py: Python<'py>) -> Result<Self::Output, Self::Error> {
        Bound::new(py, RealAlgebraicNumberPy { value: self })
    }
}

#[pyclass(name = "RealAlgebraicNumber", module = "algebraics", frozen)]
pub struct RealAlgebraicNumberPy {
    pub value: RealAlgebraicNumber,
}

#[pymethods]
impl RealAlgebraicNumberPy {
    #[new]
    #[pyo3(signature = (value=None))]
    fn pynew<'py>(py: Python<'py>, value: Option<Number<'py>>) -> PyResult<Bound<'py, Self>> {
        match value {
            None => Bound::new(
                py,
                RealAlgebraicNumberPy {
                    value: RealAlgebraicNumber::zero(),
                },
            ),
            Some(value) => value.try_into(),
        }
    }
    fn __trunc__(&self, py: Python) -> BigInt {
        py.allow_threads(|| self.value.to_integer_trunc())
    }
    fn __int__(&self, py: Python) -> BigInt {
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
    fn recip<'py>(&self, py: Python<'py>) -> PyResult<RealAlgebraicNumber> {
        py.allow_threads(|| Some(self.value.checked_recip()?))
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
        Ok(format!("<{:?}>", self.value))
    }
    fn __richcmp__(&self, py: Python<'_>, other: Number<'_>, op: CompareOp) -> PyResult<bool> {
        let other = Bound::<RealAlgebraicNumberPy>::try_from(other)?;
        let other = other.get();
        Ok(py.allow_threads(|| match op {
            CompareOp::Lt => self.value < other.value,
            CompareOp::Le => self.value <= other.value,
            CompareOp::Eq => self.value == other.value,
            CompareOp::Ne => self.value != other.value,
            CompareOp::Gt => self.value > other.value,
            CompareOp::Ge => self.value >= other.value,
        }))
    }

    // Numeric methods
    fn __add__(
        lhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        rhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        arithmetic_helper(py, lhs.get(), rhs, |lhs, rhs| lhs + rhs)
    }
    fn __radd__(
        rhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        lhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        Self::__add__(lhs.try_into()?, py, rhs.into())
    }
    fn __sub__(
        lhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        rhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        arithmetic_helper(py, lhs.get(), rhs, |lhs, rhs| lhs - rhs)
    }
    fn __rsub__(
        rhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        lhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        Self::__sub__(lhs.try_into()?, py, rhs.into())
    }
    fn __mul__(
        lhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        rhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        arithmetic_helper(py, lhs.get(), rhs, |lhs, rhs| lhs * rhs)
    }
    fn __rmul__(
        rhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        lhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        Self::__mul__(lhs.try_into()?, py, rhs.into())
    }
    fn __truediv__(
        lhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        rhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        try_arithmetic_helper(
            py,
            lhs.get(),
            rhs,
            |lhs, rhs| lhs.checked_exact_div(rhs).ok_or(()),
            |_| get_div_by_zero_error(),
        )
    }
    fn __rtruediv__(
        rhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        lhs: Number<'_>,
    ) -> PyResult<RealAlgebraicNumber> {
        Self::__truediv__(lhs.try_into()?, py, rhs.into())
    }
    fn __pow__(
        lhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        rhs: Number<'_>,
        modulus: &Bound<'_, PyAny>,
    ) -> PyResult<RealAlgebraicNumber> {
        if !modulus.is_none() {
            return Err(PyTypeError::new_err(
                "3 argument pow() not allowed for RealAlgebraicNumber",
            ));
        }
        try_arithmetic_helper(
            py,
            lhs.get(),
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
        rhs: Bound<'_, RealAlgebraicNumberPy>,
        py: Python<'_>,
        lhs: Number<'_>,
        modulus: &Bound<'_, PyAny>,
    ) -> PyResult<RealAlgebraicNumber> {
        Self::__pow__(lhs.try_into()?, py, rhs.into(), modulus)
    }

    // Unary arithmetic
    fn __neg__(&self, py: Python) -> PyResult<RealAlgebraicNumber> {
        Ok(py.allow_threads(|| (-&self.value).into()))
    }
    fn __abs__(&self, py: Python) -> PyResult<RealAlgebraicNumber> {
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
    lhs: &RealAlgebraicNumberPy,
    rhs: Number<'_>,
    f: F,
    map_err: MapErr,
) -> PyResult<RealAlgebraicNumber> {
    let rhs = Bound::<RealAlgebraicNumberPy>::try_from(rhs)?;
    let rhs = rhs.get();
    py.allow_threads(|| Ok(f(&lhs.value, &rhs.value)?.into()))
        .map_err(map_err)
}

fn arithmetic_helper<
    F: Send + FnOnce(&RealAlgebraicNumber, &RealAlgebraicNumber) -> RealAlgebraicNumber,
>(
    py: Python,
    lhs: &RealAlgebraicNumberPy,
    rhs: Number<'_>,
    f: F,
) -> PyResult<RealAlgebraicNumber> {
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
fn algebraics(_py: Python, m: Bound<PyModule>) -> PyResult<()> {
    m.add_class::<RealAlgebraicNumberPy>()?;
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conversion_compile_test() {
        #![allow(dead_code)]

        #[pyfunction]
        fn identity_result(v: RealAlgebraicNumber) -> PyResult<RealAlgebraicNumber> {
            Ok(v)
        }

        #[pyfunction]
        fn identity(v: RealAlgebraicNumber) -> RealAlgebraicNumber {
            v
        }
    }
}
