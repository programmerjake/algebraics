// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#![cfg(feature = "python")]

use crate::algebraic_numbers::RealAlgebraicNumber;
use crate::traits::ExactDivAssign;
use num_bigint::BigInt;
use num_traits::Signed;
use num_traits::Zero;
use pyo3::basic::CompareOp;
use pyo3::exceptions::TypeError;
use pyo3::exceptions::ValueError;
use pyo3::exceptions::ZeroDivisionError;
use pyo3::prelude::*;
use pyo3::types::PyAny;
use pyo3::PyNativeType;
use pyo3::PyNumberProtocol;
use pyo3::PyObjectProtocol;
use std::sync::Arc;

impl FromPyObject<'_> for RealAlgebraicNumber {
    fn extract(value: &PyAny) -> PyResult<Self> {
        Ok((*RealAlgebraicNumberPy::extract(value)?.value).clone())
    }
}

impl<'a> FromPyObject<'a> for &'a RealAlgebraicNumber {
    fn extract(value: &'a PyAny) -> PyResult<Self> {
        let result = RealAlgebraicNumberPy::extract(value)?.value.clone();
        let result: &'a _ = value.py().register_any(result);
        Ok(&**result)
    }
}

impl IntoPy<PyObject> for RealAlgebraicNumber {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberPy {
            value: Arc::new(self),
        }
        .into_py(py)
    }
}

impl IntoPy<PyObject> for &'_ RealAlgebraicNumber {
    fn into_py(self, py: Python) -> PyObject {
        RealAlgebraicNumberPy {
            value: Arc::new(self.clone()),
        }
        .into_py(py)
    }
}

impl ToPyObject for RealAlgebraicNumber {
    fn to_object(&self, py: Python) -> PyObject {
        self.into_py(py)
    }
}

#[pyclass(name=RealAlgebraicNumber, module="algebraics")]
#[derive(Clone)]
struct RealAlgebraicNumberPy {
    value: Arc<RealAlgebraicNumber>,
}

impl FromPyObject<'_> for RealAlgebraicNumberPy {
    fn extract(value: &PyAny) -> PyResult<Self> {
        if let Ok(value) = value.downcast_ref::<RealAlgebraicNumberPy>() {
            return Ok(value.clone());
        }
        let value = value.extract::<Option<BigInt>>()?;
        let value = match value {
            None => RealAlgebraicNumber::zero(),
            Some(value) => RealAlgebraicNumber::from(value),
        }
        .into();
        Ok(RealAlgebraicNumberPy { value })
    }
}

#[pymethods(PyObjectProtocol, PyNumberProtocol)]
impl RealAlgebraicNumberPy {
    #[new]
    fn pynew(obj: &PyRawObject, value: Option<RealAlgebraicNumberPy>) {
        obj.init(value.unwrap_or_else(|| RealAlgebraicNumberPy {
            value: RealAlgebraicNumber::zero().into(),
        }));
    }
    fn __trunc__(&self) -> BigInt {
        let gil = Python::acquire_gil();
        let py = gil.python();
        py.allow_threads(|| self.value.to_integer_trunc())
    }
    fn __floor__(&self) -> BigInt {
        let gil = Python::acquire_gil();
        let py = gil.python();
        py.allow_threads(|| self.value.to_integer_floor())
    }
    fn __ceil__(&self) -> BigInt {
        let gil = Python::acquire_gil();
        let py = gil.python();
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
    fn recip(&self) -> PyResult<RealAlgebraicNumberPy> {
        Python::acquire_gil()
            .python()
            .allow_threads(|| {
                Some(RealAlgebraicNumberPy {
                    value: self.value.checked_recip()?.into(),
                })
            })
            .ok_or_else(get_div_by_zero_error)
    }
    /// returns `floor(log2(self))`
    fn floor_log2(&self) -> PyResult<i64> {
        Python::acquire_gil()
            .python()
            .allow_threads(|| self.value.checked_floor_log2())
            .ok_or_else(get_floor_ceil_log2_error)
    }
    /// returns `ceil(log2(self))`
    fn ceil_log2(&self) -> PyResult<i64> {
        Python::acquire_gil()
            .python()
            .allow_threads(|| self.value.checked_ceil_log2())
            .ok_or_else(get_floor_ceil_log2_error)
    }
}

#[pyproto]
impl PyObjectProtocol for RealAlgebraicNumberPy {
    fn __repr__(&self) -> PyResult<String> {
        Ok(format!("<{:?}>", self.value))
    }
    fn __richcmp__(&self, other: &PyAny, op: CompareOp) -> PyResult<bool> {
        let py = other.py();
        let other = other.extract::<RealAlgebraicNumberPy>()?;
        Ok(py.allow_threads(|| match op {
            CompareOp::Lt => self.value < other.value,
            CompareOp::Le => self.value <= other.value,
            CompareOp::Eq => self.value == other.value,
            CompareOp::Ne => self.value != other.value,
            CompareOp::Gt => self.value > other.value,
            CompareOp::Ge => self.value >= other.value,
        }))
    }
}

fn get_div_by_zero_error() -> PyErr {
    ZeroDivisionError::py_err("can't divide RealAlgebraicNumber by zero")
}

fn get_floor_ceil_log2_error() -> PyErr {
    ValueError::py_err("can't extract base-2 logarithm of zero or negative RealAlgebraicNumber")
}

#[pyproto]
impl PyNumberProtocol for RealAlgebraicNumberPy {
    fn __add__(lhs: &PyAny, rhs: RealAlgebraicNumberPy) -> PyResult<RealAlgebraicNumberPy> {
        let py = lhs.py();
        let mut lhs = lhs.extract::<RealAlgebraicNumberPy>()?;
        Ok(py.allow_threads(|| {
            *Arc::make_mut(&mut lhs.value) += &*rhs.value;
            lhs
        }))
    }
    fn __sub__(lhs: &PyAny, rhs: RealAlgebraicNumberPy) -> PyResult<RealAlgebraicNumberPy> {
        let py = lhs.py();
        let mut lhs = lhs.extract::<RealAlgebraicNumberPy>()?;
        Ok(py.allow_threads(|| {
            *Arc::make_mut(&mut lhs.value) -= &*rhs.value;
            lhs
        }))
    }
    fn __mul__(lhs: &PyAny, rhs: RealAlgebraicNumberPy) -> PyResult<RealAlgebraicNumberPy> {
        let py = lhs.py();
        let mut lhs = lhs.extract::<RealAlgebraicNumberPy>()?;
        Ok(py.allow_threads(|| {
            *Arc::make_mut(&mut lhs.value) *= &*rhs.value;
            lhs
        }))
    }
    fn __truediv__(lhs: &PyAny, rhs: RealAlgebraicNumberPy) -> PyResult<RealAlgebraicNumberPy> {
        let py = lhs.py();
        let mut lhs = lhs.extract::<RealAlgebraicNumberPy>()?;
        py.allow_threads(|| -> Result<RealAlgebraicNumberPy, ()> {
            Arc::make_mut(&mut lhs.value).checked_exact_div_assign(&*rhs.value)?;
            Ok(lhs)
        })
        .map_err(|()| get_div_by_zero_error())
    }
    fn __pow__(
        lhs: RealAlgebraicNumberPy,
        rhs: RealAlgebraicNumberPy,
        modulus: &PyAny,
    ) -> PyResult<RealAlgebraicNumberPy> {
        let py = modulus.py();
        if !modulus.is_none() {
            return Err(TypeError::py_err(
                "3 argument pow() not allowed for RealAlgebraicNumber",
            ));
        }
        py.allow_threads(|| -> Result<RealAlgebraicNumberPy, &'static str> {
            if let Some(rhs) = rhs.value.to_rational() {
                Ok(RealAlgebraicNumberPy {
                    value: lhs
                        .value
                        .checked_pow(rhs)
                        .ok_or("pow() failed for RealAlgebraicNumber")?
                        .into(),
                })
            } else {
                Err("exponent must be rational for RealAlgebraicNumber")
            }
        })
        .map_err(ValueError::py_err)
    }

    // Unary arithmetic
    fn __neg__(&self) -> PyResult<RealAlgebraicNumberPy> {
        Ok(Python::acquire_gil()
            .python()
            .allow_threads(|| RealAlgebraicNumberPy {
                value: Arc::from(-&*self.value),
            }))
    }
    fn __abs__(&self) -> PyResult<RealAlgebraicNumberPy> {
        Ok(Python::acquire_gil()
            .python()
            .allow_threads(|| RealAlgebraicNumberPy {
                value: self.value.abs().into(),
            }))
    }
}

#[pymodule]
fn algebraics(_py: Python, m: &PyModule) -> PyResult<()> {
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
