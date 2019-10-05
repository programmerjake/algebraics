// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#![cfg(feature = "python-extension")]

use crate::algebraic_numbers::RealAlgebraicNumber;
use crate::traits::ExactDivAssign;
use num_bigint::BigInt;
use num_bigint::Sign;
use num_traits::Signed;
use num_traits::ToPrimitive;
use num_traits::Zero;
use pyo3::basic::CompareOp;
use pyo3::exceptions::TypeError;
use pyo3::exceptions::ValueError;
use pyo3::exceptions::ZeroDivisionError;
use pyo3::prelude::*;
use pyo3::types::IntoPyDict;
use pyo3::types::PyAny;
use pyo3::types::PyBytes;
use pyo3::types::PyInt;
use pyo3::types::PyType;
use pyo3::FromPy;
use pyo3::PyNativeType;
use pyo3::PyNumberProtocol;
use pyo3::PyObjectProtocol;
use std::sync::Arc;

// TODO: Switch to using BigInt's python conversions once they are implemented
// see https://github.com/PyO3/pyo3/issues/543
#[derive(Clone, Debug)]
pub struct PyBigInt(pub BigInt);

impl ToPyObject for PyBigInt {
    fn to_object(&self, py: Python) -> PyObject {
        if let Some(value) = self.0.to_i64() {
            value.to_object(py)
        } else {
            let (sign, bytes) = self.0.to_bytes_le();
            let int_type: &PyType = py.get_type::<PyInt>();
            let retval = int_type
                .call_method1("from_bytes", (bytes, "little"))
                .unwrap()
                .downcast_ref::<PyInt>()
                .unwrap();
            if sign == Sign::Minus {
                retval.call_method0("__neg__").unwrap().to_object(py)
            } else {
                retval.to_object(py)
            }
        }
    }
}

impl FromPy<PyBigInt> for PyObject {
    fn from_py(value: PyBigInt, py: Python) -> Self {
        value.to_object(py)
    }
}

impl FromPyObject<'_> for PyBigInt {
    fn extract(ob: &PyAny) -> PyResult<Self> {
        let value = ob.downcast_ref::<PyInt>()?;
        if let Ok(value) = value.extract::<i64>() {
            Ok(PyBigInt(value.into()))
        } else {
            let mut len = 32;
            let bytes = loop {
                match value.call_method(
                    "to_bytes",
                    (len, "little"),
                    Some([("signed", true)].into_py_dict(ob.py())),
                ) {
                    Ok(bytes) => break bytes.downcast_ref::<PyBytes>()?,
                    Err(_) => len *= 2,
                }
            };
            Ok(PyBigInt(BigInt::from_signed_bytes_le(bytes.as_bytes())))
        }
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
        let value = value.extract::<Option<&PyInt>>()?;
        let value = match value {
            None => RealAlgebraicNumber::zero(),
            Some(value) => RealAlgebraicNumber::from(value.extract::<PyBigInt>()?.0),
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
    fn __trunc__(&self) -> PyBigInt {
        let gil = Python::acquire_gil();
        let py = gil.python();
        py.allow_threads(|| PyBigInt(self.value.to_integer_trunc()))
    }
    fn __floor__(&self) -> PyBigInt {
        let gil = Python::acquire_gil();
        let py = gil.python();
        py.allow_threads(|| PyBigInt(self.value.to_integer_floor()))
    }
    fn __ceil__(&self) -> PyBigInt {
        let gil = Python::acquire_gil();
        let py = gil.python();
        py.allow_threads(|| PyBigInt(self.value.to_integer_ceil()))
    }
    fn to_integer(&self) -> Option<PyBigInt> {
        self.value.to_integer().map(PyBigInt)
    }
    fn to_rational(&self) -> Option<(PyBigInt, PyBigInt)> {
        self.value.to_rational().map(|value| {
            let (numer, denom) = value.into();
            (PyBigInt(numer), PyBigInt(denom))
        })
    }
    #[getter]
    fn minimal_polynomial(&self) -> Vec<PyBigInt> {
        self.value
            .minimal_polynomial()
            .iter()
            .map(PyBigInt)
            .collect()
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

// FIXME: add tests
