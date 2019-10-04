// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#![cfg(feature = "python-extension")]

use crate::algebraic_numbers::RealAlgebraicNumber;
use num_bigint::BigInt;
use num_bigint::Sign;
use num_traits::ToPrimitive;
use num_traits::Zero;
use pyo3::prelude::*;
use pyo3::types::IntoPyDict;
use pyo3::types::PyAny;
use pyo3::types::PyBytes;
use pyo3::types::PyInt;
use pyo3::types::PyType;
use pyo3::PyNativeType;
use pyo3::PyObjectProtocol;

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
struct RealAlgebraicNumberPy {
    value: RealAlgebraicNumber,
}

#[pymethods(PyObjectProtocol)]
impl RealAlgebraicNumberPy {
    #[new]
    fn pynew(obj: &PyRawObject, value: Option<&PyInt>) -> PyResult<()> {
        let value = match value {
            None => RealAlgebraicNumber::zero(),
            Some(value) => RealAlgebraicNumber::from(value.extract::<PyBigInt>()?.0),
        };
        obj.init(RealAlgebraicNumberPy { value });
        Ok(())
    }
    // FIXME: implement rest of methods
}

#[pyproto]
impl PyObjectProtocol for RealAlgebraicNumberPy {
    fn __repr__(&self) -> PyResult<String> {
        Ok(format!("{:?}", self.value))
    }
}

#[pymodule]
fn algebraics(_py: Python, m: &PyModule) -> PyResult<()> {
    // FIXME: add module members
    m.add_class::<RealAlgebraicNumberPy>()?;
    Ok(())
}
