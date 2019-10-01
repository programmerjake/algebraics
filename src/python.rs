// SPDX-License-Identifier: LGPL-2.1-or-later
// See Notices.txt for copyright information

#![cfg(feature = "python-extension")]

use crate::algebraic_numbers::RealAlgebraicNumber;
use num_bigint::BigInt;
use num_traits::Zero;
use pyo3::prelude::*;
use pyo3::types::PyAny;
use pyo3::types::PyInt;

// TODO: Switch to using BigInt's python conversions once they are implemented
// see https://github.com/PyO3/pyo3/issues/543
#[derive(Clone, Debug)]
pub struct PyBigInt(pub BigInt);

impl ToPyObject for PyBigInt {
    fn to_object(&self, py: Python) -> PyObject {
        // FIXME: implement
        unimplemented!()
    }
}

impl FromPyObject<'_> for PyBigInt {
    fn extract(ob: &PyAny) -> PyResult<Self> {
        // FIXME: implement
        unimplemented!()
    }
}

#[pyclass(name=RealAlgebraicNumber, module="algebraics")]
struct RealAlgebraicNumberPy {
    value: RealAlgebraicNumber,
}

#[pymethods]
impl RealAlgebraicNumberPy {
    #[new]
    fn new(obj: &PyRawObject, value: Option<&PyInt>) {
        match value {
            None => obj.init(RealAlgebraicNumberPy {
                value: RealAlgebraicNumber::zero(),
            }),
            Some(value) => {
                // FIXME: implement
                unimplemented!();
            }
        }
    }
    // FIXME: implement rest of methods
}

#[pymodule]
fn algebraics(py: Python, m: &PyModule) -> PyResult<()> {
    // FIXME: add module members
    Ok(())
}
