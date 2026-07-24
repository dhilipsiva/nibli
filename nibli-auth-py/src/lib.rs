//! Python bindings for `nibli_auth::tls` (module name: `nibli_auth_native`).

use nibli_auth::tls;
use nibli_auth::{AuthError, Decision as RustDecision, Explained as RustExplained, POLICY_VERSION};
use pyo3::exceptions::PyRuntimeError;
use pyo3::prelude::*;
use pyo3::types::PyList;

fn to_py_err(e: AuthError) -> PyErr {
    PyRuntimeError::new_err(e.message)
}

/// Authorization decision (mirrors Rust Decision).
#[pyclass(name = "Decision", module = "nibli_auth_native")]
#[derive(Clone)]
pub struct PyDecision {
    #[pyo3(get)]
    pub allowed: bool,
    #[pyo3(get)]
    pub verdict: String,
    #[pyo3(get)]
    pub reason: Option<String>,
    #[pyo3(get)]
    pub fields: Vec<String>,
}

impl From<RustDecision> for PyDecision {
    fn from(d: RustDecision) -> Self {
        Self {
            allowed: d.allowed,
            verdict: format!("{:?}", d.verdict),
            reason: d.reason,
            fields: d.fields,
        }
    }
}

#[pymethods]
impl PyDecision {
    fn __repr__(&self) -> String {
        format!(
            "Decision(allowed={}, verdict={:?}, reason={:?}, fields={:?})",
            self.allowed, self.verdict, self.reason, self.fields
        )
    }
}

/// Decision + optional proof JSON.
#[pyclass(name = "Explained", module = "nibli_auth_native")]
#[derive(Clone)]
pub struct PyExplained {
    #[pyo3(get)]
    pub decision: PyDecision,
    #[pyo3(get)]
    pub proof_json: Option<String>,
}

impl From<RustExplained> for PyExplained {
    fn from(e: RustExplained) -> Self {
        Self {
            decision: e.decision.into(),
            proof_json: e.proof_json,
        }
    }
}

#[pyfunction]
#[pyo3(signature = (agent, action, object, context_kr=""))]
fn can(agent: &str, action: &str, object: &str, context_kr: &str) -> PyResult<PyDecision> {
    tls::can(agent, action, object, context_kr)
        .map(Into::into)
        .map_err(to_py_err)
}

#[pyfunction]
#[pyo3(signature = (agent, action, object, candidates, context_kr=""))]
fn allowed_fields(
    agent: &str,
    action: &str,
    object: &str,
    candidates: Bound<'_, PyList>,
    context_kr: &str,
) -> PyResult<Vec<String>> {
    let mut refs: Vec<String> = Vec::with_capacity(candidates.len());
    for item in candidates.iter() {
        refs.push(item.extract::<String>()?);
    }
    let slice: Vec<&str> = refs.iter().map(String::as_str).collect();
    tls::allowed_fields(agent, action, object, context_kr, &slice).map_err(to_py_err)
}

#[pyfunction]
#[pyo3(signature = (agent, action, object, context_kr=""))]
fn explain(
    agent: &str,
    action: &str,
    object: &str,
    context_kr: &str,
) -> PyResult<PyExplained> {
    tls::explain(agent, action, object, context_kr)
        .map(Into::into)
        .map_err(to_py_err)
}

#[pyfunction]
fn policy_version() -> &'static str {
    POLICY_VERSION
}

#[pyfunction]
fn reset_thread_auth() {
    tls::reset_thread_auth();
}

#[pymodule]
fn nibli_auth_native(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_class::<PyDecision>()?;
    m.add_class::<PyExplained>()?;
    m.add_function(wrap_pyfunction!(can, m)?)?;
    m.add_function(wrap_pyfunction!(allowed_fields, m)?)?;
    m.add_function(wrap_pyfunction!(explain, m)?)?;
    m.add_function(wrap_pyfunction!(policy_version, m)?)?;
    m.add_function(wrap_pyfunction!(reset_thread_auth, m)?)?;
    Ok(())
}
