//! Canonical type definitions for the Nibli pipeline.
//!
//! These types replace the auto-generated WIT bindings that were previously
//! duplicated across nibli-kr, nibli-semantics, and nibli-reason. All crates share one copy.

pub mod arithmetic;
pub mod ast;
pub mod error;
pub mod logic;

pub use arithmetic::eval_arithmetic;
