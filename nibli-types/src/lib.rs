//! Canonical type definitions for the Nibli pipeline.
//!
//! These types replace the auto-generated WIT bindings that were previously
//! duplicated across gerna, smuni, and logji. All crates share one copy.

pub mod arithmetic;
pub mod ast;
pub mod error;
pub mod logic;

pub use arithmetic::eval_arithmetic;
