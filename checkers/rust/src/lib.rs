// Independent Rust checkers for Grace17 proof tapes and compiled modules.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore
//
// The crate shares no code with the TypeScript kernel and never calls it.
// `machine` is the G17M proof machine of docs/checker-semantics.md, section
// 3; `compute` its ground computation; `environment` the logical
// environment and its digest; `admissions` the compiled-module events of
// section 7; and `foundation` the normative ZF, ZFC, and ZFG construction.

pub mod admissions;
pub mod ast;
pub mod compute;
pub mod environment;
pub mod foundation;
pub mod machine;
pub mod support;

pub const CHECKER_NAME: &str = "grace17-rust";
