// Command-line G17M proof-tape checker.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use grace17_checkers::environment::Environment;
use grace17_checkers::machine;
use grace17_checkers::support::{read_file, Result};
use grace17_checkers::CHECKER_NAME;
use std::process::ExitCode;

struct Options {
    certificate: String,
    environment: String,
    json: bool,
    fuel: i64,
}

const USAGE: &str = "usage: g17check CERTIFICATE --environment ENVIRONMENT [--json] [--fuel STEPS]";

fn parse_fuel(value: Option<String>) -> std::result::Result<i64, String> {
    match value.and_then(|text| text.parse::<i64>().ok()) {
        Some(steps) if steps > 0 => Ok(steps),
        _ => Err("--fuel must be a positive integer".into()),
    }
}

fn parse_arguments() -> std::result::Result<Options, String> {
    let mut certificate = None;
    let mut environment = None;
    let mut json = false;
    let mut fuel = grace17_checkers::compute::fuel();
    let mut args = std::env::args().skip(1);
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--environment" => environment = args.next(),
            "--json" => json = true,
            "--fuel" => fuel = parse_fuel(args.next())?,
            "-h" | "--help" => return Err(USAGE.into()),
            other if certificate.is_none() && !other.starts_with("--") => certificate = Some(other.to_string()),
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    match (certificate, environment) {
        (Some(certificate), Some(environment)) => Ok(Options { certificate, environment, json, fuel }),
        _ => Err(USAGE.into()),
    }
}

fn run(options: &Options) -> Result<serde_json::Value> {
    grace17_checkers::compute::set_fuel(options.fuel);
    let environment = Environment::from_file(&options.environment)?;
    let program = machine::decode(&read_file(&options.certificate)?)?;
    let (arena, _) = machine::verify(&program, &environment, true, None)?;
    Ok(serde_json::json!({
        "ok": true,
        "checker": CHECKER_NAME,
        "version": machine::VERSION,
        "theorems": if program.theorems.is_empty() { 1 } else { program.theorems.len() },
        "instructions": program.code.len(),
        "terms": arena.terms.len(),
        "formulas": arena.formulas.len(),
        "environment": environment.digest,
    }))
}

fn main() -> ExitCode {
    let options = match parse_arguments() {
        Ok(options) => options,
        Err(message) => {
            eprintln!("{message}");
            return ExitCode::from(2);
        }
    };
    // Deep proofs recurse through the arena operations; a large stack keeps
    // a resource limit a rejection rather than a crash.
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || run(&options).map(|result| (result, options.json)))
        .expect("checker thread");
    match handle.join() {
        Ok(Ok((result, json))) => {
            if json {
                println!("{result}");
            } else {
                println!("checked {} theorem(s), {} instructions", result["theorems"], result["instructions"]);
            }
            ExitCode::SUCCESS
        }
        Ok(Err(error)) => {
            let json = std::env::args().any(|argument| argument == "--json");
            let result = serde_json::json!({"ok": false, "checker": CHECKER_NAME, "message": error.to_string()});
            if json {
                eprintln!("{result}");
            } else {
                eprintln!("check failed: {error}");
            }
            ExitCode::from(1)
        }
        Err(_) => {
            eprintln!("check failed: resource limit");
            ExitCode::from(1)
        }
    }
}
