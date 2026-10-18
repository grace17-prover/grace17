// Command-line G17C compiled-module checker: constructs the foundation,
// replays every dependency and event, and checks the final digest.
// Part of the Grace17 proof assistant for mathematics based on set theory.
// Copyright (c) 2026 Grant Passmore.
// Released under the Apache License 2.0. See LICENSE in the repository root.
// Authors: Grant Passmore

use grace17_checkers::admissions::{replay_module, validate_module};
use grace17_checkers::foundation::load_foundation;
use grace17_checkers::support::{fail, parse_json, read_text, Result};
use grace17_checkers::CHECKER_NAME;
use serde_json::Value;
use std::collections::HashMap;
use std::process::ExitCode;

struct Options {
    certificate: String,
    foundation: String,
    dependencies: Vec<String>,
    json: bool,
    fuel: i64,
}

const USAGE: &str = "usage: g17c_check CERTIFICATE --foundation ZFG [--dependency FILE]... [--json] [--fuel STEPS]";

fn parse_arguments() -> std::result::Result<Options, String> {
    let mut certificate = None;
    let mut foundation = None;
    let mut dependencies = Vec::new();
    let mut json = false;
    let mut fuel = grace17_checkers::compute::fuel();
    let mut args = std::env::args().skip(1);
    while let Some(argument) = args.next() {
        match argument.as_str() {
            "--fuel" => match args.next().and_then(|text| text.parse::<i64>().ok()) {
                Some(steps) if steps > 0 => fuel = steps,
                _ => return Err("--fuel must be a positive integer".into()),
            },
            "--foundation" => foundation = args.next(),
            "--dependency" => match args.next() {
                Some(path) => dependencies.push(path),
                None => return Err(USAGE.into()),
            },
            "--json" => json = true,
            "-h" | "--help" => return Err(USAGE.into()),
            other if certificate.is_none() && !other.starts_with("--") => certificate = Some(other.to_string()),
            other => return Err(format!("unexpected argument {other}")),
        }
    }
    match (certificate, foundation) {
        (Some(certificate), Some(foundation)) => Ok(Options { certificate, foundation, dependencies, json, fuel }),
        _ => Err(USAGE.into()),
    }
}

fn run(options: &Options) -> Result<Value> {
    grace17_checkers::compute::set_fuel(options.fuel);
    let mut env = load_foundation(&options.foundation)?;
    let foundation_digest = env.digest.clone();
    let root = parse_json(&read_text(&options.certificate)?)?;
    validate_module(&root)?;
    let mut supplied: HashMap<String, Value> = HashMap::new();
    for path in &options.dependencies {
        let artifact = parse_json(&read_text(path)?)?;
        validate_module(&artifact)?;
        let digest = artifact["digest"].as_str().expect("validated").to_string();
        supplied.insert(digest, artifact);
    }
    let dependencies = root["dependencies"].as_array().expect("validated").clone();
    for dependency in &dependencies {
        let digest = dependency["digest"].as_str().expect("validated");
        let module = dependency["module"].as_str().expect("validated");
        match supplied.get(digest) {
            Some(artifact) if artifact["module"].as_str() == Some(module) => replay_module(&mut env, artifact, &foundation_digest)?,
            _ => return fail(format!("missing dependency artifact {module}")),
        }
    }
    replay_module(&mut env, &root, &foundation_digest)?;
    Ok(serde_json::json!({
        "ok": true,
        "checker": CHECKER_NAME,
        "version": 3,
        "module": root["module"],
        "events": root["events"].as_array().map(Vec::len).unwrap_or(0),
        "theorems": env.theorems.len(),
        "environment": env.digest,
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
    let json = options.json;
    let handle = std::thread::Builder::new()
        .stack_size(512 * 1024 * 1024)
        .spawn(move || run(&options))
        .expect("checker thread");
    match handle.join() {
        Ok(Ok(result)) => {
            if json {
                println!("{result}");
            } else {
                println!("checked {} ({} events)", result["module"].as_str().unwrap_or("?"), result["events"]);
            }
            ExitCode::SUCCESS
        }
        Ok(Err(error)) => {
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
