//! lattice-check: verifies a DRAT proof of unsatisfiability.
//!
//!   lattice-check formula.cnf proof.drat [--text | --binary]
//!
//! Prints "s VERIFIED" (exit 0) or "s NOT VERIFIED" (exit 1), then "c stats {json}".

mod drat;

use std::process::ExitCode;

fn main() -> ExitCode {
    let args: Vec<String> = std::env::args().collect();
    let files: Vec<&String> = args[1..].iter().filter(|a| !a.starts_with("--")).collect();
    if files.len() != 2 {
        eprintln!("usage: lattice-check formula.cnf proof.drat [--text | --binary]");
        return ExitCode::from(2);
    }
    let format = if args.iter().any(|a| a == "--text") {
        Some(false)
    } else if args.iter().any(|a| a == "--binary") {
        Some(true)
    } else {
        None
    };
    let t0 = std::time::Instant::now();
    let read = |p: &str| std::fs::read(p).map_err(|e| format!("{p}: {e}"));
    let (cnf, proof) = match (read(files[0]), read(files[1])) {
        (Ok(a), Ok(b)) => (a, b),
        (Err(e), _) | (_, Err(e)) => {
            eprintln!("{e}");
            return ExitCode::from(2);
        }
    };
    let result = drat::check(&cnf, &proof, format);
    let secs = t0.elapsed().as_secs_f64();
    match &result.outcome {
        Ok(()) => println!("s VERIFIED"),
        Err(why) => {
            println!("c {why}");
            println!("s NOT VERIFIED");
        }
    }
    println!(
        "c stats {{\"seconds\": {secs:.3}, \"clauses\": {}, \"lemmas\": {}, \"deletions\": {}, \"ignored_deletions\": {}, \"core_lemmas\": {}, \"rat_checks\": {}, \"binary\": {}}}",
        result.clauses, result.lemmas, result.deletions, result.ignored_deletions, result.core_lemmas, result.rat_checks, result.binary
    );
    if result.outcome.is_ok() {
        ExitCode::SUCCESS
    } else {
        ExitCode::from(1)
    }
}
