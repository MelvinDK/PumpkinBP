use std::num::NonZero;
use std::path::PathBuf;

use clap::Parser;
use drcp_format::Format;
use pumpkin_solver::constraints;
use pumpkin_solver::options::SolverOptions;
use pumpkin_solver::proof::ProofLog;
use pumpkin_solver::results::ProblemSolution;
use pumpkin_solver::results::SatisfactionResult;
use pumpkin_solver::termination::Indefinite;
use pumpkin_solver::Solver;

#[derive(Parser)]
struct Cli {
    /// The location of the proof.
    ///
    /// If a location is given, the full proof will be logged there.
    #[arg(short, long)]
    proof: Option<PathBuf>,
}

fn main() {
    let Cli {
        proof: proof_path,
    } = Cli::parse();

    let Ok(proof_log) = proof_path
        .as_ref()
        .map(|path| ProofLog::cp(path, Format::Text, true, true))
        .transpose()
        .map(|proof| proof.unwrap_or_default())
    else {
        eprintln!(
            "Failed to create proof file at {}",
            proof_path.unwrap().display()
        );
        return;
    };

    let mut solver = Solver::with_options(SolverOptions {
        proof_log,
        ..Default::default()
    });

    let c = 10;
    let m = 3;
    let n = 6;
    let sizes = vec![6, 1, 4, 6, 1, 3];
    
    let loads = (0..3)
        .map(|i| solver.new_named_bounded_integer(0, c, format!("load{i}")))
        .collect::<Vec<_>>();

    let bins = (0..n)
        .map(|i| solver.new_named_bounded_integer(0, m, format!("item{i}")))
        .collect::<Vec<_>>();

    let _ = solver
        .add_constraint(constraints::bin_packing(loads.clone(), bins.clone(), sizes.clone()))
        .with_tag(NonZero::new(1).unwrap())
        .post();

    let mut brancher = solver.default_brancher();
    match solver.satisfy(&mut brancher, &mut Indefinite) {
        SatisfactionResult::Satisfiable(solution) => {
            for item in 0..n {
                let bin_assignment = solution.get_integer_value(bins[item]) as u32;
                print!("{bin_assignment},");
            }
        }
        SatisfactionResult::Unsatisfiable => {
            println!("Problem is unsatisfiable.");
        }
        SatisfactionResult::Unknown => {
            println!("Timeout.");
        }
    }
}
