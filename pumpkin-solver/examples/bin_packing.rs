use std::num::NonZero;
use std::path::PathBuf;

use clap::Parser;
use convert_case::Case;
use drcp_format::Format;
use pumpkin_solver::constraints;
use pumpkin_solver::options::SolverOptions;
use pumpkin_solver::proof::ProofLog;
use pumpkin_solver::results::ProblemSolution;
use pumpkin_solver::results::SatisfactionResult;
use pumpkin_solver::statistics::configure_statistic_logging;
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

    configure_statistic_logging(
        "",
        None,
        Some(Case::Camel),
        None,
    );

    let mut solver = Solver::with_options(SolverOptions {
        proof_log,
        ..Default::default()
    });

    let capacity = 1000;
    let bin_count = 20;
    let mut sizes = vec![273,263,350,366,474,472,268,269,283,466,347,261,255,273,355,262,292,259,258,430,252,287,299,298,419,445,495,350,439,307,320,366,363,275,395,272,254,272,303,450,251,288,274,269,372,473,298,444,366,414,271,275,370,252,351,410,315,361,252,357,];

    // let capacity = 100;
    // let bin_count = 25;
    // let mut sizes = vec![99,99,96,96,92,92,91,88,87,86,85,76,74,72,69,67,67,62,61,56,52,51,49,46,44,42,40,40,33,33,30,30,29,28,28,27,25,24,23,22,21,20,17,14,13,11,10,7,7,3];

    // let capacity = 10;
    // let bin_count = 3;
    // let mut sizes = vec![6, 1, 4, 6, 1, 3, 3, 5, 1];

    // engineStatisticsNumDecisions=12
    // engineStatisticsNumConflicts=0
    // engineStatisticsNumRestarts=0
    // engineStatisticsNumPropagations=74
    // engineStatisticsTimeSpentInSolver=15
    // learnedClauseStatisticsAverageConflictSize=0
    // learnedClauseStatisticsAverageNumberOfRemovedLiteralsRecursive=0
    // learnedClauseStatisticsAverageNumberOfRemovedLiteralsSemantic=0
    // learnedClauseStatisticsNumUnitClausesLearned=0
    // learnedClauseStatisticsAverageLearnedClauseLength=0
    // learnedClauseStatisticsAverageBacktrackAmount=0
    // learnedClauseStatisticsAverageLbd=0

    // let capacity = 100;
    // let bin_count = 5;
    // let mut sizes = vec![1, 40, 4, 19, 3, 17, 9, 22, 20, 23, 27, 72, 2, 23, 1, 1, 18, 15, 63, 12, 99, 9];

    sizes.sort_by(|a, b| b.cmp(a));
    let item_count = sizes.len();

    let loads = (0..bin_count)
        .map(|i| solver.new_named_bounded_integer(0, capacity, format!("load{i}")))
        .collect::<Vec<_>>();

    let bins = (0..item_count)
        .map(|i| solver.new_named_bounded_integer(0, bin_count, format!("item{i}")))
        .collect::<Vec<_>>();

    let _ = solver
        .add_constraint(constraints::bin_packing(loads.clone(), bins.clone(), sizes.clone()))
        .with_tag(NonZero::new(1).unwrap())
        .post();

    let mut brancher = solver.default_brancher();
    match solver.satisfy(&mut brancher, &mut Indefinite) {
        SatisfactionResult::Satisfiable(solution) => {
            for item in 0..item_count {
                let bin_assignment = solution.get_integer_value(bins[item]) as u32;
                print!("{bin_assignment},");
            }
            println!();
            println!();
            println!("verifying");
            for bin in 0..bin_count {
                let size: i32 = (0..item_count).into_iter()
                    .filter(|i| solution.get_integer_value(bins[*i]) == bin)
                    .map(|i| sizes[i])
                    .sum();
                println!("Packed size of bin {bin}: {size},");
            }
            println!();
            println!();
        }
        SatisfactionResult::Unsatisfiable => {
            println!("Problem is unsatisfiable.");
        }
        SatisfactionResult::Unknown => {
            println!("Timeout.");
        }
    }

    solver.log_statistics();
    
}
