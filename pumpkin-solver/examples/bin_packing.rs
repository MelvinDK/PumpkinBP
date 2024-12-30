use std::num::NonZero;
use std::path::PathBuf;

use clap::Parser;
use convert_case::Case;
use drcp_format::Format;
use pumpkin_solver::branching::branchers::autonomous_search::AutonomousSearch;
use pumpkin_solver::branching::branchers::independent_variable_value_brancher::IndependentVariableValueBrancher;
use pumpkin_solver::branching::value_selection::InDomainMin;
use pumpkin_solver::branching::variable_selection::InputOrder;
use pumpkin_solver::branching::variable_selection::Smallest;
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

    // t60_00 [impossible with 20?]
    let capacity = 1000;
    let bin_count = 21;
    let mut sizes = vec![273,263,350,366,474,472,268,269,283,466,347,261,255,273,355,262,292,259,258,430,252,287,299,298,419,445,495,350,439,307,320,366,363,275,395,272,254,272,303,450,251,288,274,269,372,473,298,444,366,414,271,275,370,252,351,410,315,361,252,357,];

    // The unpacked items of t60_00 after some runtime, it is unpackable in 20 bins??
    // let capacity = 1000;
    // let bin_count = 5;
    // let mut sizes = vec![419,372,363,355,350,347,320,292,269,366,275,272];

    // u120_00
    // let capacity = 150;
    // let bin_count = 48;
    // let mut sizes = vec![42,69,67,57,93,90,38,36,45,42,33,79,27,57,44,84,86,92,46,38,85,33,82,73,49,70,59,23,57,72,74,69,33,42,28,46,30,64,29,74,41,49,55,98,80,32,25,38,82,30,35,39,57,84,62,50,55,27,30,36,20,78,47,26,45,41,58,98,91,96,73,84,37,93,91,43,73,85,81,79,71,80,76,83,41,78,70,23,42,87,43,84,60,55,49,78,73,62,36,44,94,69,32,96,70,84,58,78,25,80,58,66,83,24,98,60,42,43,43,39];
   
    // u120_00 modified to have a perfect fit
    // let capacity = 150;
    // let bin_count = 48;
    // let mut sizes = vec![42,69,67,57,93,90,38,36,45,42,33,79,27,57,44,84,86,92,46,38,85,33,82,73,49,70,59,23,57,72,74,69,33,42,28,46,30,64,29,74,41,49,55,98,80,32,25,38,82,30,35,39,57,84,62,50,55,27,30,36,20,78,47,26,45,41,58,98,91,96,73,84,37,93,91,43,73,85,81,79,71,80,76,83,41,78,70,23,42,87,43,84,60,55,49,78,73,62,36,44,94,69,32,96,70,84,58,78,25,80,58,66,83,24,98,60,42,43,43,39,2,3,3,5,7,1,1,1,3,5,8,9,9,11,12,2,22,2,3,3,4,1,3,2];
    
    // u120_08, took about 5 minutes in the original paper, didn't finish in an hour
    // let capacity = 150;
    // let bin_count = 51;
    // let mut sizes = vec![100,22,25,51,95,58,97,30,79,23,53,80,20,65,64,21,26,100,81,98,70,85,92,97,86,71,91,29,63,34,67,23,33,89,94,47,100,37,40,58,73,39,49,79,54,57,98,69,67,49,38,34,96,27,92,82,69,45,69,20,75,97,51,70,29,91,98,77,48,45,43,61,36,82,89,94,26,35,58,58,57,46,44,91,49,52,65,42,33,60,37,57,91,52,95,84,72,75,89,81,67,74,87,60,32,76,85,59,62,39,64,52,88,45,29,88,85,54,40,57];

    // u120_19, don't bother, took original paper 15 hours
    // let capacity = 150;
    // let bin_count = 50;
    // let mut sizes = vec![49,95,38,62,63,97,42,62,100,43,44,77,97,94,68,23,50,36,89,58,97,27,64,65,54,58,24,35,33,63,32,50,58,90,44,50,48,21,72,75,21,74,28,95,77,69,96,24,57,85,72,96,50,83,65,62,99,93,23,77,94,31,50,33,79,73,23,55,44,78,84,66,31,59,97,95,22,76,90,66,29,100,90,92,50,49,47,43,37,40,60,52,54,99,34,46,88,97,85,39,32,51,95,54,99,86,48,90,28,25,86,39,74,26,38,60,41,67,80,33];

    // let capacity = 100;
    // let bin_count = 25;
    // let mut sizes = vec![99,99,96,96,92,92,91,88,87,86,85,76,74,72,69,67,67,62,61,56,52,51,49,46,44,42,40,40,33,33,30,30,29,28,28,27,25,24,23,22,21,20,17,14,13,11,10,7,7,3];

    // let capacity = 10;
    // let bin_count = 3;
    // let mut sizes = vec![6, 1, 4, 6, 1, 3, 3, 5, 1];

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

    // Symmetry breaking constraint, loads of bins are in non-increasing order
    (1..bin_count)
        .for_each(|i| {
            let _ = solver
                .add_constraint(constraints::binary_less_than_or_equals(loads[i as usize], loads[(i - 1) as usize]))
                .with_tag(NonZero::new(1).unwrap())
                .post();
        });

    // Only branch over the bin assignments, not the loads
    let mut brancher = AutonomousSearch::new(
        IndependentVariableValueBrancher::new(
            InputOrder::new(&bins),
            InDomainMin,
    ));

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
