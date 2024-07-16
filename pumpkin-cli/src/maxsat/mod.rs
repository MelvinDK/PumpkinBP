use std::fs::File;
use std::path::Path;
use std::time::Duration;
pub(crate) mod optimisation;

use optimisation::linear_search::LinearSearch;
use optimisation::optimisation_result::MaxSatOptimisationResult;
use optimisation::optimisation_solver::OptimisationSolver;
use pumpkin_lib::options::SolverOptions;
use pumpkin_lib::termination::TimeBudget;

use crate::result::PumpkinError;

pub(crate) fn wcnf_problem(
    solver_options: SolverOptions,
    time_limit: Option<Duration>,
    instance_path: impl AsRef<Path>,
) -> Result<(), PumpkinError> {
    // todo: parsers were removed?
    todo!()
    // let instance_file = File::open(instance_path)?;
    // let WcnfInstance {
    //     formula: solver,
    //     objective: objective_function,
    //     last_instance_variable,
    // } = parse_wcnf::<SolverDimacsSink>(
    //     instance_file,
    //     SolverArgs::new(learning_options, solver_options),
    // )?;

    // let brancher = solver.default_brancher_over_all_propositional_variables();

    // let mut solver = OptimisationSolver::new(solver, objective_function, LinearSearch::new());

    // let mut termination = time_limit.map(TimeBudget::starting_now);

    // match solver.solve(&mut termination, brancher) {
    //     MaxSatOptimisationResult::Optimal { solution } => {
    //         println!("s OPTIMAL");
    //         println!(
    //             "v {}",
    //             stringify_solution(&solution, last_instance_variable + 1, false)
    //         );
    //     }
    //     MaxSatOptimisationResult::Satisfiable { best_solution } => {
    //         println!("s SATISFIABLE");
    //         println!(
    //             "v {}",
    //             stringify_solution(&best_solution, last_instance_variable + 1, false)
    //         );
    //     }
    //     MaxSatOptimisationResult::Infeasible => {
    //         println!("s UNSATISFIABLE");
    //     }
    //     MaxSatOptimisationResult::Unknown => {
    //         println!("s UNKNOWN");
    //     }
    // }

    // Ok(())
}
