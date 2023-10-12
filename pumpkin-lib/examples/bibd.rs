//! See:
//! - https://en.wikipedia.org/wiki/Block_design#Pairwise_balanced_uniform_designs_(2-designs_or_BIBDs)
//! - https://mathworld.wolfram.com/BlockDesign.html

use pumpkin_lib::{
    basic_types::{variables::IntVar, CSPSolverExecutionFlag},
    engine::ConstraintSatisfactionSolver,
    propagators::{IntTimes, IntTimesArgs, LinearLeq, LinearLeqArgs},
};

struct BIBD {
    v: u32,
    b: u32,
    r: u32,
    k: u32,
    l: u32,
}

impl BIBD {
    fn from_args() -> Option<BIBD> {
        let args = std::env::args()
            .skip(1)
            .map(|arg| arg.parse::<u32>())
            .collect::<Result<Vec<u32>, _>>()
            .ok()?;

        if args.len() != 3 {
            return None;
        }

        let v = args[0];
        let k = args[1];
        let l = args[2];

        let r = l * (v - 1) / (k - 1);
        let b = v * r / k;

        Some(Self { v, b, r, k, l })
    }
}

fn main() {
    env_logger::init();

    let Some(bibd) = BIBD::from_args() else {
        eprintln!("Usage: {} <v> <k> <l>", std::env::args().nth(0).unwrap());
        return;
    };

    println!(
        "bibd: (v = {}, b = {}, r = {}, k = {}, l = {}",
        bibd.v, bibd.b, bibd.r, bibd.k, bibd.l
    );

    let mut solver = ConstraintSatisfactionSolver::default();
    let matrix = (0..bibd.v)
        .map(|_| {
            (0..bibd.b)
                .map(|_| solver.create_new_integer_variable(0, 1))
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    let pairwise_product = (0..bibd.v)
        .map(|_| {
            (0..bibd.v)
                .map(|_| {
                    (0..bibd.b)
                        .map(|_| solver.create_new_integer_variable(0, 1))
                        .collect::<Vec<_>>()
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();

    for row in matrix.iter() {
        linear_eq(&mut solver, row, bibd.r as i32);
    }

    for row in transpose(&matrix) {
        linear_eq(&mut solver, &row, bibd.k as i32);
    }

    for r1 in 0..bibd.v as usize {
        for r2 in r1 + 1..bibd.v as usize {
            for col in 0..bibd.b as usize {
                solver.add_propagator::<IntTimes<_, _, _>>(IntTimesArgs {
                    a: matrix[r1][col],
                    b: matrix[r2][col],
                    c: pairwise_product[r1][r2][col],
                });
            }
            linear_leq(&mut solver, &pairwise_product[r1][r2], bibd.l as i32);
        }
    }

    match solver.solve(i64::MAX) {
        CSPSolverExecutionFlag::Feasible => {
            let row_separator = format!("{}+", "+---".repeat(bibd.b as usize));

            for row in matrix.iter() {
                let line = row
                    .iter()
                    .map(|var| {
                        if solver
                            .get_integer_assignments()
                            .get_assigned_value(var.clone())
                            == 1
                        {
                            "| * ".to_string()
                        } else {
                            "|   ".to_string()
                        }
                    })
                    .collect::<String>();

                println!("{row_separator}\n{line}|");
            }

            println!("{row_separator}");
        }

        CSPSolverExecutionFlag::Infeasible => println!("UNSATISFIABLE"),
        CSPSolverExecutionFlag::Timeout => println!("UNKNOWN"),
    }
}

fn linear_leq<Var: IntVar + 'static>(
    solver: &mut ConstraintSatisfactionSolver,
    vars: &[Var],
    c: i32,
) {
    solver.add_propagator::<LinearLeq<_>>(LinearLeqArgs {
        x: vars.iter().cloned().collect(),
        c,
    });
}

fn transpose<T: Clone, Inner: AsRef<[T]>>(matrix: &[Inner]) -> Vec<Vec<T>> {
    let rows = matrix.len();
    let cols = matrix[0].as_ref().len();

    (0..cols)
        .map(|col| {
            (0..rows)
                .map(|row| matrix[row].as_ref()[col].clone())
                .collect()
        })
        .collect()
}

fn linear_eq<Var: IntVar + 'static>(
    solver: &mut ConstraintSatisfactionSolver,
    row: &[Var],
    rhs: i32,
) {
    linear_leq(solver, row, rhs);

    let negated = row.iter().map(|var| var.scaled(-1)).collect::<Vec<_>>();
    linear_leq(solver, &negated, -rhs);
}
