This Repository was made as part of the [Research Project at TUDelft](https://github.com/TU-Delft-CSE/Research-Project) (2024-2025)

The codebase is originally from [Pumpkin](https://github.com/consol-lab/pumpkin)

All the work done for the Research Project is on the bin-packing-dev branch

To run the benchmarks in steelmillslab-2019 or team-assignment-2022, execute the following command:
```
minizinc --solver minizinc/pumpkin.msc steelmillslab-2019/steelmillslab.mzn -d steelmillslab-2019/bench_17_7.dzn -a -s --time-limit 300000
```
Or replace the .mzn or .dzn file with the desired files in those folders.

By default this runs our implementation. To run the decomposition, remove the following files:
```
minizinc/lib/fzn_bin_packing.mzn
minizinc/lib/fzn_bin_packing_load.mzn
```

To run the code with naive explanations, set `naive = true` in line 81 of `pumpkin-solver/src/propagators/bin_packing.rs`
