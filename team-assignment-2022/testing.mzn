include "globals.mzn";

% Parameters
int: num_items = 6;
int: num_bins = 3;

array[1..num_items] of int: weights = [2, 5, 7, 3, 8, 4]; % Weights of items

% Variables
array[1..num_items] of var 1..num_bins: bin_assignment; % Which bin each item is assigned to
array[1..num_bins] of var 0..sum(weights): bin_loads;   % Total load in each bin

% Constraint: Custom bin_packing_load
constraint bin_packing_load(bin_loads, bin_assignment, weights);

% Objective: Minimize the maximum bin load
var int: max_bin_load = max(bin_loads);

solve minimize max_bin_load;

% Output
output [
    "Bin Assignments: ", show(bin_assignment), "\n",
    "Bin Loads: ", show(bin_loads), "\n",
    "Maximum Bin Load: ", show(max_bin_load), "\n"
];
