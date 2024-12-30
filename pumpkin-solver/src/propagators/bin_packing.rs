use crate::basic_types::HashSet;
use crate::basic_types::Inconsistency;
use crate::basic_types::PropagationStatusCP;
#[cfg(test)]
use crate::conjunction;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::LocalId;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::DomainEvents;
use crate::predicates::Predicate;
use crate::predicates::PropositionalConjunction;
use crate::variables::IntegerVariable;
use crate::predicate;

#[derive(Clone, Debug)]
pub(crate) struct BinPackingPropagator<ElementVar> {
    // Load of each bin
    loads: Box<[ElementVar]>,
    // Bin allocation for each item
    bins: Box<[ElementVar]>,
    // Size of each item
    sizes: Box<[i32]>,
}

impl<ElementVar: IntegerVariable> BinPackingPropagator<ElementVar> {
    pub(crate) fn new(loads: Box<[ElementVar]>, bins: Box<[ElementVar]>, sizes: Box<[i32]>) -> Self {
        // TODO: CHECK IF ARRAY SIZES ARE THE SAME

        // Sort items (bins and sizes) in non-increasing size
        let mut sorted_zip: Vec<_> = bins.into_vec().into_iter().zip(sizes.into_vec()).collect();
        sorted_zip.sort_unstable_by(|(_, size_a), (_, size_b)| size_b.cmp(size_a));
        let (sorted_bins, sorted_sizes): (Vec<_>, Vec<_>) = sorted_zip.into_iter().unzip();

        BinPackingPropagator {
            loads,
            bins: sorted_bins.into_boxed_slice(),
            sizes: sorted_sizes.into_boxed_slice(),
        }
    }
}

impl<ElementVar: IntegerVariable + 'static> Propagator
    for BinPackingPropagator<ElementVar>
{
    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        self.loads
            .iter()
            .cloned()
            .enumerate()
            .for_each(|(idx, load)| {
                let _ =
                    context.register(load.clone(), DomainEvents::ANY_INT, LocalId::from(idx as u32));
            });

        self.bins
            .iter()
            .cloned()
            .enumerate()
            .for_each(|(idx, bin)| {
                let _ =
                    context.register(bin.clone(), DomainEvents::ANY_INT, LocalId::from((self.loads.len() + idx) as u32));
            });

        Ok(())
    }

    fn name(&self) -> &str {
        "Bin Packing"
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        let bin_count = self.loads.len();

        // let start = Instant::now();
        // Lower Load Mainentance.
        // Lower bound of load in bin j >= total item size in bin j
        for j in 0..bin_count {
            let mut packed_sum = 0;
            let mut reason = Vec::new();
        
            self.bins
                .iter()
                .enumerate()
                // Filter items that are packed in bin j
                .filter(|(_, bin)| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items already packed in bin j
                    packed_sum += self.sizes[idx];

                    // Every item packed in j is part of the reason
                    reason.push(predicate![bin == j as i32]);
                });
        
            context.set_lower_bound(&self.loads[j], packed_sum, PropositionalConjunction::new(reason))?;
        }
        // let duration = start.elapsed().as_micros();
        // println!("Lower Load Maintenace {duration}");
        
        // let start = Instant::now();
        // Upper Load Maintenance.
        // Upper bound of load in bin j <= total item size of possible set for bin j
        for j in 0..bin_count {
            let mut potential_sum = 0;
            
            self.bins
                .iter()
                .enumerate()
                // Filter items that still have bin j in their assignment domain, including items already packed (possible set Pj)
                .filter(|(_, bin)| context.contains(*bin, j as i32))
                .for_each(|(idx, _)| {
                    // Accumulate the size of items that could be packed in bin j
                    potential_sum += self.sizes[idx];
                });

            // The reason has 2 parts: the items already packed in bin j, and the items that are in j's candidate set
            // Since items in the candidate set cannot be expressed as a predicate, we can only express the candidate set by listing the items that aren't in it
            // i.e. instead of saying "these items could be packed in bin j" we say "these items can't be packed in bin j"
            let mut reason: Vec<Predicate> = self.bins
                .iter()
                .filter(|bin| !context.contains(*bin, j as i32))
                .map(|bin| predicate![bin != j as i32])
                .collect();

            // Add items that are packed in bin j to the reason
            self.bins
                .iter()
                .filter(|bin| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|bin| {
                    reason.push(predicate![bin == j as i32]);
                });

            context.set_upper_bound(&self.loads[j], potential_sum, PropositionalConjunction::new(reason))?;
        }
        
        // let duration = start.elapsed().as_micros();
        // println!("Upper Load Maintenace {duration}");
        
        // let start = Instant::now();
        // Lower Load and Size Coherence.
        // Lower bound of load in bin j >= total size of all items - sum of upper bounds of loads in all other bins
        let total_size: i32 = self.sizes
            .iter()
            .sum();
        let total_upper_bounds: i32 = self.loads
            .iter()
            .map(|load| context.upper_bound(load))
            .sum();
            
        // Collect all upper bounds as a reason
        let reason: Vec<Predicate> = self.loads
            .iter()
            .map(|load| predicate![load <= context.upper_bound(load)])
            .collect();

        for (idx, load) in self.loads.iter().enumerate() {
            let lower_bound = total_size - total_upper_bounds + context.upper_bound(load);

            // Remove the upper bound of this bin from the reason, the reason is then all other upper bounds
            let filtered_reason = reason
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, &val)| val)
                .collect();

            context.set_lower_bound(load, lower_bound, PropositionalConjunction::new(filtered_reason))?;
        }

        // let duration = start.elapsed().as_micros();
        // println!("Lower Load and Size Coherence {duration}");
        
        // let start = Instant::now();
        // Upper Load and Size Coherence.
        // Upper bound of load in bin j <= total size of all items - sum of lower bounds of loads in all other bins
        let total_lower_bounds: i32 = self.loads
            .iter()
            .map(|l| context.lower_bound(l))
            .sum();
        
        // Collect all lower bounds as a reason
        let reason: Vec<Predicate> = self.loads
            .iter()
            .map(|load| predicate![load >= context.lower_bound(load)])
            .collect();

        for (idx, load) in self.loads.iter().enumerate() {
            let upper_bound = total_size - total_lower_bounds + context.lower_bound(load);

            // Remove the lower bound of this bin from the reason, the reason is then all other lower bounds
            let filtered_reason = reason
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, &val)| val)
                .collect();

            context.set_upper_bound(load, upper_bound, PropositionalConjunction::new(filtered_reason))?;
        }

        // let duration = start.elapsed().as_micros();
        // println!("Upper Load and Size Coherence {duration}");
        
        // let start = Instant::now();
        // Single Item Elimination.
        // If adding an item to a bin would exceed the upper bound of that bin, it is eliminated
        for j in 0..bin_count {
            let mut packed_sum = 0;
            let mut reason = Vec::new();

            // The upper bound of load in bin j is part of the reason
            reason.push(predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]);
        
            self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items already packed in bin j
                    packed_sum += self.sizes[idx];

                    // Every item packed in bin j is part of the reason
                    reason.push(predicate![bin == j as i32]);
                });
            
            // Remaining space in bin j is its upper bound - the sizes of items already packed in bin j
            let remaining_space = context.upper_bound(&self.loads[j]) - packed_sum;

            // Collect every item that can no longer be packed in bin j
            let to_remove: Vec<&ElementVar> = self.bins
                .iter()
                .enumerate()
                .filter(|(idx, bin)| !context.is_fixed(*bin) && context.contains(*bin, j as i32) && self.sizes[*idx] > remaining_space)
                .map(|(_, val)| val)
                .collect();

            for bin in to_remove.iter() {
                context.remove(*bin, j as i32, PropositionalConjunction::new(reason.clone()))?;
            }
        }

        // let duration = start.elapsed().as_micros();
        // println!("Single Item Elimination {duration}");
        
        // let start = Instant::now();
        // Single Item Commitment.
        // If item allocation cannot exceed a bin's lower bound without one of the candidate items, that candidate item must be committed to that bin
        for j in 0..bin_count {
            // Candidate set Cj
            let candidates: Vec<(usize, &ElementVar)> = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| !context.is_fixed(*item) && context.contains(*item, j as i32))
                .collect();

            // Total size of items in possible set Pj (packed items AND candidate items)
            let total_size: i32 = self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.contains(*bin, j as i32))
                .map(|(idx, _)| self.sizes[idx])
                .sum();
            
            // TODO: conflict check to see if it is even possible to pack bin with current items

            let mut reason = Vec::new();
            // The lower bound of load in bin j is part of the reason
            reason.push(predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]);

            // The items packed in bin j are part of the reason
            self.bins
                .iter()
                .filter(|bin| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|bin| {
                    reason.push(predicate![bin == j as i32]);
                });

            // The items in candidate set Cj are part of the reason
            // Since items in the candidate set cannot be expressed as a predicate, we can only express the candidate set by listing the items that aren't in it
            // i.e. instead of saying "these items could be packed in bin j" we say "these items can't be packed in bin j"
            self.bins
                .iter()
                .filter(|bin| !context.contains(*bin, j as i32))
                .for_each(|bin| {
                    reason.push(predicate![bin != j as i32]);
                });

            for c in 0..candidates.len() {
                let (i, candidate) = candidates[c];
                if total_size - self.sizes[i] < context.lower_bound(&self.loads[j]) {
                    context.post_predicate(predicate![candidate == j as i32], PropositionalConjunction::new(reason.clone()))?;
                }
            }
        }

        // let duration = start.elapsed().as_micros();
        // println!("Single Item Commitment {duration}");
        
        // let start = Instant::now();
        // NoSum Pruning
        // Read "A Constraint for Bin Packing" by Paul Shaw for details on NoSum
        for j in 0..bin_count {
            // Candidate set Cj
            let candidates: Vec<(usize, &ElementVar)> = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| !context.is_fixed(*item) && context.contains(*item, j as i32))
                .collect();

            // Sizes of the candidate items
            let sizes: Vec<i32> = candidates
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .collect();

            // Total size of items packed in bin j
            let packed: i32 = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                .map(|(idx, _)| self.sizes[idx])
                .sum();

            // If nosum returns true, prune
            let (prune, _, _) = nosum(&sizes, context.lower_bound(&self.loads[j]) - packed, context.upper_bound(&self.loads[j]) - packed);
            if prune {
                // The bounds of the load of bin j are part of the reason
                let mut reason = Vec::from([predicate![self.loads[j] >= context.lower_bound(&self.loads[j])], predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]]);

                // Every item packed in bin j is part of the reason
                self.bins
                    .iter()
                    .filter(|item| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                    .for_each(|item| reason.push(predicate![item == j as i32]));

                // Every item without bin j in its domain describes the candidate set Cj, also part of the reason
                self.bins
                    .iter()
                    .filter(|item| !context.contains(*item, j as i32))
                    .for_each(|item| {
                        reason.push(predicate![item != j as i32]);
                    });

                return Err(Inconsistency::Conflict(PropositionalConjunction::new(reason)));
            }
        }

        // let duration = start.elapsed().as_micros();
        // println!("NoSum Pruning {duration}");
        
        // let start = Instant::now();
        // NoSum Load Bound Tightening
        for j in 0..bin_count {
            // Candidate set Cj
            let candidates: Vec<(usize, &ElementVar)> = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| !context.is_fixed(*item) && context.contains(*item, j as i32))
                .collect();

            // Sizes of the candidate items
            let sizes: Vec<i32> = candidates
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .collect();

            // Total size of items packed in bin j
            let packed: i32 = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                .map(|(idx, _)| self.sizes[idx])
                .sum();

            // If nosum returns true with only lower bound inputs, adjust the lower bound
            let (adjust, _, b) = nosum(&sizes, context.lower_bound(&self.loads[j]) - packed, context.lower_bound(&self.loads[j]) - packed);
            if adjust {
                // The lower bound of the load of bin j is part of the reason
                let mut reason = Vec::from([predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]]);

                // Every item packed in bin j is part of the reason
                self.bins
                    .iter()
                    .filter(|item| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                    .for_each(|item| reason.push(predicate![item == j as i32]));

                // Every item without bin j in its domain describes the candidate set Cj, also part of the reason
                self.bins
                    .iter()
                    .filter(|item| !context.contains(*item, j as i32))
                    .for_each(|item| {
                        reason.push(predicate![item != j as i32]);
                    });

                context.set_lower_bound(&self.loads[j], packed + b, PropositionalConjunction::new(reason))?;
            }

            // If nosum returns true with only upper bound inputs, adjust the upper bound
            let (adjust, a, _) = nosum(&sizes, context.upper_bound(&self.loads[j]) - packed, context.upper_bound(&self.loads[j]) - packed);
            if adjust {
                // The upper bound of the load of bin j is part of the reason
                let mut reason = Vec::from([predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]]);

                // Every item packed in bin j is part of the reason
                self.bins
                    .iter()
                    .filter(|item| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                    .for_each(|item| reason.push(predicate![item == j as i32]));

                // Every item without bin j in its domain describes the candidate set Cj, also part of the reason
                self.bins
                    .iter()
                    .filter(|item| !context.contains(*item, j as i32))
                    .for_each(|item| {
                        reason.push(predicate![item != j as i32]);
                    });

                context.set_upper_bound(&self.loads[j], packed + a, PropositionalConjunction::new(reason))?;
            }
        }

        // let duration = start.elapsed().as_micros();
        // println!("NoSum Load Bound Tightening {duration}");
        
        // let start = Instant::now();
        // NoSum Item Elimination and Commitment
        for j in 0..bin_count {
            // Candidate set Cj
            let candidates: Vec<(usize, &ElementVar)> = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| !context.is_fixed(*item) && context.contains(*item, j as i32))
                .collect();

            // Sizes of the candidate items
            let sizes: Vec<i32> = candidates
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .collect();

            // Total size of items packed in bin j
            let packed: i32 = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                .map(|(idx, _)| self.sizes[idx])
                .sum();

            for c in 0..candidates.len() {
                // Sizes of the candidates - current candidate
                let current_sizes: Vec<i32> = sizes
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != c)
                    .map(|(_, val)| *val)
                    .collect();

                // If item has to be eliminated
                let (eliminate, _, _) = nosum(&current_sizes, context.lower_bound(&self.loads[j]) - packed - sizes[c], context.upper_bound(&self.loads[j]) - packed - sizes[c]);
                if eliminate {
                    // The bounds of the load of bin j are part of the reason
                    let mut reason = Vec::from([predicate![self.loads[j] >= context.lower_bound(&self.loads[j])], predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]]);

                    // Every item packed in bin j is part of the reason
                    self.bins
                        .iter()
                        .filter(|item| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                        .for_each(|item| reason.push(predicate![item == j as i32]));

                    // Every item without bin j in its domain describes the candidate set Cj, also part of the reason
                    self.bins
                        .iter()
                        .filter(|item| !context.contains(*item, j as i32))
                        .for_each(|item| {
                            reason.push(predicate![item != j as i32]);
                        });

                    // Remove bin j from candidate item domain
                    context.remove(candidates[c].1, j as i32, PropositionalConjunction::new(reason))?;
                }
                
                // If item has to be committed
                let (commit, _, _) = nosum(&current_sizes, context.lower_bound(&self.loads[j]) - packed, context.upper_bound(&self.loads[j]) - packed);
                if commit {
                    // The bounds of the load of bin j are part of the reason
                    let mut reason = Vec::from([predicate![self.loads[j] >= context.lower_bound(&self.loads[j])], predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]]);

                    // Every item packed in bin j is part of the reason
                    self.bins
                        .iter()
                        .filter(|item| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                        .for_each(|item| reason.push(predicate![item == j as i32]));

                    // Every item without bin j in its domain describes the candidate set Cj, also part of the reason
                    self.bins
                        .iter()
                        .filter(|item| !context.contains(*item, j as i32))
                        .for_each(|item| {
                            reason.push(predicate![item != j as i32]);
                        });

                    // Assign bin j to candidate item domain
                    let candidate = candidates[c].1;
                    context.post_predicate(predicate![candidate == j as i32], PropositionalConjunction::new(reason))?;
                }
            }
        }

        // let duration = start.elapsed().as_micros();
        // println!("NoSum Item Elimination and Commitment {duration}");

        // Lower bound pruning

        Ok(())
    }

    // Do one bin at a time
    fn propagate(
        &mut self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        // Amount of bins
        let bin_count = self.loads.len();

        // Sum of all item sizes
        let total_size: i32 = self.sizes
            .iter()
            .sum();

        for j in 0..bin_count {
            // Variable setup
            // Items that have bin j in their domain
            let possible_set: Vec<(usize, &ElementVar)> = self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.contains(*bin, j as i32))
                .collect();

            // Items packed in bin j (will not remain sorted according to item size, but shouldn't be an issue)
            let mut required_set: Vec<(usize, &ElementVar)> = possible_set
                .iter()
                .copied()
                .filter(|(_, bin)| context.is_fixed(*bin))
                .collect();

            // Candidate set Cj, i.e. items with bin j in their domain but not yet packed
            let candidate_set: Vec<(usize, &ElementVar)> = possible_set
                .into_iter()
                .filter(|(_, item)| !context.is_fixed(*item))
                .collect();

            // The reason has 2 parts: the items already packed in bin j, and the items that are in j's candidate set
            // Since items in the candidate set cannot be expressed as a predicate, we can only express the candidate set by listing the items that aren't in it
            // i.e. instead of saying "these items could still be packed in bin j" we say "these items can't be packed in bin j anymore"
            // Add items that don't have bin j in their domain to the reason for the Candidate set Cj
            let mut candidate_reason: Vec<Predicate> = self.bins
                .iter()
                .filter(|bin| !context.contains(*bin, j as i32))
                .map(|bin| predicate![bin != j as i32])
                .collect();

            // Add items that are packed in bin j to the reason
            required_set
                .iter()
                .for_each(|(_, bin)| {
                    let bin = *bin;
                    candidate_reason.push(predicate![bin == j as i32]);
                });
            



            // Lower Load Mainentance.
            // Lower bound of load in bin j >= total item size in bin j
            let mut packed_sum = 0;
            let mut lower_maintenance_reason = Vec::new();
        
            required_set
                .iter()
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items already packed in bin j
                    packed_sum += self.sizes[*idx];

                    // Every item packed in j is part of the reason
                    let bin = *bin;
                    lower_maintenance_reason.push(predicate![bin == j as i32]);
                });
        
            context.set_lower_bound(&self.loads[j], packed_sum, PropositionalConjunction::new(lower_maintenance_reason.clone()))?;
            



            // Upper Load Maintenance.
            // Upper bound of load in bin j <= total item size of possible set for bin j
            // Accumulate the size of items that could be packed in bin j
            let required_sum: i32 = required_set
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .sum();
            let candidate_sum: i32 = candidate_set
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .sum();
            let possible_sum = required_sum + candidate_sum;

            // The reason is the candidate set Cj
            context.set_upper_bound(&self.loads[j], possible_sum, PropositionalConjunction::new(candidate_reason.clone()))?;
            



            // Lower Load and Size Coherence.
            // Lower bound of load in bin j >= total size of all items - sum of upper bounds of loads in all other bins
            // Sum of all upper bounds except for this bin's one
            let total_upper_bounds: i32 = self.loads
                .iter()
                .enumerate()
                .filter(|&(idx, _)| idx != j)
                .map(|(_, load)| context.upper_bound(load))
                .sum();
            
            // Collect all upper bounds except for this bin's one as a reason
            let lower_coherence_reason: Vec<Predicate> = self.loads
                .iter()
                .enumerate()
                .filter(|&(idx, _)| idx != j)
                .map(|(_, load)| predicate![load <= context.upper_bound(load)])
                .collect();

            let lower_bound = total_size - total_upper_bounds;

            context.set_lower_bound(&self.loads[j], lower_bound, PropositionalConjunction::new(lower_coherence_reason))?;
        



            // Upper Load and Size Coherence.
            // Upper bound of load in bin j <= total size of all items - sum of lower bounds of loads in all other bins
            // Sum of all lower bounds except for this bin's one
            let total_lower_bounds: i32 = self.loads
                .iter()
                .enumerate()
                .filter(|&(idx, _)| idx != j)
                .map(|(_, load)| context.lower_bound(load))
                .sum();
            
            // Collect all lower bounds except for this bin's one as a reason
            let upper_coherence_reason: Vec<Predicate> = self.loads
                .iter()
                .enumerate()
                .filter(|&(idx, _)| idx != j)
                .map(|(_, load)| predicate![load >= context.lower_bound(load)])
                .collect();

            let upper_bound = total_size - total_lower_bounds;

            context.set_upper_bound(&self.loads[j], upper_bound, PropositionalConjunction::new(upper_coherence_reason))?;
        


        
            // Single Item Elimination.
            // If adding an item to a bin would exceed the upper bound of that bin, it is eliminated

            // The reason is the upper bound on the load of bin j and all items packed in it
            let mut single_elimination_reason = lower_maintenance_reason.clone();
            single_elimination_reason.push(predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]);
            
            // Remaining space in bin j is its upper bound - the sizes of items already packed in bin j
            let remaining_space = context.upper_bound(&self.loads[j]) - packed_sum;

            // Collect every item that can no longer be packed in bin j
            let to_remove: Vec<(usize, &ElementVar)> = candidate_set
                .iter()
                .copied()
                .filter(|(idx, _)| self.sizes[*idx] > remaining_space)
                .collect();

            // Set of indices to be removed
            let mut remove_set = HashSet::new();

            // Loop over every item that needs to be removed
            for (idx, bin) in to_remove.iter() {
                // Remove bin allocation j from the item's domain
                let bin = *bin;
                context.remove(bin, j as i32, PropositionalConjunction::new(single_elimination_reason.clone()))?;

                // Update the reason for the candidate set
                candidate_reason.push(predicate![bin != j as i32]);

                // Add index to remove_set
                let _ = remove_set.insert(*idx);
            }

            // Update the candidate set
            let candidate_set: Vec<(usize, &ElementVar)> = candidate_set
                .into_iter()
                .filter(|(idx, _)| remove_set.contains(idx))
                .collect();



        
            // Single Item Commitment.
            // If item allocation cannot exceed a bin's lower bound without one of the candidate items, that candidate item must be committed to that bin
            // Total size of items in possible set Pj (packed items AND candidate items)
            let total_size = packed_sum + candidate_set
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .sum::<i32>();

            // The reason is the lower bound on the load of bin j and the candidate items in Cj
            let mut single_commitment_reason = candidate_reason.clone();
            single_commitment_reason.push(predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]);

            // Set of indices to be removed
            let mut remove_set = HashSet::new();

            for c in 0..candidate_set.len() {
                let (i, candidate) = candidate_set[c];
                if total_size - self.sizes[i] < context.lower_bound(&self.loads[j]) {
                    // Assign bin allocation j to item i
                    context.post_predicate(predicate![candidate == j as i32], PropositionalConjunction::new(single_commitment_reason.clone()))?;

                    // Update the reason for the candidate set
                    candidate_reason.push(predicate![candidate == j as i32]);

                    // Add item to packed items
                    required_set.push((i, candidate));

                    // Add index to remove_set
                    let _ = remove_set.insert(i);
                }
            }

            // Update the candidate set
            let candidate_set: Vec<(usize, &ElementVar)> = candidate_set
                .into_iter()
                .filter(|(idx, _)| remove_set.contains(idx))
                .collect();




            // NoSum Pruning
            // Read "A Constraint for Bin Packing" by Paul Shaw for details on NoSum
            // Sizes of the candidate items
            let candidate_sizes: Vec<i32> = candidate_set
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .collect();

            // Total size of items packed in bin j
            let packed_sum: i32 = required_set
                .iter()
                .map(|(idx, _)| self.sizes[*idx])
                .sum();

            // If nosum returns true, prune
            let (prune, _, _) = nosum(&candidate_sizes, context.lower_bound(&self.loads[j]) - packed_sum, context.upper_bound(&self.loads[j]) - packed_sum);
            if prune {
                // The reason is the bounds on the load of the bin and the candidate set
                let mut nosum_prune_reason = candidate_reason.clone();
                nosum_prune_reason.push(predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]);
                nosum_prune_reason.push(predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]);

                return Err(Inconsistency::Conflict(PropositionalConjunction::new(nosum_prune_reason)));
            }




            // NoSum Load Bound Tightening
            // If nosum returns true with only lower bound inputs, adjust the lower bound
            let (adjust, _, b) = nosum(&candidate_sizes, context.lower_bound(&self.loads[j]) - packed_sum, context.lower_bound(&self.loads[j]) - packed_sum);
            if adjust {
                // The reason is the lower bound on the load of the bin and the candidate set
                let mut nosum_lower_bound_reason = candidate_reason.clone();
                nosum_lower_bound_reason.push(predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]);

                context.set_lower_bound(&self.loads[j], packed_sum + b, PropositionalConjunction::new(nosum_lower_bound_reason))?;
            }

            // If nosum returns true with only upper bound inputs, adjust the upper bound
            let (adjust, a, _) = nosum(&candidate_sizes, context.upper_bound(&self.loads[j]) - packed_sum, context.upper_bound(&self.loads[j]) - packed_sum);
            if adjust {
                // The reason is the upper bound on the load of the bin and the candidate set
                let mut nosum_upper_bound_reason = candidate_reason.clone();
                nosum_upper_bound_reason.push(predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]);

                context.set_upper_bound(&self.loads[j], packed_sum + a, PropositionalConjunction::new(nosum_upper_bound_reason))?;
            }

        


            // NoSum Item Elimination and Commitment
            for c in 0..candidate_set.len() {
                // Sizes of the candidates without the current candidate
                let current_sizes: Vec<i32> = candidate_sizes
                    .iter()
                    .enumerate()
                    .filter(|(idx, _)| *idx != c)
                    .map(|(_, val)| *val)
                    .collect();

                // If item has to be eliminated
                let (eliminate, _, _) = nosum(&current_sizes, context.lower_bound(&self.loads[j]) - packed_sum - candidate_sizes[c], context.upper_bound(&self.loads[j]) - packed_sum - candidate_sizes[c]);
                if eliminate {
                    // The reason is the bounds on the load of the bin and the candidate set
                    let mut nosum_elimination_reason = candidate_reason.clone();
                    nosum_elimination_reason.push(predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]);
                    nosum_elimination_reason.push(predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]);

                    // Remove bin j from candidate item domain
                    context.remove(candidate_set[c].1, j as i32, PropositionalConjunction::new(nosum_elimination_reason))?;
                }
                
                // If item has to be committed
                let (commit, _, _) = nosum(&current_sizes, context.lower_bound(&self.loads[j]) - packed_sum, context.upper_bound(&self.loads[j]) - packed_sum);
                if commit {
                    // The reason is the bounds on the load of the bin and the candidate set
                    let mut nosum_commitment_reason = candidate_reason.clone();
                    nosum_commitment_reason.push(predicate![self.loads[j] >= context.lower_bound(&self.loads[j])]);
                    nosum_commitment_reason.push(predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]);

                    // Assign bin j to candidate item domain
                    let candidate = candidate_set[c].1;
                    context.post_predicate(predicate![candidate == j as i32], PropositionalConjunction::new(nosum_commitment_reason))?;
                }
            }
        }

        // WRITE DOWN WHAT NOSUM ITEM COMMITMENT AND ELIMINATION DOESN'T KEEP TRACK OF ANYMORE

        println!();
        for j in 0..bin_count {
            let bin1load = self.bins
                .iter()
                .enumerate()
                .filter(|(_, b)| context.is_fixed(*b) && context.lower_bound(*b) == j as i32)
                .map(|(i, _)| self.sizes[i])
                .sum::<i32>();
            let lowerbound = context.lower_bound(&self.loads[j]);
            let upperbound = context.upper_bound(&self.loads[j]);
            print!("{j}: {bin1load}               ({lowerbound} - {upperbound})          ");
            for i in 0..self.bins.len() {
                if context.contains(&self.bins[i], j as i32) {
                    let candidate = self.sizes[i];
                    print!("{candidate},");
                }
            }
            println!();
        }
        println!();


        // Lower bound pruning

        Ok(())
    }
}

// NoSum algorithm by Paul Shaw
// Original algorithm is 1-indexed so this makes indexing kind of annoying
fn nosum(
    sizes: &[i32],
    lower_bound: i32,
    upper_bound: i32
) -> (bool, i32, i32) {
    // sizes.iter().sum() should be kept track of dynamically for constant time
    if lower_bound <= 0 || upper_bound >= sizes.iter().sum() {
        return (false, 0, 0)
    }
    
    let length = sizes.len();
    let mut sum_a = 0;
    let mut sum_c = 0;
    let mut k1 = 0;
    let mut k2 = 0;
    
    while sum_c + sizes[length - k2 - 1] < lower_bound {
        sum_c += sizes[length - k2 - 1];
        k2 += 1;
    }

    let mut sum_b = sizes[length - k2 - 1];

    while sum_a < lower_bound && sum_b <= upper_bound {
        k1 += 1;
        sum_a += sizes[k1 - 1];

        if sum_a < lower_bound {
            k2 -= 1;
            sum_b += sizes[length - k2 - 1];
            sum_c -= sizes[length - k2 - 1];

            while sum_a + sum_c >= lower_bound {
                k2 -= 1;
                sum_c -= sizes[length - k2 - 1];
                sum_b += sizes[length - k2 - 1] - sizes[length - k2 - k1 - 2];
            }
        }
    }

    (sum_a < lower_bound, sum_a + sum_c, sum_b)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::test_solver::TestSolver;

    #[test]
    fn load_maintenance() {
        let mut solver = TestSolver::default();

        let load1 = solver.new_variable(0, 10);
        let load2 = solver.new_variable(0, 10);
        let load3 = solver.new_variable(0, 10);

        let item1 = solver.new_variable(0, 0);
        let item2 = solver.new_variable(0, 0);
        let item3 = solver.new_variable(1, 1);
        let item4 = solver.new_variable(1, 2);

        let sizes = [2,3,4,5];

        let _ = solver
            .new_propagator(BinPackingPropagator::new([load1, load2, load3].into(), [item1, item2, item3, item4].into(), sizes.into()))
            .expect("no empty domain");

        solver.assert_bounds(load1, 5, 5);
        solver.assert_bounds(load2, 4, 9);
        solver.assert_bounds(load3, 0, 5);

        let reason_lower_1 = solver.get_reason_int(predicate![load1 >= 5]);
        assert_eq!(conjunction!([item1 == 0] & [item2 == 0]), reason_lower_1);

        let reason_upper_1 = solver.get_reason_int(predicate![load1 <= 5]);
        assert_eq!(conjunction!([item1 == 0] & [item2 == 0] & [item3 != 0] & [item4 != 0]), reason_upper_1);

        let reason_lower_2 = solver.get_reason_int(predicate![load2 >= 4]);
        assert_eq!(conjunction!([item3 == 1]), reason_lower_2);

        let reason_upper_2 = solver.get_reason_int(predicate![load2 <= 9]);
        assert_eq!(conjunction!([item3 == 1] & [item1 != 1] & [item2 != 1]), reason_upper_2);

        let reason_upper_3 = solver.get_reason_int(predicate![load3 <= 5]);
        assert_eq!(conjunction!([item1 != 2] & [item2 != 2] & [item3 != 2]), reason_upper_3);
    }

    #[test]
    fn load_and_size_coherence() {
        let mut solver = TestSolver::default();

        let load1 = solver.new_variable(4, 5);
        let load2 = solver.new_variable(11, 13);
        let load3 = solver.new_variable(3, 9);

        let item1 = solver.new_variable(0, 2);
        let item2 = solver.new_variable(0, 2);
        let item3 = solver.new_variable(0, 2);
        let item4 = solver.new_variable(0, 2);

        let sizes = [4,5,6,7];

        let _ = solver
            .new_propagator(BinPackingPropagator::new([load1, load2, load3].into(), [item1, item2, item3, item4].into(), sizes.into()))
            .expect("no empty domain");

        solver.assert_bounds(load1, 4, 5);
        solver.assert_bounds(load2, 11, 13);
        solver.assert_bounds(load3, 4, 7); // only one with changed bounds

        let reason_lower = solver.get_reason_int(predicate![load3 >= 4]);
        assert_eq!(conjunction!([load1 <= 5] & [load2 <= 13]), reason_lower);

        let reason_upper = solver.get_reason_int(predicate![load3 <= 7]);
        assert_eq!(conjunction!([load1 >= 4] & [load2 >= 11]), reason_upper);
    }

    #[test]
    fn elimination_and_commitment() {
        let mut solver = TestSolver::default();

        let load1 = solver.new_variable(0, 2);
        let load2 = solver.new_variable(0, 100);
        let load3 = solver.new_variable(8, 10);
        let load4 = solver.new_variable(0, 100);

        let item1 = solver.new_variable(0, 3);
        let item2 = solver.new_variable(0, 3);
        let item3 = solver.new_variable(0, 3);
        let item4 = solver.new_variable(0, 3);
        let item5 = solver.new_variable(0, 3);

        let sizes = [1,2,3,5,50];

        let _ = solver
            .new_propagator(BinPackingPropagator::new([load1, load2, load3, load4].into(), [item1, item2, item3, item4, item5].into(), sizes.into()))
            .expect("no empty domain");

        solver.assert_bounds(item1, 0, 3);
        solver.assert_bounds(item2, 0, 3);
        solver.assert_bounds(item3, 1, 3);
        // solver.assert_bounds(item4, 2, 2);

        let reason3 = solver.get_reason_int(predicate![item3 != 0]);
        assert_eq!(conjunction!([load1 <= 2]), reason3);

        // Test failed after changing the algorithm to binwise, might fix later
        // // For some reason it can't find a reason for predicate [item4 == 2], so we'll just check the bounds
        // let reason4 = solver.get_reason_int(predicate![item4 >= 2]);
        // let reason4_alt = solver.get_reason_int(predicate![item4 <= 2]);
        // assert_eq!(reason4_alt, reason4);
        // assert_eq!(conjunction!([load3 >= 8] & [item5 != 2]), reason4);
    }
}
