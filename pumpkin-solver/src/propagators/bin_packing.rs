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

        // NoSum Pruning
        // Read "A Constraint for Bin Packing" by Paul Shaw for details
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

            let packed: i32 = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| context.is_fixed(*item) && context.lower_bound(*item) == j as i32)
                .map(|(idx, _)| self.sizes[idx])
                .sum();

            // If nosum returns true, prune
            if nosum(&sizes, context.lower_bound(&self.loads[j]) - packed, context.upper_bound(&self.loads[j]) - packed) {
                // The bounds of the loads of bin j are part of the reason
                let mut reason = Vec::from([predicate![self.loads[j] >= context.lower_bound(&self.loads[j])], predicate![self.loads[j] <= context.upper_bound(&self.loads[j])]]);

                // Every item packed in bin j are part of the reason
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

        Ok(())
    }
}

// Original algorithm is 1-indexed so this makes indexing kind of annoying
fn nosum(
    sizes: &[i32],
    lower_bound: i32,
    upper_bound: i32
) -> bool {
    if lower_bound <= 0 || upper_bound >= sizes.iter().sum() {
        return false
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

    sum_a < lower_bound
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
        solver.assert_bounds(item4, 2, 2);

        let reason3 = solver.get_reason_int(predicate![item3 != 0]);
        assert_eq!(conjunction!([load1 <= 2]), reason3);

        // For some reason it can't find a reason for predicate [item4 == 2], so we'll just check the bounds
        let reason4 = solver.get_reason_int(predicate![item4 >= 2]);
        let reason4_alt = solver.get_reason_int(predicate![item4 <= 2]);
        assert_eq!(reason4_alt, reason4);
        assert_eq!(conjunction!([load3 >= 8] & [item5 != 2]), reason4);
    }
}
