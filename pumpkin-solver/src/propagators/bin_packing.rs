
use crate::basic_types::PropagationStatusCP;
use crate::engine::cp::propagation::ReadDomains;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::predicates::PropositionalConjunction;
use crate::variables::IntegerVariable;
use crate::predicate;

#[derive(Clone, Debug)]
pub(crate) struct BinPackingPropagator<ElementVar> {
    loads: Box<[ElementVar]>,
    bins: Box<[ElementVar]>,
    sizes: Box<[i32]>,
}

impl<ElementVar: IntegerVariable> BinPackingPropagator<ElementVar> {
    pub(crate) fn new(loads: Box<[ElementVar]>, bins: Box<[ElementVar]>, sizes: Box<[i32]>) -> Self {
        BinPackingPropagator { loads, bins, sizes }
    }
}

impl<ElementVar: IntegerVariable + 'static> Propagator
    for BinPackingPropagator<ElementVar>
{
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
            let mut reasons = Vec::new();
        
            self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items already packed in bin j
                    packed_sum += self.sizes[idx];

                    // Collect reasons for the lower bound
                    reasons.push(predicate![bin == j as i32]);
                });
        
            context.set_lower_bound(&self.loads[j], packed_sum, PropositionalConjunction::new(reasons))?;
        }

        // Upper Load Maintenance.
        // Upper bound of load in bin j <= total item size of possible set for bin j
        for j in 0..bin_count {
            let mut potential_sum = 0;
            let mut reasons = Vec::new();
        
            self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.contains(*bin, j as i32))
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items that could be packed in bin j
                    potential_sum += self.sizes[idx];

                    // Collect reasons for the upper bound
                    reasons.push(predicate![bin == j as i32]);
                });
        
            context.set_upper_bound(&self.loads[j], potential_sum, PropositionalConjunction::new(reasons))?;
        }

        // Lower Load and Size Coherence.
        // Lower bound of load in bin j >= total size of all items - sum of upper bounds of loads in all other bins
        let total_size: i32 = self.sizes
            .iter()
            .sum();
        let total_upper_bounds: i32 = self.loads
            .iter()
            .map(|l| context.upper_bound(l))
            .sum();
        let mut reasons = Vec::new();
        for load in self.loads.iter() {
            reasons.push(predicate![load >= context.lower_bound(load)]);
        }

        for (idx, load) in self.loads.iter().enumerate() {
            let lower_bound = total_size - total_upper_bounds + context.upper_bound(load);
            let filtered_reasons = reasons
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, &val)| val)
                .collect();

            context.set_lower_bound(load, lower_bound, PropositionalConjunction::new(filtered_reasons))?;
        }

        // Upper Load and Size Coherence.
        // Upper bound of load in bin j <= total size of all items - sum of lower bounds of loads in all other bins
        let total_lower_bounds: i32 = self.loads
            .iter()
            .map(|l| context.lower_bound(l))
            .sum();
        let mut reasons = Vec::new();
        for load in self.loads.iter() {
            reasons.push(predicate![load <= context.upper_bound(load)]);
        }

        for (idx, load) in self.loads.iter().enumerate() {
            let upper_bound = total_size - total_lower_bounds + context.lower_bound(load);
            let filtered_reasons = reasons
                .iter()
                .enumerate()
                .filter(|&(i, _)| i != idx)
                .map(|(_, &val)| val)
                .collect();

            context.set_upper_bound(load, upper_bound, PropositionalConjunction::new(filtered_reasons))?;
        }

        // Single Item Elimination.
        // If adding an item to a bin would exceed the upper bound of that bin, it is eliminated
        for j in 0..bin_count {
            let mut packed_sum = 0;
            let mut reasons = Vec::new();
        
            self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items already packed in bin j
                    packed_sum += self.sizes[idx];

                    // Collect reasons for the removal
                    reasons.push(predicate![bin == j as i32]);
                });
        
            let remaining_space = context.upper_bound(&self.loads[j]) - packed_sum;

            let to_remove: Vec<&ElementVar> = self.bins
                .iter()
                .enumerate()
                .filter(|(idx, bin)| !context.is_fixed(*bin) && context.contains(*bin, j as i32) && self.sizes[*idx] > remaining_space)
                .map(|(_, val)| val)
                .collect();

            for bin in to_remove.iter() {
                context.remove(*bin, j as i32, PropositionalConjunction::new(reasons.clone()))?;
            }
        }

        // Single Item Commitment.
        // If item allocation cannot exceed a bin's lower bound without one of the candidate items, that candidate item must be committed to that bin
        for j in 0..bin_count {
            let candidates: Vec<(usize, &ElementVar)> = self.bins
                .iter()
                .enumerate()
                .filter(|(_, item)| !context.is_fixed(*item) && context.contains(*item, j as i32))
                .collect();

            let total_size: i32 = self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.contains(*bin, j as i32))
                .map(|(idx, _)| self.sizes[idx])
                .sum();
            
            let mut reason = Vec::new();
            self.bins
                .iter()
                .filter(|bin| context.is_fixed(*bin))
                .for_each(|bin| {
                    if context.lower_bound(bin) == j as i32 {
                        reason.push(predicate![bin == j as i32]);
                    } else {
                        reason.push(predicate![bin != j as i32]);
                    }
                });

            for c in 0..candidates.len() {
                let (i, candidate) = candidates[c];
                if total_size - self.sizes[i] < context.lower_bound(&self.loads[j]) {
                    context.post_predicate(predicate![candidate == j as i32], PropositionalConjunction::new(reason))?;
                }
            }
        }


        Ok(())
    }
}