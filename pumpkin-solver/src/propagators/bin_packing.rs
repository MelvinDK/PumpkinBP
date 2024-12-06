use crate::basic_types::PropagationStatusCP;
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
                .for_each(|(idx, bin)| {
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
            .map(|load| predicate![load <= context.lower_bound(load)])
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

            // Collect every bin that can no longer be packed in bin j
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


        Ok(())
    }
}