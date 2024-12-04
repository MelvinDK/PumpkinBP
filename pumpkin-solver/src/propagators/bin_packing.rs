use itertools::Itertools;

use crate::basic_types::PropagationStatusCP;
use crate::conjunction;
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
        let item_count = self.bins.len();

        // Rule 1.
        // Lower bound of load in bin j >= total item size in bin j
        for j in 0..bin_count {
            let mut packed_sum = 0;
            let mut reasons = Vec::new();
        
            self.bins
                .iter()
                .enumerate()
                .filter(|(_, bin)| context.is_fixed(*bin) && context.lower_bound(*bin) == j as i32)
                .for_each(|(idx, bin)| {
                    // Accumulate the size of items packed in bin `j`
                    packed_sum += self.sizes[idx];

                    // Collect reasons for the lower bound
                    reasons.push(predicate![bin == j as i32]);
                });
        
            context.set_lower_bound(&self.loads[j], packed_sum, PropositionalConjunction::new(reasons))?;
        }

        // let mut lbs = vec![0; bin_count];
        // self.bins
        //     .iter()
        //     .enumerate()
        //     .filter(|(_, bin)| context.is_fixed(*bin))
        //     .for_each(|(idx, bin)| {
        //         let j = context.lower_bound(bin);
        //         lbs[j as usize] += self.sizes[idx];
        //     });

        // Rule 2.
        // Upper bound of load in bin j <= total item size of possible set for bin j

        // Rule 3.
        // Lower bound of load in bin j >= total size of all items - sum of upper bounds of loads in all other bins

        // Rule 4.
        // Upper bound of load in bin j <= total size of all items - sum of lower bounds of loads in all other bins

        // Rule 5.
        // If adding an item to a bin would exceed the upper bound of that bin, it is eliminated

        // Rule 6.
        // If item allocation cannot exceed a bin's lower bound without one of the candidate items, that candidate item must be committed to that bin

        Ok(())
    }
}