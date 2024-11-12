use super::ConflictResolver;
use crate::basic_types::moving_averages::MovingAverage;
use crate::basic_types::PredicateId;
use crate::basic_types::PredicateIdGenerator;
use crate::branching::Brancher;
use crate::containers::KeyValueHeap;
use crate::containers::StorageKey;
use crate::engine::conflict_analysis::minimisers::Mode;
use crate::engine::conflict_analysis::minimisers::RecursiveMinimiser;
use crate::engine::conflict_analysis::ConflictAnalysisNogoodContext;
use crate::engine::conflict_analysis::LearnedNogood;
use crate::engine::Assignments;
use crate::predicates::Predicate;
use crate::pumpkin_assert_advanced;
use crate::pumpkin_assert_simple;

#[derive(Clone, Debug, Default)]
pub struct ResolutionResolver {
    /// Heap containing the current decision level predicates.
    /// It sorts the predicates based on trail position.
    heap_current_decision_level: KeyValueHeap<PredicateId, u32>,
    /// The generator is used in combination with the heap.
    predicate_id_generator: PredicateIdGenerator,
    /// Vector containing predicates above the current decision level.
    /// The vector may contain duplicates, but will be removed at the end.
    predicates_lower_decision_level: Vec<Predicate>,
    recursive_minimiser: RecursiveMinimiser,
}

impl ConflictResolver for ResolutionResolver {
    fn resolve_conflict(
        &mut self,
        context: &mut ConflictAnalysisNogoodContext,
    ) -> Option<LearnedNogood> {
        self.clean_up();

        // Initialise the data structures with the conflict nogood.
        for predicate in context.get_conflict_nogood().iter() {
            self.add_predicate_to_conflict_nogood(
                *predicate,
                context.assignments,
                context.brancher,
            );
        }
        // Record conflict nogood size statistics.
        let num_initial_conflict_predicates =
            self.heap_current_decision_level.num_nonremoved_elements()
                + self.predicates_lower_decision_level.len();
        context
            .counters
            .learned_clause_statistics
            .average_conflict_size
            .add_term(num_initial_conflict_predicates as u64);

        // Keep refining the conflict nogood until there is only one predicate from the current
        // decision level
        //
        // There is an exception special case:
        // When posting the decision [x = v], it gets decomposed into two decisions ([x >= v] & [x
        // <= v]). In this case there will be two predicates left from the current decision
        // level, and both will be decisions. This is accounted for below.
        while self.heap_current_decision_level.num_nonremoved_elements() > 1 {
            // Replace the predicate from the nogood that has been assigned last on the trail.
            //
            // This is done in two steps:
            // 1) Pop the predicate last assigned on the trail from the nogood.
            let next_predicate = self.pop_predicate_from_conflict_nogood();

            // 2) Add the reason of the next_predicate to the nogood.

            // 2.a) Here we treat the special case: if the next predicate is a decision, this means
            // that we are done with analysis since the only remaining predicate in the heap is the
            // other decision.
            if context.assignments.is_decision_predicate(&next_predicate) {
                // As a simple workaround, we add the currently analysed predicate to set of
                // predicates from the lower predicate level, and stop analysis.
                //
                // Semantic minimisation will ensure the bound predicates get converted into an
                // equality decision predicate.
                while self.heap_current_decision_level.num_nonremoved_elements() != 1 {
                    let predicate = self.pop_predicate_from_conflict_nogood();
                    let predicate_replacement = if context
                        .assignments
                        .is_decision_predicate(&predicate)
                    {
                        predicate
                    } else {
                        // Note that we decompose [x == v] into the two predicates [x >= v] and [x
                        // <= v] and that these have distinct trail entries (where [x >= v] has a
                        // lower trail position than [x <= v])
                        //
                        // However, this can lead to [x <= v] to be processed *before* [x >= v -
                        // y], meaning that these implied predicates should be replaced with their
                        // reason
                        let reason = ConflictAnalysisNogoodContext::get_propagation_reason_simple(
                            predicate,
                            context.assignments,
                            context.reason_store,
                            context.propagators,
                        );
                        pumpkin_assert_simple!(predicate.is_lower_bound_predicate() || predicate.is_not_equal_predicate(), "A non-decision predicate in the nogood should be either a lower-bound or a not-equals predicate");
                        pumpkin_assert_simple!(
                                reason.len() == 1 && reason[0].is_lower_bound_predicate() ,
                                "The reason for the only propagated predicates left on the trail should be lower-bound predicates"
                            );
                        reason[0]
                    };

                    // We push to `predicates_lower_decision_level` since this structure will be
                    // used for creating the final nogood
                    self.predicates_lower_decision_level
                        .push(predicate_replacement);
                }
                // It could be the case that the final predicate in the nogood is implied, in
                // this case we eagerly replace it since the conflict analysis output assumes
                // that a single variable is propagating.
                //
                // For example, let's say we have made the decision [x == v] (which is
                // decomposed into [x >= v] and [x <= v]).
                //
                // Now let's say we have the nogood [[x>= v - 1], [x <= v]], then we have a
                // final element [x >= v - 1] left in the heap which is
                // implied. This could mean that we end up with 2 predicates in
                // the conflict nogood which goes against the 2-watcher scheme so we eagerly
                // replace it here!
                //
                // TODO: This leads to a less general explanation!
                if !context
                    .assignments
                    .is_decision_predicate(&self.peek_predicate_from_conflict_nogood())
                {
                    let predicate = self.peek_predicate_from_conflict_nogood();
                    let reason = ConflictAnalysisNogoodContext::get_propagation_reason_simple(
                        predicate,
                        context.assignments,
                        context.reason_store,
                        context.propagators,
                    );
                    pumpkin_assert_simple!(predicate.is_lower_bound_predicate() , "If the final predicate in the conflict nogood is not a decision predicate then it should be a lower-bound predicate");
                    pumpkin_assert_simple!(
                        reason.len() == 1 && reason[0].is_lower_bound_predicate(),
                        "The reason for the decision predicate should be a lower-bound predicate"
                    );
                    self.replace_predicate_in_conflict_nogood(predicate, reason[0]);
                }

                // The final predicate in the heap will get pushed in `extract_final_nogood`
                self.predicates_lower_decision_level.push(next_predicate);
                break;
            }

            // 2.b) Standard case, get the reason for the predicate and add it to the nogood.
            let reason = ConflictAnalysisNogoodContext::get_propagation_reason_simple(
                next_predicate,
                context.assignments,
                context.reason_store,
                context.propagators,
            );

            for predicate in reason.iter() {
                self.add_predicate_to_conflict_nogood(
                    *predicate,
                    context.assignments,
                    context.brancher,
                );
            }
        }
        Some(self.extract_final_nogood(context))
    }

    fn process(
        &mut self,
        context: &mut ConflictAnalysisNogoodContext,
        learned_nogood: &Option<LearnedNogood>,
    ) -> Result<(), ()> {
        let learned_nogood = learned_nogood.as_ref().expect("Expected nogood");

        context.backtrack(learned_nogood.backjump_level);
        Ok(())
    }
}

impl ResolutionResolver {
    /// Clears all data structures to prepare for the new conflict analysis.
    fn clean_up(&mut self) {
        self.predicates_lower_decision_level.clear();
        self.predicate_id_generator.clear();
        self.heap_current_decision_level.clear();
    }

    fn add_predicate_to_conflict_nogood(
        &mut self,
        predicate: Predicate,
        assignments: &Assignments,
        brancher: &mut dyn Brancher,
    ) {
        let dec_level = assignments
            .get_decision_level_for_predicate(&predicate)
            .unwrap_or_else(|| {
                panic!(
                    "Expected predicate {predicate} to be assigned but bounds were ({}, {})",
                    assignments.get_lower_bound(predicate.get_domain()),
                    assignments.get_upper_bound(predicate.get_domain()),
                )
            });

        // Ignore root level predicates.
        if dec_level == 0 {
            // do nothing
        }
        // We distinguish between predicates from the current decision level and other predicates.
        else if dec_level == assignments.get_decision_level() {
            let predicate_id = self.predicate_id_generator.get_id(predicate);
            // The first time we encounter the predicate, we initialise its value in the heap.
            //
            // Note that if the predicate is already in the heap, no action needs to be taken. It
            // can happen that a predicate is returned multiple times as a reason for other
            // predicates.

            // TODO: could improve the heap structure to be more user-friendly.

            // Here we manually adjust the size of the heap to accommodate new elements.
            while self.heap_current_decision_level.len() <= predicate_id.index() {
                let next_id = PredicateId {
                    id: self.heap_current_decision_level.len() as u32,
                };
                self.heap_current_decision_level.grow(next_id, 0);
                self.heap_current_decision_level.delete_key(next_id);
            }

            // Then we check whether the predicate was not already present in the heap, if this is
            // not the case then we insert it
            if !self
                .heap_current_decision_level
                .is_key_present(predicate_id)
                && *self.heap_current_decision_level.get_value(predicate_id) == 0
            {
                brancher.on_appearance_in_conflict_predicate(predicate);

                let trail_position = assignments.get_trail_position(&predicate).unwrap();

                // The goal is to traverse predicate in reverse order of the trail.
                //
                // However some predicates may share the trail position. For example, if a predicate
                // that was posted to trail resulted in some other predicates being true, then all
                // these predicates would have the same trail position.
                //
                // When considering the predicates in reverse order of the trail, the implicitly set
                // predicates are posted after the explicitly set one, but they all
                // have the same trail position.
                //
                // To remedy this, we make a tie-breaking scheme to prioritise implied predicates
                // over explicit predicates. This is done by assigning explicitly set predicates the
                // value `2 * trail_position`, whereas implied predicates get `2 * trail_position +
                // 1`.
                let heap_value = if assignments.trail[trail_position].predicate == predicate {
                    trail_position * 2
                } else {
                    trail_position * 2 + 1
                };

                // We restore the key and since we know that the value is 0, we can safely
                // increment with `heap_value`
                self.heap_current_decision_level.restore_key(predicate_id);
                self.heap_current_decision_level
                    .increment(predicate_id, heap_value as u32);

                // TODO: Likely not needed, but double check.
                if *self.heap_current_decision_level.get_value(predicate_id)
                    != heap_value.try_into().unwrap()
                {
                    self.heap_current_decision_level.delete_key(predicate_id);
                }
            }
        } else {
            // We do not check for duplicate, we simply add the predicate.
            // Semantic minimisation will later remove duplicates and do other processing.
            self.predicates_lower_decision_level.push(predicate);
        }
    }

    fn pop_predicate_from_conflict_nogood(&mut self) -> Predicate {
        let next_predicate_id = self.heap_current_decision_level.pop_max().unwrap();
        self.predicate_id_generator
            .get_predicate(next_predicate_id)
            .unwrap()
    }

    fn peek_predicate_from_conflict_nogood(&self) -> Predicate {
        let next_predicate_id = self.heap_current_decision_level.peek_max().unwrap().0;
        self.predicate_id_generator
            .get_predicate(*next_predicate_id)
            .unwrap()
    }

    fn replace_predicate_in_conflict_nogood(
        &mut self,
        predicate: Predicate,
        replacement: Predicate,
    ) {
        self.predicate_id_generator
            .replace_predicate(predicate, replacement);
    }

    fn extract_final_nogood(
        &mut self,
        context: &mut ConflictAnalysisNogoodContext,
    ) -> LearnedNogood {
        // The final nogood is composed of the predicates encountered from the lower decision
        // levels, plus the predicate remaining in the heap.

        // First we obtain a semantically minimised nogood.
        //
        // We reuse the vector with lower decision levels for simplicity.
        let last_predicate = self.pop_predicate_from_conflict_nogood();
        self.predicates_lower_decision_level.push(last_predicate);

        // First we minimise the nogood using semantic minimisation to remove duplicates but we
        // avoid equality merging (since some of these literals could potentailly be removed by
        // recursive minimisation)
        let mut clean_nogood: Vec<Predicate> = context.semantic_minimiser.minimise(
            &self.predicates_lower_decision_level,
            context.assignments,
            Mode::DisableEqualityMerging,
        );

        // Then we perform recrusive minimisation to remove the dominated predicates
        self.recursive_minimiser
            .remove_dominated_predicates(&mut clean_nogood, context);

        // We perform a final semantic minimisation call which allows the merging of the equality
        // predicates which remain in the nogood
        clean_nogood = context.semantic_minimiser.minimise(
            &clean_nogood,
            context.assignments,
            Mode::EnableEqualityMerging,
        );

        // Sorting does the trick with placing the correct predicates at the first two positions,
        // however this can be done more efficiently, since we only need the first two positions
        // to be properly sorted.
        //
        // TODO: Do not sort but do a linear scan to find the correct placement of the predicates
        clean_nogood.sort_by_key(|p| context.assignments.get_trail_position(p).unwrap());
        clean_nogood.reverse();
        // The second highest decision level predicate is at position one.
        // This is the backjump level.
        let backjump_level = if clean_nogood.len() > 1 {
            context
                .assignments
                .get_decision_level_for_predicate(&clean_nogood[1])
                .unwrap()
        } else {
            // For unit nogoods, the solver backtracks to the root level.
            0
        };

        pumpkin_assert_advanced!(clean_nogood[1..]
            .iter()
            .all(|p| context.assignments.is_predicate_satisfied(*p)));

        // TODO: asserting predicate may be bumped twice, probably not a problem.
        for predicate in clean_nogood.iter() {
            context
                .brancher
                .on_appearance_in_conflict_predicate(*predicate);
        }

        LearnedNogood {
            backjump_level,
            predicates: clean_nogood,
        }
    }
}
