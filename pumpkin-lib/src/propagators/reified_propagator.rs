use crate::basic_types::Inconsistency;
use crate::basic_types::PropagationStatusCP;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::EnqueueDecision;
use crate::engine::propagation::LocalId;
use crate::engine::propagation::PropagationContext;
use crate::engine::propagation::PropagationContextMut;
use crate::engine::propagation::Propagator;
use crate::engine::propagation::PropagatorInitialisationContext;
use crate::engine::propagation::ReadDomains;
use crate::engine::DomainEvents;
use crate::predicates::PropositionalConjunction;
use crate::pumpkin_assert_simple;
use crate::variables::Literal;

/// Propagator for the constraint `r -> p`, where `r` is a Boolean literal and `p` is an arbitrary
/// propagator.
///
/// When a propagator is reified, it will only propagate whenever `r` is set to true. However, if
/// the propagator implements [`Propagator::detect_inconsistency`], the result of that method may
/// be used to propagate `r` to false. If that method is not implemented, `r` will never be
/// propagated to false.
pub(crate) struct ReifiedPropagator<WrappedPropagator> {
    propagator: WrappedPropagator,
    reification_literal: Literal,
    /// The inconsistency that is identified by `propagator` during initialisation.
    root_level_inconsistency: Option<PropositionalConjunction>,
    /// The formatted name of the propagator.
    name: String,
    /// The `LocalId` of the reification literal. Is guaranteed to be a larger ID than any of the
    /// registered ids of the wrapped propagator.
    reification_literal_id: LocalId,
}

impl<WrappedPropagator: Propagator> ReifiedPropagator<WrappedPropagator> {
    pub(crate) fn new(propagator: WrappedPropagator, reification_literal: Literal) -> Self {
        let name = format!("Reified({})", propagator.name());
        ReifiedPropagator {
            reification_literal,
            propagator,
            root_level_inconsistency: None,
            name,
            reification_literal_id: LocalId::from(0), /* Place-holder, will be set in
                                                       * `initialise_at_root` */
        }
    }
}

impl<WrappedPropagator: Propagator> Propagator for ReifiedPropagator<WrappedPropagator> {
    fn notify(
        &mut self,
        context: PropagationContext,
        local_id: LocalId,
        event: OpaqueDomainEvent,
    ) -> EnqueueDecision {
        if local_id < self.reification_literal_id {
            let decision = self.propagator.notify(context, local_id, event);
            self.filter_enqueue_decision(context, decision)
        } else {
            pumpkin_assert_simple!(local_id == self.reification_literal_id);
            EnqueueDecision::Enqueue
        }
    }

    fn notify_backtrack(
        &mut self,
        context: &PropagationContext,
        local_id: LocalId,
        event: OpaqueDomainEvent,
    ) {
        if local_id < self.reification_literal_id {
            self.propagator.notify_backtrack(context, local_id, event)
        } else {
            pumpkin_assert_simple!(local_id == self.reification_literal_id);
        }
    }

    fn initialise_at_root(
        &mut self,
        context: &mut PropagatorInitialisationContext,
    ) -> Result<(), PropositionalConjunction> {
        // Since we cannot propagate here, we store a conflict which the wrapped propagator
        // identifies at the root, and propagate the reification literal to false in the
        // `propagate` method.
        if let Err(conjunction) = self.propagator.initialise_at_root(context) {
            self.root_level_inconsistency = Some(conjunction);
        }

        self.reification_literal_id = context.get_next_local_id();

        let _ = context.register(
            self.reification_literal,
            DomainEvents::BOUNDS,
            self.reification_literal_id,
        );

        Ok(())
    }

    fn priority(&self) -> u32 {
        self.propagator.priority()
    }

    fn propagate(&mut self, mut context: PropagationContextMut) -> PropagationStatusCP {
        if let Some(conjunction) = self.root_level_inconsistency.take() {
            context.assign_literal(self.reification_literal, false, conjunction)?;
        }

        self.propagate_reification(&mut context)?;

        if context.is_literal_true(self.reification_literal) {
            context.with_reification(self.reification_literal);

            let result = self.propagator.propagate(context);

            self.map_propagation_status(result)?;
        }

        Ok(())
    }

    fn name(&self) -> &str {
        &self.name
    }

    fn debug_propagate_from_scratch(
        &self,
        mut context: PropagationContextMut,
    ) -> PropagationStatusCP {
        self.propagate_reification(&mut context)?;

        if context.is_literal_true(self.reification_literal) {
            context.with_reification(self.reification_literal);

            let result = self.propagator.debug_propagate_from_scratch(context);

            self.map_propagation_status(result)?;
        }

        Ok(())
    }

    fn synchronise(&mut self, context: &PropagationContext) {
        self.propagator.synchronise(context);
    }
}

impl<Prop> ReifiedPropagator<Prop> {
    fn map_propagation_status(&self, mut status: PropagationStatusCP) -> PropagationStatusCP {
        if let Err(Inconsistency::Conflict {
            ref mut conflict_nogood,
        }) = status
        {
            conflict_nogood.add(self.reification_literal.into());
        }
        status
    }

    fn propagate_reification(&self, context: &mut PropagationContextMut<'_>) -> PropagationStatusCP
    where
        Prop: Propagator,
    {
        if !context.is_literal_fixed(self.reification_literal) {
            if let Some(conjunction) = self.propagator.detect_inconsistency(context.as_readonly()) {
                context.assign_literal(self.reification_literal, false, conjunction)?;
            }
        }

        Ok(())
    }

    fn filter_enqueue_decision(
        &self,
        context: PropagationContext<'_>,
        decision: EnqueueDecision,
    ) -> EnqueueDecision {
        if decision == EnqueueDecision::Enqueue && context.is_literal_true(self.reification_literal)
        {
            EnqueueDecision::Enqueue
        } else {
            EnqueueDecision::Skip
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::basic_types::Inconsistency;
    use crate::conjunction;
    use crate::engine::test_solver::TestSolver;
    use crate::predicate;
    use crate::predicates::Predicate;
    use crate::predicates::PropositionalConjunction;

    #[test]
    fn a_detected_inconsistency_is_given_as_reason_for_propagating_reification_literal_to_false() {
        let mut solver = TestSolver::default();

        let reification_literal = solver.new_literal();
        let a = solver.new_variable(1, 1);
        let b = solver.new_variable(2, 2);

        let triggered_conflict = conjunction!([a == 1] & [b == 2]);
        let t1 = triggered_conflict.clone();
        let t2 = triggered_conflict.clone();

        let _ = solver
            .new_propagator(ReifiedPropagator::new(
                GenericPropagator::new(
                    move |_: PropagationContextMut| Err(t1.clone().into()),
                    move |_: PropagationContext| Some(t2.clone()),
                    |_: &mut PropagatorInitialisationContext| Ok(()),
                ),
                reification_literal,
            ))
            .expect("no conflict");

        assert!(solver.is_literal_false(reification_literal));

        let reason = solver.get_reason_bool(reification_literal, false);
        assert_eq!(reason, &triggered_conflict);
    }

    #[test]
    fn a_true_literal_is_added_to_reason_for_propagation() {
        let mut solver = TestSolver::default();

        let reification_literal = solver.new_literal();
        let var = solver.new_variable(1, 5);

        let mut propagator = solver
            .new_propagator(ReifiedPropagator::new(
                GenericPropagator::new(
                    move |mut ctx: PropagationContextMut| {
                        ctx.set_lower_bound(&var, 3, conjunction!())?;
                        Ok(())
                    },
                    |_: PropagationContext| None,
                    |_: &mut PropagatorInitialisationContext| Ok(()),
                ),
                reification_literal,
            ))
            .expect("no conflict");

        solver.assert_bounds(var, 1, 5);

        let _ = solver.set_literal(reification_literal, true);
        solver.propagate(&mut propagator).expect("no conflict");

        solver.assert_bounds(var, 3, 5);
        let reason = solver.get_reason_int(predicate![var >= 3]);
        assert_eq!(
            reason,
            &PropositionalConjunction::from(Predicate::from(reification_literal))
        );
    }

    #[test]
    fn a_true_literal_is_added_to_a_conflict_conjunction() {
        let mut solver = TestSolver::default();

        let reification_literal = solver.new_literal();
        let _ = solver.set_literal(reification_literal, true);

        let var = solver.new_variable(1, 1);

        let inconsistency = solver
            .new_propagator(ReifiedPropagator::new(
                GenericPropagator::new(
                    move |_: PropagationContextMut| Err(conjunction!([var >= 1]).into()),
                    |_: PropagationContext| None,
                    |_: &mut PropagatorInitialisationContext| Ok(()),
                ),
                reification_literal,
            ))
            .expect_err("eagerly triggered the conflict");

        match inconsistency {
            Inconsistency::Conflict { conflict_nogood } => {
                assert_eq!(
                    conflict_nogood,
                    PropositionalConjunction::from(vec![
                        reification_literal.into(),
                        predicate![var >= 1]
                    ])
                )
            }

            other => panic!("Inconsistency {other:?} is not expected."),
        }
    }

    #[test]
    fn a_root_level_conflict_propagates_reification_literal() {
        let mut solver = TestSolver::default();

        let reification_literal = solver.new_literal();
        let var = solver.new_variable(1, 1);

        let _ = solver
            .new_propagator(ReifiedPropagator::new(
                GenericPropagator::new(
                    |_: PropagationContextMut| Ok(()),
                    |_: PropagationContext| None,
                    move |_: &mut PropagatorInitialisationContext| Err(conjunction!([var >= 0])),
                ),
                reification_literal,
            ))
            .expect("eagerly triggered the conflict");

        assert!(solver.is_literal_false(reification_literal));
    }

    struct GenericPropagator<Propagation, ConsistencyCheck, Init> {
        propagation: Propagation,
        consistency_check: ConsistencyCheck,
        init: Init,
    }

    impl<Propagation, ConsistencyCheck, Init> Propagator
        for GenericPropagator<Propagation, ConsistencyCheck, Init>
    where
        Propagation: Fn(PropagationContextMut) -> PropagationStatusCP + 'static,
        ConsistencyCheck: Fn(PropagationContext) -> Option<PropositionalConjunction> + 'static,
        Init: Fn(&mut PropagatorInitialisationContext) -> Result<(), PropositionalConjunction>
            + 'static,
    {
        fn name(&self) -> &str {
            "Failing Propagator"
        }

        fn debug_propagate_from_scratch(
            &self,
            context: PropagationContextMut,
        ) -> PropagationStatusCP {
            (self.propagation)(context)
        }

        fn detect_inconsistency(
            &self,
            context: PropagationContext,
        ) -> Option<PropositionalConjunction> {
            (self.consistency_check)(context)
        }

        fn initialise_at_root(
            &mut self,
            context: &mut PropagatorInitialisationContext,
        ) -> Result<(), PropositionalConjunction> {
            (self.init)(context)
        }
    }

    impl<Propagation, ConsistencyCheck, Init> GenericPropagator<Propagation, ConsistencyCheck, Init>
    where
        Propagation: Fn(PropagationContextMut) -> PropagationStatusCP,
        ConsistencyCheck: Fn(PropagationContext) -> Option<PropositionalConjunction>,
        Init: Fn(&mut PropagatorInitialisationContext) -> Result<(), PropositionalConjunction>,
    {
        pub(crate) fn new(
            propagation: Propagation,
            consistency_check: ConsistencyCheck,
            init: Init,
        ) -> Self {
            GenericPropagator {
                propagation,
                consistency_check,
                init,
            }
        }
    }
}
