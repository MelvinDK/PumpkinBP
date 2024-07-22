use downcast_rs::impl_downcast;
use downcast_rs::Downcast;

use crate::basic_types::PropagationStatusCP;
use crate::engine::opaque_domain_event::OpaqueDomainEvent;
use crate::engine::propagation::local_id::LocalId;
use crate::engine::propagation::propagation_context::PropagationContext;
use crate::engine::propagation::propagation_context::PropagationContextMut;
#[cfg(doc)]
use crate::engine::propagation::PropagatorConstructor;
#[cfg(doc)]
use crate::engine::propagation::PropagatorConstructorContext;
use crate::engine::Assignments;
#[cfg(doc)]
use crate::engine::ConstraintSatisfactionSolver;
use crate::predicates::Predicate;
use crate::predicates::PropositionalConjunction;
#[cfg(doc)]
use crate::pumpkin_asserts::PUMPKIN_ASSERT_ADVANCED;
#[cfg(doc)]
use crate::pumpkin_asserts::PUMPKIN_ASSERT_EXTREME;

// We need to use this to cast from `Box<dyn Propagator>` to `NogoodPropagator`; rust inherently
// does not allow downcasting from the trait definition to its concrete type.
impl_downcast!(Propagator);

/// All propagators implement the [`Propagator`] trait, with the exception of the
/// clausal propagator. Structs implementing the trait defines the main propagator logic with
/// regards to propagation, detecting conflicts, and providing explanations.
///
/// The only required functions are [`Propagator::debug_propagate_from_scratch`] and
/// [`Propagator::name`], all other functions have default implementations. For initial development,
/// the required functions are enough, but a more mature implementation consider all functions in
/// most cases.
///
/// See the [`crate::engine::cp::propagation`] documentation for more details.
pub trait Propagator: Downcast {
    /// Return the name of the propagator, this is a convenience method that is used for printing.
    fn name(&self) -> &str;

    /// A propagation method that is used to help debugging.
    ///
    /// This method propagates without relying on internal data structures, hence the immutable
    /// &self parameter. It is usually best to implement this propagation method in the simplest
    /// but correct way. When the assert level is set to [`PUMPKIN_ASSERT_ADVANCED`] or
    /// [`PUMPKIN_ASSERT_EXTREME`] (see [`crate::pumpkin_asserts`]) this method will be called
    /// to double check the reasons for failures and propagations that have been reported by
    /// this propagator.
    ///
    /// Propagators are not required to propagate until a fixed point. It will be called again by
    /// the solver until no further propagations happen.
    fn debug_propagate_from_scratch(&self, context: PropagationContextMut) -> PropagationStatusCP;

    /// Propagate method that will be called during search (e.g. in
    /// [`ConstraintSatisfactionSolver::solve`]).
    ///
    /// This method extends the current partial
    /// assignments with inferred domain changes found by the
    /// [`Propagator`]. In case no conflict has been detected it should return
    /// [`Result::Ok`], otherwise it should return a [`Result::Err`] with an [`Inconsistency`] which
    /// contains the reason for the failure; either because a propagation caused an
    /// an empty domain ([`Inconsistency::EmptyDomain`]) or because the logic of the propagator
    /// found the current state to be inconsistent ([`Inconsistency::Conflict`]).
    ///
    /// Note that the failure (explanation) is given as a conjunction of predicates that lead to the
    /// failure
    ///
    /// Propagators are not required to propagate until a fixed point. It will be called
    /// again by the solver until no further propagations happen.
    ///
    /// By default, this function calls [`Propagator::debug_propagate_from_scratch`].
    fn propagate(&mut self, context: PropagationContextMut) -> PropagationStatusCP {
        self.debug_propagate_from_scratch(context)
    }

    /// Called when an event happens to one of the variables the propagator is subscribed to. It
    /// indicates whether the provided event should cause the propagator to be enqueued.
    ///
    /// This can be used to incrementally maintain data structures or perform propagations, and
    /// should only be used for computationally cheap logic. Expensive computation should be
    /// performed in the [`Propagator::propagate()`] method.
    ///
    /// By default the propagator is always enqueued for every event. Not all propagators will
    /// benefit from implementing this, so it is not required to do so.
    ///
    /// Note that the variables and events to which the propagator is subscribed to are determined
    /// upon propagator construction via [`PropagatorConstructor`].
    fn notify(
        &mut self,
        _context: PropagationContext,
        _local_id: LocalId,
        _event: OpaqueDomainEvent,
    ) -> EnqueueDecision {
        EnqueueDecision::Enqueue
    }

    /// Called each time the [`ConstraintSatisfactionSolver`] backtracks, the propagator can then
    /// update its internal data structures given the new variable domains.
    ///
    /// By default this function does nothing.
    fn synchronise(&mut self, _context: &PropagationContext) {}

    /// Returns the priority of the propagator represented as an integer. Lower values mean higher
    /// priority and the priority determines the order in which propagators will be asked to
    /// propagate. It is custom for simpler propagators to have lower priority values.
    ///
    /// By default the priority is set to 3. It is expected that propagator implementations would
    /// set this value to some appropriate value.
    fn priority(&self) -> u32 {
        // setting an arbitrary priority by default
        3
    }

    /// Initialises the propagator without performing propagation. This method is called only once
    /// by the [`ConstraintSatisfactionSolver`] when the propagator is added using
    /// [`ConstraintSatisfactionSolver::add_propagator`].
    ///
    /// The method can be used to detect root-level inconsistencies.
    ///
    /// The solver will call this before any call to [`Propagator::propagate`] is made.
    fn initialise_at_root(
        &mut self,
        _: PropagationContext,
    ) -> Result<(), PropositionalConjunction> {
        Ok(())
    }

    /// A check whether this propagator can detect an inconsistency.
    ///
    /// By implementing this function, if the propagator is reified, it can propagate the
    /// reification literal based on the detected inconsistency. Yet, an implementation is not
    /// needed for correctness, as [`Propagator::propagate`] should still check for
    /// inconsistency as well.
    fn detect_inconsistency(
        &self,
        _context: PropagationContext,
    ) -> Option<PropositionalConjunction> {
        None
    }

    fn lazy_explanation(&mut self, _code: u64, _assignments: &Assignments) -> &[Predicate] {
        panic!(
            "{}",
            format!(
                "Propagator {} does not support lazy explanations.",
                self.name()
            )
        );
    }
}

/// Indicator of what to do when a propagator is notified.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum EnqueueDecision {
    /// The propagator should be enqueued.
    Enqueue,
    /// The propagator should not be enqueued.
    Skip,
}
