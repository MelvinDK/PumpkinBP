use super::Constraint;
use crate::propagators::BinPackingPropagator;
use crate::variables::IntegerVariable;

/// Creates the [`Constraint`] that packs items of non-negative integer sizes in bins with a non-negative integer capacity.
pub fn bin_packing<Var: IntegerVariable + 'static>(
    loads: impl IntoIterator<Item = Var>,
    bins: impl IntoIterator<Item = Var>,
    sizes: impl IntoIterator<Item = i32>,
) -> impl Constraint {
    BinPackingPropagator::new(loads.into_iter().collect(), bins.into_iter().collect(), sizes.into_iter().collect())
}