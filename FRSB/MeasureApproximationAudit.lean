module

public import FRSB.MeasureApproximation

@[expose] public section

/-! Check the actual finite-law approximation against the exact universal
target, rejecting any transitive nonstandard theorem axiom. -/

example : FRSB.FiniteAtomicApproximationTarget := FRSB.finite_atomic_approximation

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.measurable_preservingRound,
    ``FRSB.abs_preservingRound_sub_le_mesh,
    ``FRSB.finite_support_preservingMeasure,
    ``FRSB.preservingMeasure_left_mass,
    ``FRSB.preservingMeasure_atom_mass,
    ``FRSB.preservingMeasure_cdf_mass,
    ``FRSB.preservingMeasure_open_interval_mass,
    ``FRSB.tendsto_preservingMeasure,
    ``FRSB.tendsto_preservingMeasure_cdfDistance,
    ``FRSB.finite_atomic_approximation] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.finite_atomic_approximation
