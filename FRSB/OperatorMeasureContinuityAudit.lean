module

public import FRSB.OperatorMeasureContinuity

@[expose] public section

/-! Reject transitive nonstandard axioms in the actual weak-measure operator
continuity and its quantitative estimates. -/

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.symmetric_bilinear_polarization,
    ``FRSB.norm_parisiSlabQuadraticOperator_measure_mesh_le,
    ``FRSB.parisiSlabBilinearOperator_measure_mesh_le,
    ``FRSB.tendsto_parisiSlabBilinearOperator_of_tendsto,
    ``FRSB.continuous_parisiSlabBilinearOperator] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.continuous_parisiSlabBilinearOperator
