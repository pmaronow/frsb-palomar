module

public import FRSB.ForwardDensityObservables

@[expose] public section

/-! Reject nonstandard axioms in the actual arbitrary-measure forward law. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.selectedState_endpoint_eq_bridgeDensity_finite,
    ``FRSB.tendsto_integral_selectedState_of_weak,
    ``FRSB.integral_selectedState_bridgeDensity_continuous,
    ``FRSB.selectedState_endpoint_eq_bridgeDensity,
    ``FRSB.isProbabilityMeasure_forwardDensityMeasure,
    ``FRSB.integral_selectedState_bridgeDensity,
    ``FRSB.integral_forwardBridgeDensity_eq_one,
    ``FRSB.optimalState_endpoint_eq_bridgeDensity,
    ``FRSB.integral_optimalState_bridgeDensity] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.selectedState_endpoint_eq_bridgeDensity
#print axioms FRSB.integral_optimalState_bridgeDensity
#print axioms FRSB.integral_forwardBridgeDensity_eq_one
