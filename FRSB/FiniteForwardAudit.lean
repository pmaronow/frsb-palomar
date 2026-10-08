module

public import FRSB.FiniteForwardEndpoint

@[expose] public section

/-! Audit actual finite optimal-diffusion laws and literal Brownian-action
weights, rejecting every nonstandard axiom in transitive dependencies. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.joint_transitionLaw_of_restricted,
    ``FRSB.historySample_law_of_restricted,
    ``FRSB.finiteHistoryLaw_withDensity,
    ``FRSB.selectedState_forwardScheme_historyLaw,
    ``FRSB.scaledBrownian_historyLaw,
    ``FRSB.selectedState_history_eq_tiltedBrownian,
    ``FRSB.finiteHistoryDensity_forwardScheme_terminal,
    ``FRSB.finiteHistoryDensity_eq_forwardBrownianWeight,
    ``FRSB.selectedState_endpoint_eq_BrownianTilt_finite] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.selectedState_history_eq_tiltedBrownian
#print axioms FRSB.finiteHistoryDensity_eq_forwardBrownianWeight
#print axioms FRSB.selectedState_endpoint_eq_BrownianTilt_finite
