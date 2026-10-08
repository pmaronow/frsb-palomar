module

public import FRSB.PotentialMeasureContinuity

@[expose] public section

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.parisiPotential_measure_error_bound,
    ``FRSB.tendsto_parisiPotentialMeasureError_of_weak,
    ``FRSB.eventually_uniform_parisiPotential_of_weak,
    ``FRSB.tendstoUniformlyOn_parisiPotential_of_weak] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.tendstoUniformlyOn_parisiPotential_of_weak
