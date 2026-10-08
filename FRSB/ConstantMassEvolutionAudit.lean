module

public import FRSB.ConstantMassEvolution

@[expose] public section

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.notMem_support_of_cdf_constant,
    ``FRSB.parisiMeasure_open_interval_eq_zero_of_cdf_constant,
    ``FRSB.parisiPotential_coleHopf_of_finite_support,
    ``FRSB.parisiPotential_coleHopf_on_constantCDF,
    ``FRSB.parisiPotential_coleHopf_constant_interval,
    ``FRSB.parisiPotential_exp_heat_on_constant_interval,
    ``FRSB.parisiPotential_heat_on_zeroCDF_interval] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.parisiPotential_coleHopf_constant_interval
#print axioms FRSB.parisiPotential_exp_heat_on_constant_interval
#print axioms FRSB.parisiPotential_heat_on_zeroCDF_interval
