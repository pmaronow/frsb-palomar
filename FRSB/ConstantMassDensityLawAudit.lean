module

public import FRSB.ConstantMassDensityLaw
public import Lean

@[expose] public section
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.kernel_comp_measure_density,
    ``FRSB.selectedState_endpoint_eq_constantMassDensityLaw,
    ``FRSB.forwardBridgeDensity_constantMass_initialLaw_formula,
    ``FRSB.integrable_constantMassDensity_initialLaw_integrand,
    ``FRSB.constantMassDensity_initialLaw_integral_pos,
    ``FRSB.selectedState_initialLaw_zero,
    ``FRSB.forwardBridgeDensity_constantMass_from_zero] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on nonstandard axiom {ax}"
#print axioms FRSB.forwardBridgeDensity_constantMass_initialLaw_formula
