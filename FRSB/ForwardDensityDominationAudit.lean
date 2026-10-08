module

public import FRSB.ForwardDensityDomination
public import Lean

@[expose] public section
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.norm_parisiForwardDensity_compact_time_bound,
    ``FRSB.norm_deriv_parisiForwardDensity_compact_time_bound,
    ``FRSB.norm_iteratedDeriv_parisiForwardDensity_two_compact_time_bound,
    ``FRSB.norm_parisiForwardDensityT_compact_time_bound,
    ``FRSB.integrable_forwardDensity_compact_envelope,
    ``FRSB.integrableOn_parisiForwardDensityT] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on nonstandard axiom {ax}"
#print axioms FRSB.norm_parisiForwardDensityT_compact_time_bound
