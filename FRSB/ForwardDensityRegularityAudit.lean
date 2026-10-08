module

public import FRSB.ForwardDensityRegularity
public import Lean

@[expose] public section
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.hasDerivAt_parisiForwardDensity_T,
    ``FRSB.continuousOn_parisiForwardDensity_fields,
    ``FRSB.continuousOn_constantMassForwardDensity_fields] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on nonstandard axiom {ax}"
#print axioms FRSB.continuousOn_parisiForwardDensity_fields
