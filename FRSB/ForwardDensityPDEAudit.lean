module

public import FRSB.ForwardDensityPDE
public import Lean

@[expose] public section
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.hasDerivAt_heatDensity_time,
    ``FRSB.hasDerivAt_forwardHeatDensity_time,
    ``FRSB.hasDerivAt_constantMassForwardDensity_time,
    ``FRSB.hasDerivAt_parisiForwardDensity_time,
    ``FRSB.hasDerivAt_forwardBridgeDensity_time] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on nonstandard axiom {ax}"
#print axioms FRSB.hasDerivAt_parisiForwardDensity_time
