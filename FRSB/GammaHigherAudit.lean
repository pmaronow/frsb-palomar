module

public import FRSB.GammaHigher
public import Lean

@[expose] public section
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.moment_interval_integral_physical,
    ``FRSB.hasDerivAt_moment_of_continuousAt_CDF,
    ``FRSB.contDiffOn_moment_of_constant_CDF,
    ``FRSB.hasDerivWithinAt_moment_of_continuous_coefficient,
    ``FRSB.GammaSecond_eq_integral,
    ``FRSB.GammaThird_eq_integral,
    ``FRSB.hasDerivAt_GammaSecond_of_constant_CDF,
    ``FRSB.contDiffOn_Gamma_three_of_constant_CDF,
    ``FRSB.hasDerivAt_deriv_deriv_Gamma_of_constant_CDF] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on nonstandard axiom {ax}"
#print axioms FRSB.contDiffOn_Gamma_three_of_constant_CDF
#print axioms FRSB.hasDerivAt_deriv_deriv_Gamma_of_constant_CDF
