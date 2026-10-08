module

public import FRSB.ConstantMassItoEndpoint
public import FRSB.ConstantMassBackwardKernel

@[expose] public section

/-! The actual weighted Fourier endpoint identities have no supplied PDE,
transition-law, or stochastic-martingale assumptions. Reject every custom
axiom in their full transitive proof dependencies. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.hasDerivAt_gaussianHeatFlow_variance,
    ``FRSB.hasDerivAt_backwardHeatQuotientDx,
    ``FRSB.backwardHeatQuotient_heat_generator,
    ``FRSB.heatC2Datum_exp_parisiPotential,
    ``FRSB.abs_parisiBackwardQuotientDx_le,
    ``FRSB.cappedBackwardHeatQuotient_ito_continuous,
    ``FRSB.capped_parisiBackwardQuotient_PDE,
    ``FRSB.selectedParisiItoState_constantMass_weighted_interior,
    ``FRSB.selectedParisiItoState_constantMass_weighted,
    ``FRSB.selectedParisiItoState_constantMass_weighted_cos,
    ``FRSB.selectedParisiItoState_constantMass_weighted_sin,
    ``FRSB.parisiBackwardQuotient_eq_kernel_integral] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.selectedParisiItoState_constantMass_weighted_cos
#print axioms FRSB.selectedParisiItoState_constantMass_weighted_sin
#print axioms FRSB.parisiBackwardQuotient_eq_kernel_integral
