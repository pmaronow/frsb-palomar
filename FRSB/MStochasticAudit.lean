module

public import FRSB.MStochasticL2

@[expose] public section

/-! Reject every nonstandard axiom in the closed arbitrary-measure stochastic identity. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.integral_terminal_martingale_mul_uniformLeftSum,
    ``FRSB.integral_square_known_scaledBrownian_increment,
    ``FRSB.integral_fourth_scaledBrownian_increment,
    ``FRSB.integral_abs_scaledBrownian_cross_remainder,
    ``FRSB.uniform_left_riemann_tendsto,
    ``FRSB.optimalMLeftSum_secondMoment,
    ``FRSB.optimalM_cross_cell_bound,
    ``FRSB.optimalM_cross_sum_bound,
    ``FRSB.tendsto_optimalMLeftSum_L2,
    ``FRSB.tendstoInMeasure_optimalMLeftSum,
    ``FRSB.optimalM_stochastic_identity] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.tendsto_optimalMLeftSum_L2
#print axioms FRSB.optimalM_stochastic_identity
