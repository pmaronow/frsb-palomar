module

public import FRSB.BrownianCrossVariance

@[expose] public section

/-! Kernel audit of the actual martingale conditioning and Brownian variance identities. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.integral_known_mul_martingaleIncrement_eq_zero,
    ``FRSB.terminal_martingale_cross_increment,
    ``FRSB.integral_terminal_martingale_mul_uniformLeftSum,
    ``FRSB.integral_square_centered_gaussian,
    ``FRSB.integral_square_scaledBrownian_increment,
    ``FRSB.integral_square_known_scaledBrownian_increment] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.integral_terminal_martingale_mul_uniformLeftSum
#print axioms FRSB.integral_square_known_scaledBrownian_increment
