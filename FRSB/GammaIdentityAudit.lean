module

public import FRSB.GammaIdentity

@[expose] public section

/-! Transitive kernel audit for the genuine diffusion Gamma identity. -/
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.Gamma_tail_integral, ``FRSB.Gamma_integral,
      ``FRSB.hasDerivAt_Gamma, ``FRSB.hasDerivWithinAt_Gamma,
      ``FRSB.contDiffOn_Gamma_one] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
#print axioms FRSB.hasDerivAt_Gamma
#print axioms FRSB.hasDerivWithinAt_Gamma
