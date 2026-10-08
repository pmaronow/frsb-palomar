module

public import FRSB.Optimality

@[expose] public section
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.GammaPrime_pos, ``FRSB.continuousOn_GammaPrime,
      ``FRSB.support_overlap_lt_one, ``FRSB.Gamma_eq_overlap_of_support,
      ``FRSB.GammaPrime_le_one_of_support] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "Unexpected axiom {ax} in {name}"
#print axioms FRSB.Gamma_eq_overlap_of_support
#print axioms FRSB.GammaPrime_le_one_of_support
