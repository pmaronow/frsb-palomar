module

public import FRSB.MeasureCellInduction

@[expose] public section

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.finite_closed_interval_induction,
    ``FRSB.backward_scheme_cell_induction] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.backward_scheme_cell_induction
