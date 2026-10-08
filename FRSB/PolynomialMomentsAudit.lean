module

public import FRSB.PolynomialMomentCells
public import Lean

@[expose] public section
open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [``FRSB.polynomial_generator_identity,
    ``FRSB.hasDerivAt_finiteCell_polynomialJetField_time,
    ``FRSB.continuous_polynomialJetBCF,
    ``FRSB.tendsto_polynomialMomentSource_integral_of_weak,
    ``FRSB.polynomial_moment_finite_cell_cropped_bound] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on nonstandard axiom {ax}"
#print axioms FRSB.polynomial_moment_finite_cell_cropped_bound
