module

public import FRSB.FiniteSchemeRepresentation

@[expose] public section

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.finiteLawCDF_cell,
    ``FRSB.parisiSchemeMeasure_finiteLawRSBScheme,
    ``FRSB.exists_RSBScheme_of_finite_support,
    ``FRSB.parisiSchemeMeasure_preservingRSBScheme,
    ``FRSB.parisiGradient_finiteLawRSBScheme,
    ``FRSB.parisiPotential_finiteLawRSBScheme] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.parisiSchemeMeasure_finiteLawRSBScheme
#print axioms FRSB.parisiSchemeMeasure_preservingRSBScheme
