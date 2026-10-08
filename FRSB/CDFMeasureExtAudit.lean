module

public import FRSB.CDFMeasureExt

@[expose] public section

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in [
    ``FRSB.parisiCDF_right_continuous,
    ``FRSB.eq_of_parisiCDF_ae_eq,
    ``FRSB.eq_of_parisiCDF_ae_eq_on,
    ``FRSB.eq_of_parisiCDFDistance_eq_zero,
    ``FRSB.eq_of_parisiCDF_tail_integrals_eq_zero] do
    for ax in ← Lean.collectAxioms name do
      unless allowed.contains ax do
        throwError "{name} depends on disallowed axiom {ax}"

#print axioms FRSB.eq_of_parisiCDFDistance_eq_zero
#print axioms FRSB.eq_of_parisiCDF_tail_integrals_eq_zero
