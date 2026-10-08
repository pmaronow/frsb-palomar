module

public import FRSB.MinimizerConclusions
public import FRSB.CrossingProposition

@[expose] public section
#print axioms FRSB.fullRSB
#print axioms FRSB.quantitative_atom
#print axioms FRSB.fullRSB_unique
#print axioms FRSB.fullRSB_of_minimizer
#print axioms FRSB.atom_bounds_of_minimizer_support_interval
#print axioms FRSB.minimizer_full_support
#print axioms FRSB.constantMassGammaShape
#print axioms FRSB.crossing_proposition
#print axioms FRSB.crossing_shape
#print axioms FRSB.minimizer_support_eq_Icc_of_max
#print axioms FRSB.minimizer_quotient
#print axioms FRSB.minimizer_moments_smooth
#print axioms FRSB.minimizer_endpoint_regular
#print axioms FRSB.parisiSmoothDensity_total_mass_of_support_interval
#print axioms FRSB.parisiSmoothDensity_atom_normalization_of_support_interval
#print axioms FRSB.positive_derivative_at_zeros_preserves_positive
#print axioms FRSB.nonnegative_derivative_zero_crossing_preserves_positive
#print axioms FRSB.positive_derivative_at_zeros_sign_threshold
#print axioms FRSB.crossing_shape_of_positive_derivative_at_zeros
example : FRSB.FullRSBTarget := FRSB.fullRSB
example : FRSB.QuantitativeAtomTarget := FRSB.quantitative_atom
