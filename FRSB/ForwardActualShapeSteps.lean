module

public import FRSB.ForwardLeftAtoms
public import FRSB.ForwardShapeSteps
public import FRSB.ForwardShapeConsequences

@[expose] public section

/-! Exact analytical transfers for the actual selected-potential bridge
gauges.  The remaining finite forward law input is a literal heat-step
identity; all regularity and shape data are discharged here. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology
namespace FRSB

def forwardCorrectionDerivativeConstant (β : ℝ) (j : ℕ) : ℝ :=
  negativeLogDerivativeConstant (forwardBridgeRelativeConstant β j) j

lemma forwardCorrectionDerivativeConstant_nonneg (β : ℝ) (j : ℕ) :
    0 ≤ forwardCorrectionDerivativeConstant β j :=
  negativeLogDerivativeConstant_nonneg _ (forwardBridgeRelativeConstant_nonneg β j) j

/-- A genuine finite-law heat-step identity supplies the only probabilistic
input. Smoothness, evenness and all derivative bounds are actual proved
properties of the selected arbitrary-measure bridge gauge. -/
theorem forwardBridgeLeft_heat_shape_transfer (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) (hrt : r ≤ t)
    (hheat : forwardBridgeLeftCorrection β μ t ht =
      forwardHeatCorrection (β ^ 2 * r) (β ^ 2 * t) (forwardBridgeCorrection β μ r hr))
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ r hr) x ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 3 (forwardBridgeLeftCorrection β μ t ht) x ≤ 0 := by
  rw [hheat]
  exact forwardHeatCorrection_third_nonpos (mul_pos (sq_pos_of_ne_zero hβ) hr.1)
    (mul_le_mul_of_nonneg_left hrt (sq_nonneg β))
    (forwardBridgeCorrection β μ r hr) (contDiff_forwardBridgeCorrection β μ r hr)
    (forwardBridgeCorrection_nonneg β μ r hr) (forwardBridgeCorrection_even β μ r hr)
    (forwardCorrectionDerivativeConstant β) (forwardCorrectionDerivativeConstant_nonneg β)
    (fun j y => forwardBridgeCorrection_uniform_derivative_bound β μ r hr (j + 1) (by omega) y)
    hshape x hx

/-- The actual singleton atom update preserves the sign, including the
atom at the terminal time one. -/
theorem forwardBridgeRight_atom_shape_transfer (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ t ht) x ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 3 (forwardBridgeCorrection β μ t ht) x ≤ 0 := by
  have hfun : forwardBridgeCorrection β μ t ht = fun y =>
      forwardBridgeLeftCorrection β μ t ht y + parisiAtomMass μ t ht * parisiPotential β μ (t,y) := by
    funext y
    unfold forwardBridgeLeftCorrection
    ring
  rw [hfun]
  exact forwardAtomUpdate_third_nonpos β hβ μ t ⟨ht.1.le,ht.2⟩
    (forwardBridgeLeftCorrection β μ t ht) (contDiff_forwardBridgeLeftCorrection β μ t ht)
    (parisiAtomMass μ t ht) (parisiAtomMass_nonneg μ t ht) hshape x hx

lemma forwardBridgeCorrection_curvature_nonneg_of_third (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0)
    (x : ℝ) : 0 ≤ iteratedDeriv 2 (forwardBridgeCorrection β μ s hs) x := by
  apply second_derivative_nonneg_of_even_third_nonpos_bounded_slope
    (forwardBridgeCorrection β μ s hs) (contDiff_forwardBridgeCorrection β μ s hs)
    (forwardBridgeCorrection_even β μ s hs) 1
  · intro y
    simpa only [Real.norm_eq_abs] using forwardBridgeCorrection_slope_bound β μ s hs y
  · exact hshape

lemma forwardBridgeLeftCorrection_curvature_nonneg_of_third (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0)
    (x : ℝ) : 0 ≤ iteratedDeriv 2 (forwardBridgeLeftCorrection β μ s hs) x := by
  apply second_derivative_nonneg_of_even_third_nonpos_bounded_slope
    (forwardBridgeLeftCorrection β μ s hs) (contDiff_forwardBridgeLeftCorrection β μ s hs)
    (forwardBridgeLeftCorrection_even β μ s hs) (forwardBridgeLeftDerivativeConstant β 1)
  · intro y
    simpa only [Real.norm_eq_abs, iteratedDeriv_one] using
      forwardBridgeLeftCorrection_uniform_derivative_bound β μ s hs 1 (le_refl _) y
  · exact hshape

/-- Before the first positive atom the left bridge action is independent
of x. This includes an initial atom at zero, so no Gaussian/Brownian
endpoint normalization is assumed for the starting correction. -/
lemma forwardBridgeLeftAction_constant_of_no_positive_mass (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hzero : (μ : Measure Overlap) {t : Overlap | 0 < (t : ℝ) ∧ (t : ℝ) < s} = 0)
    (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeLeftAction β μ s hs path x = forwardBridgeLeftAction β μ s hs path 0 := by
  have hAE : ∀ᵐ t : Overlap ∂(μ : Measure Overlap), ¬(0 < (t : ℝ) ∧ (t : ℝ) < s) := by
    exact ae_iff.mpr (by simpa only [not_not] using hzero)
  apply integral_congr_ae
  filter_upwards [hAE] with t ht
  change (if (t : ℝ) < s then parisiPotential β μ (t, forwardBridgePoint β s hs path x t) else 0) =
    (if (t : ℝ) < s then parisiPotential β μ (t, forwardBridgePoint β s hs path 0 t) else 0)
  split_ifs with hts
  · have hv : (t : ℝ) = 0 := by
      have hn : ¬0 < (t : ℝ) := fun hp => ht ⟨hp,hts⟩
      exact le_antisymm (le_of_not_gt hn) t.property.1
    simp only [forwardBridgePoint, forwardBridgeFraction, hv, zero_div, min_eq_left zero_le_one,
      zero_mul, sub_zero, zero_add]
  · rfl

lemma forwardBridgeLeftCorrection_constant_of_no_positive_mass (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hzero : (μ : Measure Overlap) {t : Overlap | 0 < (t : ℝ) ∧ (t : ℝ) < s} = 0)
    (x : ℝ) : forwardBridgeLeftCorrection β μ s hs x = forwardBridgeLeftCorrection β μ s hs 0 := by
  rw [forwardBridgeLeftCorrection_eq_negativeLog, forwardBridgeLeftCorrection_eq_negativeLog,
    forwardBridgeLeftFactor_eq_integral, forwardBridgeLeftFactor_eq_integral]
  simp_rw [forwardBridgeLeftAction_constant_of_no_positive_mass β μ s hs hzero]

lemma forwardBridgeLeft_third_zero_of_no_positive_mass (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hzero : (μ : Measure Overlap) {t : Overlap | 0 < (t : ℝ) ∧ (t : ℝ) < s} = 0)
    (x : ℝ) : iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x = 0 := by
  have he : forwardBridgeLeftCorrection β μ s hs = fun _ => forwardBridgeLeftCorrection β μ s hs 0 :=
    funext (forwardBridgeLeftCorrection_constant_of_no_positive_mass β μ s hs hzero)
  rw [he]
  simp only [iteratedDeriv_const, ite_eq_right (by norm_num : ¬(3 : ℕ) = 0)]

end FRSB
