module

public import FRSB.ForwardLeftPotential
public import FRSB.CrossingBridgeCurvature
public import FRSB.ForwardPropositionShape

@[expose] public section

/-! Literal right-CDF forward potential and its sharp curvature bounds. -/
noncomputable section
open Set Paper
open scoped ContDiff
namespace FRSB
/-- The actual right CDF gauge, including a singleton at the observation time. -/
def forwardRightPotential (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  parisiCDF μ s * parisiPotential β μ (s,x) - Real.log (forwardBridgeDensity β μ s hs x)

lemma forwardRightPotential_eq_correction_gaussian (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardRightPotential β μ s hs x = forwardBridgeCorrection β μ s hs x -
      Real.log (heatDensity (β ^ 2 * s) x) := by
  have hg := heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) hs.1) x
  unfold forwardRightPotential forwardBridgeDensity forwardBridgeCorrection
  rw [Real.log_mul (mul_pos hg (Real.exp_pos _)).ne' (forwardBridgeFactor_pos β μ s hs x).ne',
    Real.log_mul hg.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

lemma contDiff_forwardRightPotential (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardRightPotential β μ s hs) := by
  have he : forwardRightPotential β μ s hs = fun x => forwardBridgeCorrection β μ s hs x +
      -Real.log (heatDensity (β ^ 2 * s) x) := by
    funext x
    rw [forwardRightPotential_eq_correction_gaussian β hβ μ s hs x]
    ring
  rw [he]
  exact (contDiff_forwardBridgeCorrection β μ s hs).add
    (contDiff_negativeLog_heatDensity _ (mul_pos (sq_pos_of_ne_zero hβ) hs.1))

lemma forwardRightPotential_even (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardRightPotential β μ s hs (-x) = forwardRightPotential β μ s hs x := by
  simp only [forwardRightPotential, forwardBridgeDensity_even, parisiPotential_even β μ s x ⟨hs.1.le,hs.2⟩]

lemma forwardRightPotential_deriv_origin (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : deriv (forwardRightPotential β μ s hs) 0 = 0 := by
  have he : (fun x => forwardRightPotential β μ s hs (-x)) = forwardRightPotential β μ s hs :=
    funext (forwardRightPotential_even β μ s hs)
  have hh := iteratedDeriv_comp_neg 1 (forwardRightPotential β μ s hs) (0 : ℝ)
  rw [he] at hh
  norm_num [smul_eq_mul, iteratedDeriv_one] at hh
  linarith

lemma iteratedDeriv_forwardRightPotential_two (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 2 (forwardRightPotential β μ s hs) x =
      1 / (β ^ 2 * s) + iteratedDeriv 2 (forwardBridgeCorrection β μ s hs) x := by
  have ht : 0 < β ^ 2 * s := mul_pos (sq_pos_of_ne_zero hβ) hs.1
  have he : forwardRightPotential β μ s hs =
      forwardBridgeCorrection β μ s hs + (fun y => -Real.log (heatDensity (β ^ 2 * s) y)) := by
    funext y
    rw [forwardRightPotential_eq_correction_gaussian β hβ μ s hs y]
    rfl
  rw [he, iteratedDeriv_add ((contDiff_forwardBridgeCorrection β μ s hs).of_le (by simp)).contDiffAt
      ((contDiff_negativeLog_heatDensity _ ht).of_le (by simp)).contDiffAt,
    iteratedDeriv_negativeLog_heatDensity_two _ ht]
  ring

lemma iteratedDeriv_forwardRightPotential_three (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 3 (forwardRightPotential β μ s hs) x =
      iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x := by
  have ht : 0 < β ^ 2 * s := mul_pos (sq_pos_of_ne_zero hβ) hs.1
  have he : forwardRightPotential β μ s hs =
      forwardBridgeCorrection β μ s hs + (fun y => -Real.log (heatDensity (β ^ 2 * s) y)) := by
    funext y
    rw [forwardRightPotential_eq_correction_gaussian β hβ μ s hs y]
    rfl
  rw [he, iteratedDeriv_add ((contDiff_forwardBridgeCorrection β μ s hs).of_le (by simp)).contDiffAt
      ((contDiff_negativeLog_heatDensity _ ht).of_le (by simp)).contDiffAt,
    iteratedDeriv_negativeLog_heatDensity_three _ ht, add_zero]

lemma forwardRightPotential_curvature_lower_of_third (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0)
    (x : ℝ) : 1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardRightPotential β μ s hs) x := by
  rw [iteratedDeriv_forwardRightPotential_two β hβ μ s hs x]
  exact le_add_of_nonneg_right (forwardBridgeCorrection_curvature_nonneg_of_third β μ s hs hshape x)

lemma forwardRightPotential_third_nonpos_of_third (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 3 (forwardRightPotential β μ s hs) x ≤ 0 := by
  rw [iteratedDeriv_forwardRightPotential_three β hβ μ s hs x]
  exact hshape x hx

theorem forwardRightPotential_curvature_bounds (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardRightPotential β μ s hs) x ∧
    iteratedDeriv 2 (forwardRightPotential β μ s hs) x ≤ 1 / (β ^ 2 * s) + parisiCDF μ s := by
  rw [iteratedDeriv_forwardRightPotential_two β hβ μ s hs x]
  constructor
  · exact le_add_of_nonneg_right (forwardBridgeCorrection_curvature_nonneg β hβ μ s hs x)
  · exact add_le_add le_rfl (forwardBridgeCorrection_curvature_le_cdf β μ s hs x)

theorem forwardRightPotential_third_nonpos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (forwardRightPotential β μ s hs) x ≤ 0 := by
  rw [iteratedDeriv_forwardRightPotential_three β hβ μ s hs x]
  exact forwardBridgeCorrection_third_nonpos β hβ μ s hs x hx

end FRSB
