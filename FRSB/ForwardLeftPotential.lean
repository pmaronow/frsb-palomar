module

public import FRSB.ForwardActualShapeSteps

@[expose] public section

/-! Literal pre-atom forward potential at the observation time, with its
Gaussian curvature separated from the atom-removed bridge correction. -/
noncomputable section
open Set Paper
open scoped ContDiff
namespace FRSB

lemma negativeLog_heatDensity_eq (t : ℝ) (ht : 0 < t) (x : ℝ) :
    -Real.log (heatDensity t x) = Real.log (Real.sqrt (2 * Real.pi * t)) + x ^ 2 / (2 * t) := by
  have hp : 0 < Real.sqrt (2 * Real.pi * t) := by positivity
  unfold heatDensity
  rw [Real.log_mul (inv_ne_zero hp.ne') (Real.exp_pos _).ne', Real.log_inv, Real.log_exp]
  ring

lemma contDiff_negativeLog_heatDensity (t : ℝ) (ht : 0 < t) :
    ContDiff ℝ ∞ (fun x => -Real.log (heatDensity t x)) := by
  have he : (fun x => -Real.log (heatDensity t x)) =
      fun x => Real.log (Real.sqrt (2 * Real.pi * t)) + x ^ 2 / (2 * t) :=
    funext (negativeLog_heatDensity_eq t ht)
  rw [he]
  fun_prop

lemma hasDerivAt_negativeLog_heatDensity (t : ℝ) (ht : 0 < t) (x : ℝ) :
    HasDerivAt (fun y => -Real.log (heatDensity t y)) (x / t) x := by
  have he : (fun y => -Real.log (heatDensity t y)) =
      fun y => Real.log (Real.sqrt (2 * Real.pi * t)) + y ^ 2 / (2 * t) :=
    funext (negativeLog_heatDensity_eq t ht)
  rw [he]
  have hh := (((hasDerivAt_id x).pow 2).div_const (2 * t)).const_add (Real.log (Real.sqrt (2 * Real.pi * t)))
  convert hh using 1
  · rfl
  · norm_num
    field_simp

lemma iteratedDeriv_negativeLog_heatDensity_two (t : ℝ) (ht : 0 < t) (x : ℝ) :
    iteratedDeriv 2 (fun y => -Real.log (heatDensity t y)) x = 1 / t := by
  have he : deriv (fun y => -Real.log (heatDensity t y)) = fun y => y / t :=
    funext (fun y => (hasDerivAt_negativeLog_heatDensity t ht y).deriv)
  rw [show (2 : ℕ) = 1 + 1 by rfl, iteratedDeriv_succ, iteratedDeriv_one, he]
  exact ((hasDerivAt_id x).div_const t).deriv

lemma iteratedDeriv_negativeLog_heatDensity_three (t : ℝ) (ht : 0 < t) (x : ℝ) :
    iteratedDeriv 3 (fun y => -Real.log (heatDensity t y)) x = 0 := by
  have he : iteratedDeriv 2 (fun y => -Real.log (heatDensity t y)) = fun _ => 1 / t :=
    funext (iteratedDeriv_negativeLog_heatDensity_two t ht)
  rw [show (3 : ℕ) = 2 + 1 by rfl, iteratedDeriv_succ, he]
  exact deriv_const x _

/-- The actual mass below s, excluding its singleton atom, is used here. -/
def forwardLeftPotential (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  parisiLeftMass μ s * parisiPotential β μ (s,x) - Real.log (forwardBridgeDensity β μ s hs x)

lemma forwardLeftPotential_eq_correction_gaussian (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardLeftPotential β μ s hs x = forwardBridgeLeftCorrection β μ s hs x -
      Real.log (heatDensity (β ^ 2 * s) x) := by
  have hg := heatDensity_pos (mul_pos (sq_pos_of_ne_zero hβ) hs.1) x
  unfold forwardLeftPotential forwardBridgeDensity forwardBridgeLeftCorrection forwardBridgeCorrection
  rw [Real.log_mul (mul_pos hg (Real.exp_pos _)).ne' (forwardBridgeFactor_pos β μ s hs x).ne',
    Real.log_mul hg.ne' (Real.exp_pos _).ne', Real.log_exp,
    parisiCDF_eq_left_add_atom μ s hs]
  ring

lemma contDiff_forwardLeftPotential (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardLeftPotential β μ s hs) := by
  have he : forwardLeftPotential β μ s hs = fun x => forwardBridgeLeftCorrection β μ s hs x +
      -Real.log (heatDensity (β ^ 2 * s) x) := by
    funext x
    rw [forwardLeftPotential_eq_correction_gaussian β hβ μ s hs x]
    ring
  rw [he]
  exact (contDiff_forwardBridgeLeftCorrection β μ s hs).add
    (contDiff_negativeLog_heatDensity _ (mul_pos (sq_pos_of_ne_zero hβ) hs.1))

lemma forwardLeftPotential_even (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardLeftPotential β μ s hs (-x) = forwardLeftPotential β μ s hs x := by
  simp only [forwardLeftPotential, forwardBridgeDensity_even, parisiPotential_even β μ s x ⟨hs.1.le,hs.2⟩]

lemma forwardLeftPotential_deriv_origin (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : deriv (forwardLeftPotential β μ s hs) 0 = 0 := by
  have he : (fun x => forwardLeftPotential β μ s hs (-x)) = forwardLeftPotential β μ s hs :=
    funext (forwardLeftPotential_even β μ s hs)
  have hh := iteratedDeriv_comp_neg 1 (forwardLeftPotential β μ s hs) (0 : ℝ)
  rw [he] at hh
  norm_num [smul_eq_mul, iteratedDeriv_one] at hh
  linarith

lemma iteratedDeriv_forwardLeftPotential_two (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 2 (forwardLeftPotential β μ s hs) x =
      1 / (β ^ 2 * s) + iteratedDeriv 2 (forwardBridgeLeftCorrection β μ s hs) x := by
  have ht : 0 < β ^ 2 * s := mul_pos (sq_pos_of_ne_zero hβ) hs.1
  have he : forwardLeftPotential β μ s hs =
      forwardBridgeLeftCorrection β μ s hs + (fun y => -Real.log (heatDensity (β ^ 2 * s) y)) := by
    funext y
    rw [forwardLeftPotential_eq_correction_gaussian β hβ μ s hs y]
    rfl
  rw [he, iteratedDeriv_add ((contDiff_forwardBridgeLeftCorrection β μ s hs).of_le (by simp)).contDiffAt
      ((contDiff_negativeLog_heatDensity _ ht).of_le (by simp)).contDiffAt,
    iteratedDeriv_negativeLog_heatDensity_two _ ht]
  ring

lemma iteratedDeriv_forwardLeftPotential_three (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    iteratedDeriv 3 (forwardLeftPotential β μ s hs) x =
      iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x := by
  have ht : 0 < β ^ 2 * s := mul_pos (sq_pos_of_ne_zero hβ) hs.1
  have he : forwardLeftPotential β μ s hs =
      forwardBridgeLeftCorrection β μ s hs + (fun y => -Real.log (heatDensity (β ^ 2 * s) y)) := by
    funext y
    rw [forwardLeftPotential_eq_correction_gaussian β hβ μ s hs y]
    rfl
  rw [he, iteratedDeriv_add ((contDiff_forwardBridgeLeftCorrection β μ s hs).of_le (by simp)).contDiffAt
      ((contDiff_negativeLog_heatDensity _ ht).of_le (by simp)).contDiffAt,
    iteratedDeriv_negativeLog_heatDensity_three _ ht, add_zero]

lemma forwardLeftPotential_curvature_lower_of_third (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0)
    (x : ℝ) : 1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardLeftPotential β μ s hs) x := by
  rw [iteratedDeriv_forwardLeftPotential_two β hβ μ s hs x]
  exact le_add_of_nonneg_right (forwardBridgeLeftCorrection_curvature_nonneg_of_third β μ s hs hshape x)

lemma forwardLeftPotential_third_nonpos_of_third (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 3 (forwardLeftPotential β μ s hs) x ≤ 0 := by
  rw [iteratedDeriv_forwardLeftPotential_three β hβ μ s hs x]
  exact hshape x hx

end FRSB
