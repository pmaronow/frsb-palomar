module

public import FRSB.TerminalAtomCentering
public import FRSB.AtomMomentInequality

@[expose] public section

/-! Positivity and integrability of the actual normalized terminal moments,
and the elementary hyperbolic slope comparisons used in the atom estimate. -/
noncomputable section
open Set Filter MeasureTheory Paper
namespace FRSB

theorem tanh_nonneg_on_halfLine {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  have hm : Monotone Real.tanh := monotone_of_hasDerivAt_nonneg hasDerivAt_tanh
    (fun y => sq_nonneg (sech y))
  simpa only [Real.tanh_zero] using hm hx

theorem tanh_le_id_on_halfLine {x : ℝ} (hx : 0 ≤ x) : Real.tanh x ≤ x := by
  have hm : Monotone (fun y : ℝ => y-Real.tanh y) :=
    monotone_of_hasDerivAt_nonneg (fun y => (hasDerivAt_id y).sub (hasDerivAt_tanh y))
      (fun y => sub_nonneg.mpr (sech_sq_le_one y))
  have h := hm hx
  simpa only [Real.tanh_zero,sub_zero,sub_nonneg] using h

theorem linear_lower_bound_of_curvature (R R' : ℝ → ℝ) (ell : ℝ)
    (hd : ∀ x, HasDerivAt R (R' x) x) (hcurv : ∀ x, ell ≤ R' x)
    (hzero : R 0 = 0) {x : ℝ} (hx : 0 ≤ x) : ell*x ≤ R x := by
  have hm : Monotone (fun y : ℝ => R y-ell*y) :=
    monotone_of_hasDerivAt_nonneg (fun y => (hd y).sub ((hasDerivAt_id y).const_mul ell))
      (fun y => by
        change (0:ℝ) ≤ R' y-ell*1
        simpa only [mul_one] using sub_nonneg.mpr (hcurv y))
  have h := hm hx
  simp only [hzero,mul_zero,sub_zero] at h
  linarith

theorem tanh_lower_bound_of_curvature (R R' : ℝ → ℝ) (ell : ℝ)
    (hell : 0 ≤ ell) (hd : ∀ x, HasDerivAt R (R' x) x)
    (hcurv : ∀ x, ell ≤ R' x) (hzero : R 0 = 0) {x : ℝ} (hx : 0 ≤ x) :
    ell*Real.tanh x ≤ R x :=
  (mul_le_mul_of_nonneg_left (tanh_le_id_on_halfLine hx) hell).trans
    (linear_lower_bound_of_curvature R R' ell hd hcurv hzero hx)

theorem integrable_terminal_crossing_C (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1) :
    Integrable (fun x => sech x^2) (crossingWeightLaw (bridgeCrossingWeight β μ q hq)) := by
  letI := bridgeCrossingWeightLaw_isProbability β hβ μ q hq
  apply (integrable_const (1:ℝ)).mono' (gaussian_continuous_sech.pow 2).aestronglyMeasurable
  exact .of_forall fun x => by
    change ‖sech x^2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact sech_sq_le_one x

theorem integrable_terminal_crossing_B2 (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1) :
    Integrable (fun x => Real.tanh x^2) (crossingWeightLaw (bridgeCrossingWeight β μ q hq)) := by
  letI := bridgeCrossingWeightLaw_isProbability β hβ μ q hq
  apply (integrable_const (1:ℝ)).mono' (gaussian_continuous_tanh.pow 2).aestronglyMeasurable
  exact .of_forall fun x => by
    change ‖Real.tanh x^2‖ ≤ 1
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact tanh_sq_le_one x

theorem terminal_crossing_C_integral_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1) :
    0 < ∫ x, sech x^2 ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq) := by
  letI := bridgeCrossingWeightLaw_isProbability β hβ μ q hq
  apply (integral_pos_iff_support_of_nonneg (fun x => sq_nonneg (sech x))
    (integrable_terminal_crossing_C β hβ μ q hq)).mpr
  have hs : Function.support (fun x : ℝ => sech x^2) = univ := by
    ext x
    simp only [Function.mem_support,mem_univ,iff_true]
    exact (sq_pos_of_pos (sech_pos x)).ne'
  rw [hs,measure_univ]
  exact zero_lt_one

theorem terminal_crossing_second_moment_relation (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1) (m : ℝ)
    (hphi : (∫ x, terminalCrossingPhi m x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) = 0) :
    2*(∫ x, Real.tanh x^2 ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) =
      m*(∫ x, sech x^2 ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) := by
  unfold terminalCrossingPhi at hphi
  rw [integral_sub ((integrable_terminal_crossing_B2 β hβ μ q hq).const_mul 2)
    ((integrable_terminal_crossing_C β hβ μ q hq).const_mul m),
    integral_const_mul,integral_const_mul] at hphi
  linarith

end FRSB
