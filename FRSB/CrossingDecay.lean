module

public import Mathlib

@[expose] public section

/-! Integrability and boundary decay of the concrete Gaussian envelopes
 in Section 5. These estimates turn actual pointwise density bounds into
 genuine Bochner integrability and zero flux at spatial infinity. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace FRSB

def crossingGaussianEnvelope (v : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (1 + |x| ^ n) * Real.exp (x - x ^ 2 / (2 * v))

theorem crossing_exp_exponent_le (v x : ℝ) (hv : 0 < v) :
    x - x ^ 2 / (2 * v) ≤ v - (1 / (4 * v)) * x ^ 2 := by
  have hs := sq_nonneg (x - 2 * v)
  apply (mul_le_mul_iff_of_pos_right (show 0 < 4 * v by positivity)).mp
  field_simp
  nlinarith

theorem crossingGaussianEnvelope_le (v : ℝ) (n : ℕ) (hv : 0 < v) (x : ℝ) :
    crossingGaussianEnvelope v n x ≤
      Real.exp v * ((1 + |x| ^ n) * Real.exp (-(1 / (4 * v)) * x ^ 2)) := by
  unfold crossingGaussianEnvelope
  calc
    _ ≤ (1 + |x| ^ n) * Real.exp (v - (1 / (4 * v)) * x ^ 2) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (crossing_exp_exponent_le v x hv)) (by positivity)
    _ = _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      simp only [neg_mul]
      ring

/-- Every fixed polynomial power against the paper's envelope is integrable. -/
theorem integrable_crossingGaussianEnvelope (v : ℝ) (n : ℕ) (hv : 0 < v) :
    Integrable (crossingGaussianEnvelope v n) := by
  have hb : 0 < 1 / (4 * v) := by positivity
  have h0 := integrable_exp_neg_mul_sq hb
  have hn : Integrable (fun x : ℝ => x ^ n * Real.exp (-(1 / (4 * v)) * x ^ 2)) := by
    simpa only [Real.rpow_natCast] using integrable_rpow_mul_exp_neg_mul_sq hb
      (show (-1 : ℝ) < n from lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))
  have ha : Integrable (fun x : ℝ => |x| ^ n * Real.exp (-(1 / (4 * v)) * x ^ 2)) := by
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)] using hn.norm
  have hm : Integrable (fun x : ℝ =>
      Real.exp v * ((1 + |x| ^ n) * Real.exp (-(1 / (4 * v)) * x ^ 2))) := by
    convert (h0.add ha).const_mul (Real.exp v) using 1
    funext x
    simp only [Pi.add_apply]
    ring
  apply hm.mono' (by unfold crossingGaussianEnvelope; fun_prop) (Filter.Eventually.of_forall ?_)
  intro x
  rw [Real.norm_eq_abs, abs_of_nonneg (by unfold crossingGaussianEnvelope; positivity)]
  exact crossingGaussianEnvelope_le v n hv x

/-- Every polynomial-weighted Gaussian envelope vanishes at infinity. -/
theorem tendsto_crossingGaussianEnvelope_atTop (v : ℝ) (n : ℕ) (hv : 0 < v) :
    Tendsto (crossingGaussianEnvelope v n) atTop (𝓝 0) := by
  have hb : 0 < 1 / (4 * v) := by positivity
  have hx2 : Tendsto (fun x : ℝ => x ^ 2) atTop atTop := tendsto_pow_atTop (by decide)
  have h0 : Tendsto (fun x : ℝ => Real.exp (-(1 / (4 * v)) * x ^ 2)) atTop (𝓝 0) := by
    simpa only [Real.rpow_zero, one_mul, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 _ hb).comp hx2
  have hn : Tendsto (fun x : ℝ => (x ^ 2) ^ n * Real.exp (-(1 / (4 * v)) * x ^ 2))
      atTop (𝓝 0) := by
    simpa only [Real.rpow_natCast, Function.comp_def] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero n _ hb).comp hx2
  have hm : Tendsto (fun x : ℝ => Real.exp v *
      ((1 + (x ^ 2) ^ n) * Real.exp (-(1 / (4 * v)) * x ^ 2))) atTop (𝓝 0) := by
    convert (h0.add hn).const_mul (Real.exp v) using 1
    · funext x
      ring
    · simp only [zero_add, mul_zero]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun x => by
    unfold crossingGaussianEnvelope; positivity)) _ hm
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  apply (crossingGaussianEnvelope_le v n hv x).trans
  gcongr
  rw [abs_of_nonneg (by linarith : 0 ≤ x)]
  nlinarith

/-- An actual function dominated by the envelope is integrable. -/
theorem integrableOn_of_crossingGaussianEnvelope_bound (f : ℝ → ℝ)
    (v : ℝ) (n : ℕ) (c : ℝ) (hv : 0 < v)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ))))
    (hb : ∀ x > 0, ‖f x‖ ≤ c * crossingGaussianEnvelope v n x) :
    IntegrableOn f (Ioi (0 : ℝ)) := by
  apply ((integrable_crossingGaussianEnvelope v n hv).const_mul c).integrableOn.mono' hf
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  exact hb x hx

/-- The same actual bound forces its spatial boundary value to vanish. -/
theorem tendsto_zero_of_crossingGaussianEnvelope_bound (f : ℝ → ℝ)
    (v : ℝ) (n : ℕ) (c : ℝ) (hv : 0 < v)
    (hb : ∀ x > 0, ‖f x‖ ≤ c * crossingGaussianEnvelope v n x) :
    Tendsto f atTop (𝓝 0) := by
  apply squeeze_zero_norm' _ (by simpa only [mul_zero] using
    (tendsto_crossingGaussianEnvelope_atTop v n hv).const_mul c)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact hb x hx

end FRSB
