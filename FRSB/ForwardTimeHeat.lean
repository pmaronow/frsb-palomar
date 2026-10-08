module

public import FRSB.ForwardHigherHeat
public import Common.Mathlib.Probability.Distributions.Gaussian.HeatSemigroup

@[expose] public section

/-! The genuine Gaussian bridge satisfies the transformed forward heat
equation at every spatial derivative order.  No mixed-partial premise is
assumed: time differentiation is Gaussian integration by parts. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped ContDiff Topology NNReal
namespace FRSB

def forwardHeatVariance (r t : ℝ) : ℝ := r - r ^ 2 / t

lemma forwardHeatVariance_eq (r t : ℝ) (ht : t ≠ 0) :
    forwardHeatVariance r t = r * (t - r) / t := by
  unfold forwardHeatVariance
  field_simp

lemma forwardHeatVariance_pos {r t : ℝ} (hr : 0 < r) (hrt : r < t) :
    0 < forwardHeatVariance r t := by
  rw [forwardHeatVariance_eq r t (hr.trans hrt).ne']
  exact div_pos (mul_pos hr (sub_pos.mpr hrt)) (hr.trans hrt)

def forwardHeatFactor (r : ℝ) (F : ℝ → ℝ) (t x : ℝ) : ℝ :=
  gaussianScaledAverage (r / t) (Real.sqrt (forwardHeatVariance r t)) F x

def forwardHeatJet (r : ℝ) (F : ℝ → ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  (r / t) ^ j * gaussianScaledAverage (r / t)
    (Real.sqrt (forwardHeatVariance r t)) (iteratedDeriv j F) x

theorem forwardHeatJet_eq_iteratedDeriv (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) (t x : ℝ) :
    forwardHeatJet r F j t x = iteratedDeriv j (forwardHeatFactor r F t) x :=
  (iteratedDeriv_gaussianScaledAverage _ _ F hF B hb j x).symm

lemma hasDerivAt_forwardFraction (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (fun v => r / v) (-r / t ^ 2) t := by
  have h := (hasDerivAt_const t r).div (hasDerivAt_id t) ht
  convert h using 1
  · rfl
  · dsimp
    ring

lemma hasDerivAt_forwardVariance (r t : ℝ) (ht : t ≠ 0) :
    HasDerivAt (forwardHeatVariance r) (r ^ 2 / t ^ 2) t := by
  have h := (hasDerivAt_const t r).sub (hasDerivAt_forwardFraction (r ^ 2) t ht)
  convert h using 1
  · rfl
  · ring

lemma forwardGaussianIntegral_eq (H : ℝ → ℝ) (hH : Continuous H)
    (r t x : ℝ) (hv : 0 ≤ forwardHeatVariance r t) :
    (∫ z, H (r / t * x + z) ∂gaussianReal 0 (forwardHeatVariance r t).toNNReal) =
      gaussianScaledAverage (r / t) (Real.sqrt (forwardHeatVariance r t)) H x := by
  have h := ColeHopfFoundation.ProbabilityTheory.integral_gaussianReal_eq_integral_sqrt_mul
    (forwardHeatVariance r t).toNNReal (F := fun z => H (r / t * x + z))
    ((hH.comp (by fun_prop)).aestronglyMeasurable)
  simp only [Function.comp_def, Real.coe_toNNReal _ hv] at h
  exact h

theorem hasDerivAt_forwardGaussianAverage (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) (t x : ℝ) (hrt : r < t) :
    HasDerivAt (fun v => gaussianScaledAverage (r / v)
      (Real.sqrt (forwardHeatVariance r v)) (iteratedDeriv j F) x)
      ((-r / t ^ 2 * x) * gaussianScaledAverage (r / t)
        (Real.sqrt (forwardHeatVariance r t)) (iteratedDeriv (j + 1) F) x +
       (r ^ 2 / t ^ 2) / 2 * gaussianScaledAverage (r / t)
        (Real.sqrt (forwardHeatVariance r t)) (iteratedDeriv (j + 2) F) x) t := by
  have ht : 0 < t := hr.trans hrt
  have hd (n : ℕ) (y : ℝ) : HasDerivAt (iteratedDeriv n F) (iteratedDeriv (n + 1) F y) y := by
    rw [iteratedDeriv_succ]
    exact (hF.differentiable_iteratedDeriv n (by exact_mod_cast WithTop.coe_lt_top n) y).hasDerivAt
  have hg (n : ℕ) : ColeHopfFoundation.ProbabilityTheory.HasExpGrowth (iteratedDeriv n F) :=
    ColeHopfFoundation.ProbabilityTheory.HasExpGrowth.of_bounded (fun y => by
      simpa only [Real.norm_eq_abs] using hb n y)
  have hlocal : ∀ᶠ v in 𝓝 t, r < v := Ioi_mem_nhds hrt
  have hy : ∀ᶠ v in 𝓝 t, HasDerivAt (fun v => r / v * x) (-r / v ^ 2 * x) v := by
    filter_upwards [hlocal] with v hv
    exact (hasDerivAt_forwardFraction r v (hr.trans hv).ne').mul_const x
  have hv : ∀ᶠ v in 𝓝 t, HasDerivAt (forwardHeatVariance r) (r ^ 2 / v ^ 2) v := by
    filter_upwards [hlocal] with v hv
    exact hasDerivAt_forwardVariance r v (hr.trans hv).ne'
  have hout := ColeHopfFoundation.ProbabilityTheory.hasDerivAt_integral_comp_add_gaussianReal_curve
    (hd j) (hd (j + 1)) (hg j) (hg (j + 1)) (hg (j + 2))
    (hF.continuous_iteratedDeriv (j + 2) (by simp)) hy
    (by fun_prop (disch := exact pow_ne_zero 2 ht.ne')) hv (by fun_prop (disch := exact pow_ne_zero 2 ht.ne'))
    (forwardHeatVariance_pos hr hrt)
  have he : (fun v => ∫ z, iteratedDeriv j F (r / v * x + z)
      ∂gaussianReal 0 (forwardHeatVariance r v).toNNReal) =ᶠ[𝓝 t]
      (fun v => gaussianScaledAverage (r / v) (Real.sqrt (forwardHeatVariance r v)) (iteratedDeriv j F) x) := by
    filter_upwards [hlocal] with v hv
    exact forwardGaussianIntegral_eq _ (hF.continuous_iteratedDeriv j (by simp)) r v x
      (forwardHeatVariance_pos hr hv).le
  rw [forwardGaussianIntegral_eq _ (hF.continuous_iteratedDeriv (j + 1) (by simp)) r t x
      (forwardHeatVariance_pos hr hrt).le,
    forwardGaussianIntegral_eq _ (hF.continuous_iteratedDeriv (j + 2) (by simp)) r t x
      (forwardHeatVariance_pos hr hrt).le] at hout
  exact hout.congr_of_eventuallyEq he.symm

lemma forwardHeatJet_time_coefficient (r t x a₀ a₁ a₂ : ℝ) (ht : t ≠ 0) (j : ℕ) :
    (1 / 2 : ℝ) * ((r / t) ^ (j + 2) * a₂) -
      x / t * ((r / t) ^ (j + 1) * a₁) -
      (j : ℝ) / t * ((r / t) ^ j * a₀) =
    (j : ℝ) * (r / t) ^ (j - 1) * (-r / t ^ 2) * a₀ +
      (r / t) ^ j * ((-r / t ^ 2 * x) * a₁ + (r ^ 2 / t ^ 2) / 2 * a₂) := by
  cases j with
  | zero =>
    norm_num
    simp only [div_pow]
    field_simp [ht]
    <;> ring
  | succ j =>
    simp only [Nat.cast_add, Nat.cast_one, Nat.add_one_sub_one, pow_succ]
    field_simp [ht]
    <;> field_simp [ht]
    <;> ring

/-- Every genuine spatial jet satisfies the transformed heat equation. -/
theorem hasDerivAt_forwardHeatJet_time (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) (t x : ℝ) (hrt : r < t) :
    HasDerivAt (fun v => forwardHeatJet r F j v x)
      ((1 / 2 : ℝ) * forwardHeatJet r F (j + 2) t x -
        x / t * forwardHeatJet r F (j + 1) t x -
        (j : ℝ) / t * forwardHeatJet r F j t x) t := by
  have ht : 0 < t := hr.trans hrt
  have hp := (hasDerivAt_forwardFraction r t ht.ne').pow j
  have ha := hasDerivAt_forwardGaussianAverage r hr F hF B hb j t x hrt
  have hout := hp.mul ha
  convert hout using 1
  · rfl
  · simp only [forwardHeatJet, Pi.pow_apply]
    exact forwardHeatJet_time_coefficient r t x _ _ _ ht.ne' j

end FRSB
