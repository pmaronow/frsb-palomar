module

public import FRSB.ForwardHeatRegularity
public import FRSB.ForwardJetLimits

@[expose] public section

/-! Explicit logarithmic spatial jets and their genuine forward heat
transport equation.  These formulas use the Gaussian time derivatives,
not an assumed interchange of mixed derivatives. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace FRSB

def logJet1 (a₀ a₁ : ℝ) : ℝ := -a₁ / a₀

def logJet2 (a₀ a₁ a₂ : ℝ) : ℝ := -a₂ / a₀ + a₁ ^ 2 / a₀ ^ 2

def logJet3 (a₀ a₁ a₂ a₃ : ℝ) : ℝ :=
  -a₃ / a₀ + 3 * a₁ * a₂ / a₀ ^ 2 - 2 * a₁ ^ 3 / a₀ ^ 3

def logJet4 (a₀ a₁ a₂ a₃ a₄ : ℝ) : ℝ :=
  -a₄ / a₀ + 4 * a₁ * a₃ / a₀ ^ 2 + 3 * a₂ ^ 2 / a₀ ^ 2 -
    12 * a₁ ^ 2 * a₂ / a₀ ^ 3 + 6 * a₁ ^ 4 / a₀ ^ 4

def logJet5 (a₀ a₁ a₂ a₃ a₄ a₅ : ℝ) : ℝ :=
  -a₅ / a₀ + 5 * a₁ * a₄ / a₀ ^ 2 + 10 * a₂ * a₃ / a₀ ^ 2 -
    20 * a₁ ^ 2 * a₃ / a₀ ^ 3 - 30 * a₁ * a₂ ^ 2 / a₀ ^ 3 +
    60 * a₁ ^ 3 * a₂ / a₀ ^ 4 - 24 * a₁ ^ 5 / a₀ ^ 5

lemma iteratedDeriv_negativeLog_one (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ x, 0 < F x) (x : ℝ) :
    iteratedDeriv 1 (fun y => -Real.log (F y)) x = logJet1 (F x) (iteratedDeriv 1 F x) := by
  have h := iteratedDeriv_negativeLog_formula F hF hp 0 x
  simpa [logJet1] using h

lemma iteratedDeriv_negativeLog_two (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ x, 0 < F x) (x : ℝ) :
    iteratedDeriv 2 (fun y => -Real.log (F y)) x =
      logJet2 (F x) (iteratedDeriv 1 F x) (iteratedDeriv 2 F x) := by
  have h := iteratedDeriv_negativeLog_formula F hF hp 1 x
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num only [Nat.choose] at h
  rw [iteratedDeriv_negativeLog_one F hF hp] at h
  simp only [logJet1] at h
  rw [h]
  unfold logJet2
  field_simp [(hp x).ne']
  <;> ring

lemma iteratedDeriv_negativeLog_three (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ x, 0 < F x) (x : ℝ) :
    iteratedDeriv 3 (fun y => -Real.log (F y)) x =
      logJet3 (F x) (iteratedDeriv 1 F x) (iteratedDeriv 2 F x) (iteratedDeriv 3 F x) := by
  have h := iteratedDeriv_negativeLog_formula F hF hp 2 x
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num only [Nat.choose] at h
  rw [iteratedDeriv_negativeLog_one F hF hp, iteratedDeriv_negativeLog_two F hF hp] at h
  simp only [logJet1, logJet2] at h
  rw [h]
  unfold logJet3
  field_simp [(hp x).ne']
  <;> ring

lemma iteratedDeriv_negativeLog_four (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ x, 0 < F x) (x : ℝ) :
    iteratedDeriv 4 (fun y => -Real.log (F y)) x =
      logJet4 (F x) (iteratedDeriv 1 F x) (iteratedDeriv 2 F x)
        (iteratedDeriv 3 F x) (iteratedDeriv 4 F x) := by
  have h := iteratedDeriv_negativeLog_formula F hF hp 3 x
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num only [Nat.choose] at h
  rw [iteratedDeriv_negativeLog_one F hF hp, iteratedDeriv_negativeLog_two F hF hp,
    iteratedDeriv_negativeLog_three F hF hp] at h
  simp only [logJet1, logJet2, logJet3] at h
  rw [h]
  unfold logJet4
  field_simp [(hp x).ne']
  <;> ring

lemma iteratedDeriv_negativeLog_five (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (hp : ∀ x, 0 < F x) (x : ℝ) :
    iteratedDeriv 5 (fun y => -Real.log (F y)) x =
      logJet5 (F x) (iteratedDeriv 1 F x) (iteratedDeriv 2 F x)
        (iteratedDeriv 3 F x) (iteratedDeriv 4 F x) (iteratedDeriv 5 F x) := by
  have h := iteratedDeriv_negativeLog_formula F hF hp 4 x
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  norm_num only [Nat.choose] at h
  rw [iteratedDeriv_negativeLog_one F hF hp, iteratedDeriv_negativeLog_two F hF hp,
    iteratedDeriv_negativeLog_three F hF hp, iteratedDeriv_negativeLog_four F hF hp] at h
  simp only [logJet1, logJet2, logJet3, logJet4] at h
  rw [h]
  unfold logJet5
  field_simp [(hp x).ne']
  <;> ring

/-- The ordinary chain rule for the explicit third logarithmic jet. -/
lemma hasDerivAt_logJet3 {f₀ f₁ f₂ f₃ : ℝ → ℝ} {d₀ d₁ d₂ d₃ t : ℝ}
    (h₀ : HasDerivAt f₀ d₀ t) (h₁ : HasDerivAt f₁ d₁ t)
    (h₂ : HasDerivAt f₂ d₂ t) (h₃ : HasDerivAt f₃ d₃ t) (hn : f₀ t ≠ 0) :
    HasDerivAt (fun v => logJet3 (f₀ v) (f₁ v) (f₂ v) (f₃ v))
      (-d₃ / f₀ t + f₃ t * d₀ / (f₀ t) ^ 2 +
       3 * (d₁ * f₂ t + f₁ t * d₂) / (f₀ t) ^ 2 -
       6 * f₁ t * f₂ t * d₀ / (f₀ t) ^ 3 -
       6 * (f₁ t) ^ 2 * d₁ / (f₀ t) ^ 3 +
       6 * (f₁ t) ^ 3 * d₀ / (f₀ t) ^ 4) t := by
  have hh := ((h₃.neg.div h₀ hn).add (((h₁.const_mul 3).mul h₂).div (h₀.pow 2) (pow_ne_zero 2 hn))).sub
    (((h₁.pow 3).const_mul 2).div (h₀.pow 3) (pow_ne_zero 3 hn))
  convert hh using 1
  · rfl
  · simp only [Pi.neg_apply, Pi.pow_apply, Pi.mul_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
    field_simp [hn]
    <;> ring

lemma logJet3_heat_algebra (a₀ a₁ a₂ a₃ a₄ a₅ b c : ℝ) (hn : a₀ ≠ 0) :
    let d₀ := (1 / 2 : ℝ) * a₂ - b * a₁;
    let d₁ := (1 / 2 : ℝ) * a₃ - b * a₂ - c * a₁;
    let d₂ := (1 / 2 : ℝ) * a₄ - b * a₃ - 2 * c * a₂;
    let d₃ := (1 / 2 : ℝ) * a₅ - b * a₄ - 3 * c * a₃;
    -d₃ / a₀ + a₃ * d₀ / a₀ ^ 2 + 3 * (d₁ * a₂ + a₁ * d₂) / a₀ ^ 2 -
      6 * a₁ * a₂ * d₀ / a₀ ^ 3 - 6 * a₁ ^ 2 * d₁ / a₀ ^ 3 + 6 * a₁ ^ 3 * d₀ / a₀ ^ 4 =
      (1 / 2 : ℝ) * logJet5 a₀ a₁ a₂ a₃ a₄ a₅ -
      (b + logJet1 a₀ a₁) * logJet4 a₀ a₁ a₂ a₃ a₄ -
      3 * (c + logJet2 a₀ a₁ a₂) * logJet3 a₀ a₁ a₂ a₃ := by
  dsimp [logJet1, logJet2, logJet3, logJet4, logJet5]
  field_simp [hn]
  <;> ring

/-- The genuine spatial derivatives of the logarithmic forward correction. -/
def forwardHeatLogJet (r : ℝ) (F : ℝ → ℝ) (j : ℕ) (t x : ℝ) : ℝ :=
  iteratedDeriv j (fun y => -Real.log (forwardHeatFactor r F t y)) x

lemma forwardHeatLogJet_one (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) :
    forwardHeatLogJet r F 1 t x = logJet1 (forwardHeatJet r F 0 t x) (forwardHeatJet r F 1 t x) := by
  have h := iteratedDeriv_negativeLog_one (forwardHeatFactor r F t)
    (contDiff_forwardHeatFactor r F hF B hb t) (forwardHeatFactor_pos r F hF B hb hp t) x
  simpa only [forwardHeatLogJet, ← forwardHeatJet_eq_iteratedDeriv r F hF B hb,
    forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using h

lemma forwardHeatLogJet_two (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) :
    forwardHeatLogJet r F 2 t x = logJet2 (forwardHeatJet r F 0 t x)
      (forwardHeatJet r F 1 t x) (forwardHeatJet r F 2 t x) := by
  have h := iteratedDeriv_negativeLog_two (forwardHeatFactor r F t)
    (contDiff_forwardHeatFactor r F hF B hb t) (forwardHeatFactor_pos r F hF B hb hp t) x
  simpa only [forwardHeatLogJet, ← forwardHeatJet_eq_iteratedDeriv r F hF B hb,
    forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using h

lemma forwardHeatLogJet_three (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) :
    forwardHeatLogJet r F 3 t x = logJet3 (forwardHeatJet r F 0 t x)
      (forwardHeatJet r F 1 t x) (forwardHeatJet r F 2 t x) (forwardHeatJet r F 3 t x) := by
  have h := iteratedDeriv_negativeLog_three (forwardHeatFactor r F t)
    (contDiff_forwardHeatFactor r F hF B hb t) (forwardHeatFactor_pos r F hF B hb hp t) x
  simpa only [forwardHeatLogJet, ← forwardHeatJet_eq_iteratedDeriv r F hF B hb,
    forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using h

lemma forwardHeatLogJet_four (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) :
    forwardHeatLogJet r F 4 t x = logJet4 (forwardHeatJet r F 0 t x)
      (forwardHeatJet r F 1 t x) (forwardHeatJet r F 2 t x)
      (forwardHeatJet r F 3 t x) (forwardHeatJet r F 4 t x) := by
  have h := iteratedDeriv_negativeLog_four (forwardHeatFactor r F t)
    (contDiff_forwardHeatFactor r F hF B hb t) (forwardHeatFactor_pos r F hF B hb hp t) x
  simpa only [forwardHeatLogJet, ← forwardHeatJet_eq_iteratedDeriv r F hF B hb,
    forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using h

lemma forwardHeatLogJet_five (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) :
    forwardHeatLogJet r F 5 t x = logJet5 (forwardHeatJet r F 0 t x)
      (forwardHeatJet r F 1 t x) (forwardHeatJet r F 2 t x)
      (forwardHeatJet r F 3 t x) (forwardHeatJet r F 4 t x) (forwardHeatJet r F 5 t x) := by
  have h := iteratedDeriv_negativeLog_five (forwardHeatFactor r F t)
    (contDiff_forwardHeatFactor r F hF B hb t) (forwardHeatFactor_pos r F hF B hb hp t) x
  simpa only [forwardHeatLogJet, ← forwardHeatJet_eq_iteratedDeriv r F hF B hb,
    forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using h

/-- The paper's logarithmic third-derivative transport PDE follows from
actual Gaussian differentiation of the factor, even if the initial data
have no positive lower bound. -/
theorem hasDerivAt_forwardHeatLogJet_three_time (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) (hrt : r < t) :
    HasDerivAt (fun v => forwardHeatLogJet r F 3 v x)
      ((1 / 2 : ℝ) * forwardHeatLogJet r F 5 t x -
       (x / t + forwardHeatLogJet r F 1 t x) * forwardHeatLogJet r F 4 t x -
       3 * (1 / t + forwardHeatLogJet r F 2 t x) * forwardHeatLogJet r F 3 t x) t := by
  have hzero : forwardHeatJet r F 0 t x ≠ 0 := by
    simpa only [forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using (forwardHeatFactor_pos r F hF B hb hp t x).ne'
  have h₀ := hasDerivAt_forwardHeatJet_time r hr F hF B hb 0 t x hrt
  have h₁ := hasDerivAt_forwardHeatJet_time r hr F hF B hb 1 t x hrt
  have h₂ := hasDerivAt_forwardHeatJet_time r hr F hF B hb 2 t x hrt
  have h₃ := hasDerivAt_forwardHeatJet_time r hr F hF B hb 3 t x hrt
  have hout := hasDerivAt_logJet3 h₀ h₁ h₂ h₃ hzero
  convert hout using 1
  · funext v
    exact forwardHeatLogJet_three r F hF B hb hp v x
  · rw [forwardHeatLogJet_one r F hF B hb hp, forwardHeatLogJet_two r F hF B hb hp,
      forwardHeatLogJet_three r F hF B hb hp, forwardHeatLogJet_four r F hF B hb hp,
      forwardHeatLogJet_five r F hF B hb hp]
    have he := logJet3_heat_algebra (forwardHeatJet r F 0 t x) (forwardHeatJet r F 1 t x)
      (forwardHeatJet r F 2 t x) (forwardHeatJet r F 3 t x)
      (forwardHeatJet r F 4 t x) (forwardHeatJet r F 5 t x) (x / t) (1 / t) hzero
    dsimp at he
    convert he.symm using 1 <;> norm_num <;> ring

end FRSB
