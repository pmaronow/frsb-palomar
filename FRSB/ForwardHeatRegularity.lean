module

public import FRSB.ForwardTimeHeat
public import FRSB.ForwardLogBounds

@[expose] public section

/-! Spatial smoothness, positivity and closed-time continuity of the
actual forward Gaussian bridge, including its zero-variance initial face. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped ContDiff Topology
namespace FRSB

lemma continuous_gaussianScaledAverage_parameters (F : ℝ → ℝ)
    (hF : Continuous F) (M : ℝ) (hb : ∀ y, ‖F y‖ ≤ M) :
    Continuous (fun p : (ℝ × ℝ) × ℝ => gaussianScaledAverage p.1.1 p.1.2 F p.2) := by
  unfold gaussianScaledAverage Paper.gaussianExpectation
  apply continuous_of_dominated (bound := fun _ => M)
  · intro p
    exact (hF.comp (by fun_prop)).aestronglyMeasurable
  · intro p
    exact .of_forall fun z => hb _
  · exact integrable_const M
  · filter_upwards with z
    exact hF.comp (by fun_prop)

lemma continuousOn_forwardHeatJet (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) : ContinuousOn (fun p : ℝ × ℝ => forwardHeatJet r F j p.1 p.2)
      (Ici r ×ˢ (univ : Set ℝ)) := by
  have hn (p : ℝ × ℝ) (hp : p ∈ Ici r ×ˢ (univ : Set ℝ)) : p.1 ≠ 0 :=
    (hr.trans_le hp.1).ne'
  have hθ : ContinuousOn (fun p : ℝ × ℝ => r / p.1) (Ici r ×ˢ (univ : Set ℝ)) :=
    continuousOn_const.div continuous_fst.continuousOn hn
  have hv : ContinuousOn (fun p : ℝ × ℝ => forwardHeatVariance r p.1)
      (Ici r ×ˢ (univ : Set ℝ)) :=
    continuousOn_const.sub (continuousOn_const.div continuous_fst.continuousOn hn)
  have ha := continuous_gaussianScaledAverage_parameters (iteratedDeriv j F)
    (hF.continuous_iteratedDeriv j (by simp)) (B j) (hb j)
  exact (hθ.pow j).mul (ha.comp_continuousOn ((hθ.prodMk hv.sqrt).prodMk continuous_snd.continuousOn))

lemma hasDerivAt_forwardHeatJet_spatial (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) (t x : ℝ) :
    HasDerivAt (forwardHeatJet r F j t) (forwardHeatJet r F (j + 1) t x) x := by
  have hd (y : ℝ) : HasDerivAt (iteratedDeriv j F) (iteratedDeriv (j + 1) F y) y := by
    rw [iteratedDeriv_succ]
    exact (hF.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top j) y).hasDerivAt
  have hi := integrable_gaussian_bounded (fun z => iteratedDeriv j F
      (r / t * x + Real.sqrt (forwardHeatVariance r t) * z))
    ((hF.continuous_iteratedDeriv j (by simp)).comp (by fun_prop)) (B j) (fun z => hb j _)
  have ha := Paper.hasDerivAt_gaussian_shift (iteratedDeriv j F) (iteratedDeriv (j + 1) F)
    (Real.sqrt (forwardHeatVariance r t)) (r / t * x) (B (j + 1))
    (hF.continuous_iteratedDeriv j (by simp)) (hF.continuous_iteratedDeriv (j + 1) (by simp))
    hi hd (hb (j + 1))
  have hout := (ha.comp x ((hasDerivAt_id x).const_mul (r / t))).const_mul ((r / t) ^ j)
  convert hout using 1
  · rfl
  · simp only [forwardHeatJet, gaussianScaledAverage, pow_succ, id_eq]
    ring

lemma contDiff_forwardHeatFactor (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (t : ℝ) : ContDiff ℝ ∞ (forwardHeatFactor r F t) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j hj x
  rw [show iteratedDeriv j (forwardHeatFactor r F t) = forwardHeatJet r F j t by
    funext x; exact (forwardHeatJet_eq_iteratedDeriv r F hF B hb j t x).symm]
  exact (hasDerivAt_forwardHeatJet_spatial r F hF B hb j t x).differentiableAt

lemma forwardHeatFactor_pos (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (t x : ℝ) : 0 < forwardHeatFactor r F t x := by
  apply (integral_pos_iff_support_of_nonneg (fun z => (hp _).le)
    (integrable_gaussian_bounded _ (hF.continuous.comp (by fun_prop)) (B 0)
      (fun z => by simpa only [iteratedDeriv_zero] using hb 0 _))).mpr
  have he : Function.support (fun z => F (r / t * x + Real.sqrt (forwardHeatVariance r t) * z)) = univ := by
    ext z
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (hp _).ne'
  rw [he]
  simp

lemma forwardHeatFactor_initial (r : ℝ) (hr : r ≠ 0) (F : ℝ → ℝ) (x : ℝ) :
    forwardHeatFactor r F r x = F x := by
  have hv : forwardHeatVariance r r = 0 := by
    rw [forwardHeatVariance_eq r r hr]
    simp
  simp [forwardHeatFactor, gaussianScaledAverage, Paper.gaussianExpectation, hv, div_self hr]

lemma forwardHeatJet_initial (r : ℝ) (hr : r ≠ 0) (F : ℝ → ℝ) (j : ℕ) (x : ℝ) :
    forwardHeatJet r F j r x = iteratedDeriv j F x := by
  have hv : forwardHeatVariance r r = 0 := by
    rw [forwardHeatVariance_eq r r hr]
    simp
  simp [forwardHeatJet, gaussianScaledAverage, Paper.gaussianExpectation, hv, div_self hr]

lemma forwardHeatJet_uniform_bound (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) (t x : ℝ) (ht : r ≤ t) : ‖forwardHeatJet r F j t x‖ ≤ B j := by
  have ht0 := hr.trans_le ht
  have hθ : r / t ∈ Icc (0 : ℝ) 1 := ⟨div_nonneg hr.le ht0.le, (div_le_one ht0).mpr ht⟩
  have hb0 : 0 ≤ B j := (norm_nonneg _).trans (hb j 0)
  have ha : ‖gaussianScaledAverage (r / t) (Real.sqrt (forwardHeatVariance r t)) (iteratedDeriv j F) x‖ ≤ B j := by
    exact (norm_integral_le_of_norm_le_const (.of_forall fun z => hb j _)).trans_eq (by simp)
  rw [forwardHeatJet, norm_mul, Real.norm_of_nonneg (pow_nonneg hθ.1 j)]
  exact (mul_le_mul (pow_le_one₀ hθ.1 hθ.2) ha (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

lemma forwardHeatJet_relative_bound (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (j : ℕ) (L : ℝ) (hL : 0 ≤ L) (hrel : ∀ x, ‖iteratedDeriv j F x‖ ≤ L * F x)
    (t x : ℝ) (ht : r ≤ t) : ‖forwardHeatJet r F j t x‖ ≤ L * forwardHeatFactor r F t x := by
  rw [forwardHeatJet_eq_iteratedDeriv r F hF B hb]
  exact gaussianScaledAverage_relative_derivative_bound (r / t)
    (Real.sqrt (forwardHeatVariance r t))
    ⟨div_nonneg hr.le (hr.trans_le ht).le, (div_le_one (hr.trans_le ht)).mpr ht⟩
    F hF B hb L hL j hrel x

end FRSB
