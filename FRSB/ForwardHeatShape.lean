module

public import FRSB.ForwardLogHeat
public import FRSB.ComparisonBounded

@[expose] public section

/-! The forward heat step preserves the paper's third-derivative sign.
Every coefficient and derivative is constructed from the actual Gaussian
bridge factor, including the initial zero-variance face. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped ContDiff Topology
namespace FRSB

lemma gaussianScaledAverage_even_of_continuous (θ b : ℝ) (F : ℝ → ℝ) (hF : Continuous F)
    (he : ∀ x, F (-x) = F x) (x : ℝ) :
    gaussianScaledAverage θ b F (-x) = gaussianScaledAverage θ b F x := by
  have hm : (gaussianReal (0 : ℝ) 1).map (fun z => -z) = gaussianReal 0 1 := by
    simpa using (gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have hi := integral_map (μ := gaussianReal (0 : ℝ) 1) (φ := fun z : ℝ => -z)
    (f := fun z => F (θ * (-x) + b * z)) (by fun_prop)
    ((hF.comp (by fun_prop)).aestronglyMeasurable)
  rw [hm] at hi
  unfold gaussianScaledAverage Paper.gaussianExpectation
  rw [hi]
  apply integral_congr_ae
  exact .of_forall fun z => by
    change F (θ * (-x) + b * (-z)) = F (θ * x + b * z)
    rw [show θ * (-x) + b * (-z) = -(θ * x + b * z) by ring, he]

lemma forwardHeatLogJet_three_origin (r : ℝ) (F : ℝ → ℝ) (hF : Continuous F)
    (he : ∀ x, F (-x) = F x) (t : ℝ) : forwardHeatLogJet r F 3 t 0 = 0 := by
  let W := fun y => -Real.log (forwardHeatFactor r F t y)
  have hW : (fun y => W (-y)) = W := by
    funext y
    dsimp [W]
    rw [show forwardHeatFactor r F t (-y) = forwardHeatFactor r F t y from
      gaussianScaledAverage_even_of_continuous _ _ F hF he y]
  have hh := iteratedDeriv_comp_neg 3 W (0 : ℝ)
  rw [hW] at hh
  norm_num [smul_eq_mul] at hh
  change iteratedDeriv 3 W 0 = 0
  linarith

lemma hasDerivAt_forwardHeatLogJet_spatial (r : ℝ) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (j : ℕ) (t x : ℝ) :
    HasDerivAt (forwardHeatLogJet r F j t) (forwardHeatLogJet r F (j + 1) t x) x := by
  have hW := ((contDiff_forwardHeatFactor r F hF B hb t).log
    (fun y => (forwardHeatFactor_pos r F hF B hb hp t y).ne')).neg
  unfold forwardHeatLogJet
  rw [iteratedDeriv_succ]
  exact (hW.differentiable_iteratedDeriv j (by exact_mod_cast WithTop.coe_lt_top j) x).hasDerivAt

lemma continuousOn_forwardHeatLogJet_three (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) :
    ContinuousOn (fun p : ℝ × ℝ => forwardHeatLogJet r F 3 p.1 p.2)
      (Ici r ×ˢ (univ : Set ℝ)) := by
  have hj (j : ℕ) := continuousOn_forwardHeatJet r hr F hF B hb j
  have hn (p : ℝ × ℝ) (_hp : p ∈ Ici r ×ˢ (univ : Set ℝ)) : forwardHeatJet r F 0 p.1 p.2 ≠ 0 := by
    simpa only [forwardHeatJet, forwardHeatFactor, iteratedDeriv_zero, pow_zero, one_mul] using
      (forwardHeatFactor_pos r F hF B hb hp p.1 p.2).ne'
  have he : (fun p : ℝ × ℝ => forwardHeatLogJet r F 3 p.1 p.2) =
      fun p => logJet3 (forwardHeatJet r F 0 p.1 p.2) (forwardHeatJet r F 1 p.1 p.2)
        (forwardHeatJet r F 2 p.1 p.2) (forwardHeatJet r F 3 p.1 p.2) := by
    funext p
    exact forwardHeatLogJet_three r F hF B hb hp _ _
  rw [he]
  exact (((hj 3).neg.div (hj 0) hn).add ((((hj 1).const_mul 3).mul (hj 2)).div
    ((hj 0).pow 2) (fun p hp => pow_ne_zero 2 (hn p hp)))).sub
    ((((hj 1).pow 3).const_mul 2).div ((hj 0).pow 3) (fun p hp => pow_ne_zero 3 (hn p hp)))

lemma forwardHeatLogJet_uniform_bound (r : ℝ) (hr : 0 < r) (F : ℝ → ℝ)
    (hF : ContDiff ℝ ∞ F) (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (L : ℝ) (hL : 0 ≤ L) (k : ℕ)
    (hrel : ∀ j ≤ k, ∀ x, ‖iteratedDeriv j F x‖ ≤ L * F x)
    (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ k) (t x : ℝ) (ht : r ≤ t) :
    ‖forwardHeatLogJet r F j t x‖ ≤ negativeLogDerivativeConstant L j := by
  have hrel' (n : ℕ) (hn : n ≤ k) (y : ℝ) :
      ‖iteratedDeriv n (forwardHeatFactor r F t) y‖ ≤ L * forwardHeatFactor r F t y := by
    rw [← forwardHeatJet_eq_iteratedDeriv r F hF B hb]
    exact forwardHeatJet_relative_bound r hr F hF B hb n L hL (hrel n hn) t y ht
  exact norm_iteratedDeriv_negativeLog_le (forwardHeatFactor r F t)
    (contDiff_forwardHeatFactor r F hF B hb t) (forwardHeatFactor_pos r F hF B hb hp t)
    L hL k hrel' j hj hjk x

/-- The actual Gaussian forward heat step preserves W''' ≤ 0 on the
nonnegative half-line. The data assumptions are precisely bounded smooth
positive factors, evenness, relative jet bounds and the initial shape. -/
theorem forwardHeatLogJet_three_nonpos (r T : ℝ) (hr : 0 < r) (hrT : r ≤ T)
    (F : ℝ → ℝ) (hF : ContDiff ℝ ∞ F)
    (B : ℕ → ℝ) (hb : ∀ j x, ‖iteratedDeriv j F x‖ ≤ B j)
    (hp : ∀ x, 0 < F x) (he : ∀ x, F (-x) = F x)
    (L : ℝ) (hL : 0 ≤ L) (hrel : ∀ j ≤ 3, ∀ x, ‖iteratedDeriv j F x‖ ≤ L * F x)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (fun y => -Real.log (F y)) x ≤ 0)
    (t x : ℝ) (ht : t ∈ Icc r T) (hx : 0 ≤ x) :
    forwardHeatLogJet r F 3 t x ≤ 0 := by
  let M₁ := negativeLogDerivativeConstant L 1
  let M₂ := negativeLogDerivativeConstant L 2
  let M₃ := negativeLogDerivativeConstant L 3
  have hM₁ : 0 ≤ M₁ := negativeLogDerivativeConstant_nonneg L hL 1
  have hM₂ : 0 ≤ M₂ := negativeLogDerivativeConstant_nonneg L hL 2
  have hM₃ : 0 ≤ M₃ := negativeLogDerivativeConstant_nonneg L hL 3
  let v : ℝ × ℝ → ℝ := fun p => -forwardHeatLogJet r F 3 (r + p.1) p.2
  let vt : ℝ × ℝ → ℝ := fun p => -((1 / 2 : ℝ) * forwardHeatLogJet r F 5 (r + p.1) p.2 -
    (p.2 / (r + p.1) + forwardHeatLogJet r F 1 (r + p.1) p.2) * forwardHeatLogJet r F 4 (r + p.1) p.2 -
    3 * (1 / (r + p.1) + forwardHeatLogJet r F 2 (r + p.1) p.2) * forwardHeatLogJet r F 3 (r + p.1) p.2)
  let b : ℝ × ℝ → ℝ := fun p => -(p.2 / (r + p.1) + forwardHeatLogJet r F 1 (r + p.1) p.2)
  let κ : ℝ × ℝ → ℝ := fun p => -3 * (1 / (r + p.1) + forwardHeatLogJet r F 2 (r + p.1) p.2)
  have hbound (j : ℕ) (hj : 1 ≤ j) (hjk : j ≤ 3) (s y : ℝ) (hs : 0 ≤ s) :
      |forwardHeatLogJet r F j (r + s) y| ≤ negativeLogDerivativeConstant L j := by
    simpa only [Real.norm_eq_abs] using forwardHeatLogJet_uniform_bound r hr F hF B hb hp
      L hL 3 hrel j hj hjk (r + s) y (by linarith)
  have hsp (j : ℕ) (s y : ℝ) : HasDerivAt (fun z => v (s, z))
      (-forwardHeatLogJet r F 4 (r + s) y) y := by
    exact (hasDerivAt_forwardHeatLogJet_spatial r F hF B hb hp 3 (r + s) y).neg
  have hd (s : ℝ) : deriv (fun y => v (s, y)) = fun y => -forwardHeatLogJet r F 4 (r + s) y :=
    funext fun y => (hsp 3 s y).deriv
  have hsd (s y : ℝ) : HasDerivAt (deriv (fun z => v (s, z)))
      (-forwardHeatLogJet r F 5 (r + s) y) y := by
    rw [hd]
    exact (hasDerivAt_forwardHeatLogJet_spatial r F hF B hb hp 4 (r + s) y).neg
  have hresult := bounded_supersolution_nonneg_quadratic true (T - r) (M₁ + 3 * M₂) M₃
    (sub_nonneg.mpr hrT) (by positivity) hM₃ v vt b κ
    (by
      have hh := (continuousOn_forwardHeatLogJet_three r hr F hF B hb hp).comp
        (by fun_prop : ContinuousOn (fun p : ℝ × ℝ => (r + p.1, p.2))
          (Icc 0 (T - r) ×ˢ comparisonSpace true))
        (by
          intro p hp
          have hp0 : 0 ≤ p.1 := hp.1.1
          exact ⟨by change r ≤ r + p.1; linarith, mem_univ _⟩)
      exact hh.neg)
    (by
      intro s hs y hy
      have hh := hasDerivAt_forwardHeatLogJet_three_time r hr F hF B hb hp (r + s) y (by linarith [hs.1])
      have hout := (hh.comp s ((hasDerivAt_id s).const_add r)).neg
      convert hout.hasDerivWithinAt using 1 <;> dsimp [v, vt] <;> congr 1 <;> ring)
    (by intro s hs y hy; exact (hsp 3 s y).differentiableAt)
    (by intro s hs y hy; exact (hsd s y).differentiableAt)
    (by intro s hs y hy; simpa only [v, abs_neg] using hbound 3 (by omega) (by omega) s y hs.1)
    (by
      intro s hs y hy
      have hy0 : 0 < y := hy
      have hs0 : 0 < r + s := by linarith [hs.1]
      have hwb : -forwardHeatLogJet r F 1 (r + s) y ≤ M₁ :=
        (neg_le_abs _).trans (hbound 1 (by omega) (by omega) s y hs.1.le)
      have hneg : 2 * (-(y / (r + s))) * y ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by norm_num)
          (neg_nonpos.mpr (div_nonneg hy0.le hs0.le))) hy0.le
      have hh := mul_le_mul_of_nonneg_right hwb (by positivity : 0 ≤ 2 * y)
      have hq := mul_nonneg hM₁ (sq_nonneg (y - 1))
      have hq₂ := mul_nonneg (by positivity : 0 ≤ 3 * M₂) (by positivity : 0 ≤ 1 + y ^ 2)
      dsimp [b]
      nlinarith)
    (by
      intro s hs y hy
      have hwb : -forwardHeatLogJet r F 2 (r + s) y ≤ M₂ :=
        (neg_le_abs _).trans (hbound 2 (by omega) (by omega) s y hs.1.le)
      have hs0 : 0 < r + s := by linarith [hs.1]
      have hdiv : 0 ≤ 1 / (r + s) := by positivity
      dsimp [κ]
      linarith)
    (by
      intro s hs y hy
      rw [(hsd s y).deriv, (hsp 3 s y).deriv]
      dsimp [v, vt, b, κ]
      ring_nf
      exact le_refl _)
    (by
      intro y hy
      dsimp [v]
      simp only [add_zero, forwardHeatLogJet]
      have hf : forwardHeatFactor r F r = F := funext (forwardHeatFactor_initial r hr.ne' F)
      rw [hf]
      exact neg_nonneg.mpr (hshape y hy))
    (by
      intro _ s hs
      dsimp [v]
      rw [forwardHeatLogJet_three_origin r F hF.continuous he]
      norm_num)
  have hh := hresult (t - r, x) ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, hx⟩
  dsimp [v] at hh
  have heq : r + (t - r) = t := by ring
  rw [heq] at hh
  exact neg_nonneg.mp hh

end FRSB
