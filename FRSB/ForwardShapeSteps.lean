module

public import FRSB.ForwardHeatShape
public import FRSB.BackwardsLower

@[expose] public section

/-! Closed analytical shape steps used in the finite-measure forward
induction: a genuine Gaussian heat step and the actual Parisi atom update. -/
noncomputable section
open Set
open scoped ContDiff
namespace FRSB

lemma forwardHeatCorrection_eq_negativeLogFactor (r t : ℝ) (ht : t ≠ 0)
    (w : ℝ → ℝ) :
    forwardHeatCorrection r t w = fun x => -Real.log
      (forwardHeatFactor r (fun y => Real.exp (-w y)) t x) := by
  funext x
  simp only [forwardHeatCorrection, forwardHeatFactor, gaussianScaledAverage,
    forwardHeatVariance_eq r t ht]

/-- The literal heat-step formula in the paper preserves the nonpositive
third spatial derivative, with all domination discharged by the initial
positive-order spatial derivative bounds. -/
theorem forwardHeatCorrection_third_nonpos {r t : ℝ} (hr : 0 < r) (hrt : r ≤ t)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (hnon : ∀ y, 0 ≤ w y)
    (he : ∀ y, w (-y) = w y) (K : ℕ → ℝ) (hK : ∀ j, 0 ≤ K j)
    (hwb : ∀ j y, ‖iteratedDeriv (j + 1) w y‖ ≤ K (j + 1))
    (hshape : ∀ y, 0 ≤ y → iteratedDeriv 3 w y ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) : iteratedDeriv 3 (forwardHeatCorrection r t w) x ≤ 0 := by
  let F := fun y => Real.exp (-w y)
  let B := exponentialDerivativeConstant K
  have hF : ContDiff ℝ ∞ F := hw.neg.exp
  have hrel (j : ℕ) (y : ℝ) : ‖iteratedDeriv j F y‖ ≤ B j * F y := by
    simpa only [neg_mul, one_mul] using norm_iteratedDeriv_exp_neg_mul_le w 1 hw
      ⟨by norm_num, le_refl _⟩ K hK hwb j y
  have hB (j : ℕ) : 0 ≤ B j := exponentialDerivativeConstant_nonneg K hK j
  have hb (j : ℕ) (y : ℝ) : ‖iteratedDeriv j F y‖ ≤ B j :=
    (hrel j y).trans ((mul_le_mul_of_nonneg_left
      (Real.exp_le_one_iff.mpr (neg_nonpos.mpr (hnon y))) (hB j)).trans_eq (mul_one _))
  let L := ∑ j ∈ Finset.range 4, B j
  have hL : 0 ≤ L := Finset.sum_nonneg fun j _ => hB j
  have hLB (j : ℕ) (hj : j ≤ 3) : B j ≤ L :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_range.mpr (by omega))
  have hp (y : ℝ) : 0 < F y := Real.exp_pos _
  have heF (y : ℝ) : F (-y) = F y := by dsimp [F]; rw [he]
  have hlog : (fun y => -Real.log (F y)) = w := by
    funext y
    simp only [F, Real.log_exp, neg_neg]
  have hh := forwardHeatLogJet_three_nonpos r t hr hrt F hF B hb hp heF L hL
    (fun j hj y => (hrel j y).trans (mul_le_mul_of_nonneg_right (hLB j hj) (hp y).le))
    (by rw [hlog]; exact hshape) t x ⟨hrt, le_refl _⟩ hx
  rw [forwardHeatCorrection_eq_negativeLogFactor r t (hr.trans_le hrt).ne']
  exact hh

/-- Atoms add δu to W, so the already proved backward third-derivative
sign gives the actual forward sign at the post-atom endpoint. -/
theorem forwardAtomUpdate_third_nonpos (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w) (δ : ℝ) (hδ : 0 ≤ δ)
    (hshape : ∀ y, 0 ≤ y → iteratedDeriv 3 w y ≤ 0)
    (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (fun y => w y + δ * Paper.parisiPotential β μ (t,y)) x ≤ 0 := by
  have hu := Paper.contDiff_parisiPotential_spatial β μ t ht
  change iteratedDeriv 3 (w + (fun y => δ * Paper.parisiPotential β μ (t,y))) x ≤ 0
  rw [iteratedDeriv_add (hw.of_le (by simp)).contDiffAt
      ((contDiff_const.mul hu).of_le (by simp)).contDiffAt,
    iteratedDeriv_const_mul δ (hu.of_le (by simp)).contDiffAt]
  have hD := backwardD_three_nonpos β hβ μ t x ht hx
  have he : iteratedDeriv 3 (fun y => Paper.parisiPotential β μ (t,y)) x = backwardD β μ 3 (t,x) :=
    (Paper.parisiSpatialField_eq_iteratedDeriv β μ 3 t x ht).symm
  rw [he]
  exact add_nonpos (hshape x hx) (mul_nonpos_of_nonneg_of_nonpos hδ hD)

end FRSB
