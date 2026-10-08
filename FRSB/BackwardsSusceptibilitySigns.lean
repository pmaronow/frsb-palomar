module

public import FRSB.BackwardsSusceptibilityTime

@[expose] public section

noncomputable section
open Set Filter Paper
open scoped Topology
namespace FRSB

theorem backwardMagnetizationInverse_nonneg (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (τ v : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hv : v ∈ Ioo (-1 : ℝ) 1) (hv0 : 0 ≤ v) :
    0 ≤ backwardMagnetizationInverse β μ τ v := by
  have ht := backwardTime_mem β hβ τ hτ
  apply (parisiGradient_strictMono β hβ μ _ ht).le_iff_le.mp
  change parisiGradient β μ (backwardTime β τ,0) ≤
    parisiGradient β μ (backwardTime β τ,magnetizationInverse β μ (backwardTime β τ) v)
  rw [parisiGradient_at_zero β hβ μ _ ht,
    parisiGradient_magnetizationInverse β hβ μ _ v ht hv]
  exact hv0

theorem backward_magnetization_rates (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1)
    (hv0 : 0 ≤ v) :
    0 ≤ deriv (fun r => backwardMagnetizationInverse β μ r v) τ ∧
    deriv (fun r => backwardChi β μ r v) τ ≤ 0 ∧
    deriv (fun r => Real.log (backwardChi β μ r v)) τ ≤ 0 ∧
    deriv (fun b => Real.sqrt (backwardChi β μ τ b)) v ≤ 0 ∧
    0 ≤ deriv (fun b => deriv (fun r => Real.sqrt (backwardChi β μ r b)) τ) v := by
  have ht : backwardTime β τ ∈ Icc (0 : ℝ) 1 := ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  have hg := backwardTime_mem_converse β hβ τ ht
  let x := backwardMagnetizationInverse β μ τ v
  have hx := backwardMagnetizationInverse_nonneg β hβ μ τ v hg hv hv0
  have hm := hc _ ⟨hτ.1.le,hτ.2⟩
  have hB := backwardMagnetizationInverse_eq β hβ μ τ v hg hv
  have hzl := backwardZ_ge_massB β hβ μ _ x ht hx
  have hz := backwardZ_nonneg β hβ μ _ x ht hx
  have hq := backwardQ_nonneg β hβ μ _ x ht
  have hh := (backwardHx_bounds β hβ μ _ x ht hx).1
  rw [hm] at hzl hq hh
  rw [show backwardB β μ (backwardTime β τ,x) = v from hB] at hzl
  have hp := backwardChi_pos β hβ μ τ v hg
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [(hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc hτ hv).deriv]
    exact sub_nonneg.mpr hzl
  · rw [(hasDerivAt_backwardChi_time β hβ μ ha hab hb hc hτ hv).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq) hp.le
  · rw [(hasDerivAt_log_backwardChi_time β hβ μ ha hab hb hc hτ hv).deriv]
    exact neg_nonpos.mpr hq
  · rw [(hasDerivAt_sqrt_backwardChi_spatial β hβ μ τ v hg hv).deriv]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz) (Real.sqrt_nonneg _)
  · rw [(hasDerivAt_deriv_sqrt_backwardChi_time_spatial β hβ μ ha hab hb hc hτ hv).deriv]
    exact div_nonneg hh (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

theorem backwardTime_mem_open_interval (β : ℝ) (hβ : β ≠ 0)
    (a b τ : ℝ) (hτ : τ ∈ Ioo (β^2*(1-b)) (β^2*(1-a))) :
    backwardTime β τ ∈ Ioo a b := by
  have hp := sq_pos_of_ne_zero hβ
  have hlo : 1-b < τ/β^2 := (lt_div_iff₀ hp).mpr (by nlinarith [hτ.1])
  have hhi : τ/β^2 < 1-a := (div_lt_iff₀ hp).mpr (by nlinarith [hτ.2])
  dsimp [backwardTime]
  constructor <;> linarith

theorem backwardChi_antitoneOn_constantCDF (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (v : ℝ) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    AntitoneOn (fun r => backwardChi β μ r v) (Ioo (β^2*(1-b)) (β^2*(1-a))) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioo _ _)
  · intro τ hτ
    exact (hasDerivAt_backwardChi_time β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [interior_Ioo] at hτ
    exact (hasDerivAt_backwardChi_time β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [interior_Ioo] at hτ
    have ht := backwardTime_mem_open_interval β hβ a b τ hτ
    have hphys : backwardTime β τ ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩
    have hg := backwardTime_mem_converse β hβ τ hphys
    have hq := backwardQ_nonneg β hβ μ _ (backwardMagnetizationInverse β μ τ v) hphys
    rw [hc _ ⟨ht.1.le,ht.2⟩] at hq
    rw [(hasDerivAt_backwardChi_time β hβ μ ha hab hb hc ht hv).deriv]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq)
      (backwardChi_pos β hβ μ τ v hg).le

theorem backwardMagnetizationInverse_monotoneOn_constantCDF (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (v : ℝ)
    (hv : v ∈ Ioo (-1 : ℝ) 1) (hv0 : 0 ≤ v) :
    MonotoneOn (fun r => backwardMagnetizationInverse β μ r v)
      (Ioo (β^2*(1-b)) (β^2*(1-a))) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
  · intro τ hτ
    exact (hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [interior_Ioo] at hτ
    exact (hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [interior_Ioo] at hτ
    exact (backward_magnetization_rates β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv hv0).1

end FRSB
