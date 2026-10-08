module

public import FRSB.BackwardsSusceptibilitySigns

@[expose] public section

/-! The time derivative of the spatial square-root slope. This proves the
literal monotonicity interpretation, without assuming mixed derivatives
commute. -/
noncomputable section
open Set Filter Paper
open scoped Topology
namespace FRSB

theorem hasDerivAt_spatial_slope_sqrt_backwardChi_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => deriv (fun b => Real.sqrt (backwardChi β μ r b)) v)
      (backwardHx β μ m (backwardTime β τ,backwardMagnetizationInverse β μ τ v) /
        (4 * Real.sqrt (backwardChi β μ τ v))) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  let x := backwardMagnetizationInverse β μ τ v
  have hi := hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc hτ hv
  have hD := (hasStrictFDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 3 (x := x) hτ).hasFDerivAt
    |>.comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk hi)
  have hC := hasDerivAt_backwardChi_time β hβ μ ha hab hb hc hτ hv
  have hp := backwardChi_pos β hβ μ τ v hg
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hZ := hD.neg.div (hC.const_mul 2) (mul_ne_zero (by norm_num) hp.ne')
  have hroot := hasDerivAt_sqrt_backwardChi_time β hβ μ ha hab hb hc hτ hv
  have hd := hZ.neg.div hroot hs
  have hmap : Continuous (backwardTime β) := continuous_const.sub (continuous_id.div_const (β^2))
  have he : (fun r => deriv (fun b => Real.sqrt (backwardChi β μ r b)) v) =ᶠ[𝓝 τ]
      (fun r => -backwardTauZ β μ (r,backwardMagnetizationInverse β μ r v) /
        Real.sqrt (backwardChi β μ r v)) := by
    filter_upwards [hmap.continuousAt.eventually (isOpen_Ioo.mem_nhds hτ)] with r hr
    exact (hasDerivAt_sqrt_backwardChi_spatial β hβ μ r v
      (backwardTime_mem_converse β hβ r ⟨ha.trans hr.1.le,hr.2.le.trans hb⟩) hv).deriv
  convert hd.congr_of_eventuallyEq he using 1
  simp only [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul,one_mul]
  rw [backwardTauForcing_three,backwardMagnetizationInverse_eq β hβ μ τ v hg hv]
  have hsq := Real.sq_sqrt hp.le
  dsimp [x,backwardChi,backwardTauD,backwardTauZ,backwardZ,backwardZJet,
      backwardTauQ,backwardQ,backwardQJet,backwardZxJet,backwardHx,backwardHxJet,
      backwardQxJet,backwardZxxJet,backwardC,backwardDtJet] at *
  field_simp
  ring

theorem sqrt_backwardChi_slope_monotoneOn_constantCDF (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) (v : ℝ)
    (hv : v ∈ Ioo (-1 : ℝ) 1) (hv0 : 0 ≤ v) :
    MonotoneOn (fun r => deriv (fun b => Real.sqrt (backwardChi β μ r b)) v)
      (Ioo (β^2*(1-b)) (β^2*(1-a))) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioo _ _)
  · intro τ hτ
    exact (hasDerivAt_spatial_slope_sqrt_backwardChi_time β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [interior_Ioo] at hτ
    exact (hasDerivAt_spatial_slope_sqrt_backwardChi_time β hβ μ ha hab hb hc
      (backwardTime_mem_open_interval β hβ a b τ hτ) hv).differentiableAt.differentiableWithinAt
  · intro τ hτ
    rw [interior_Ioo] at hτ
    have ht := backwardTime_mem_open_interval β hβ a b τ hτ
    have hphys : backwardTime β τ ∈ Icc (0 : ℝ) 1 := ⟨ha.trans ht.1.le,ht.2.le.trans hb⟩
    have hg := backwardTime_mem_converse β hβ τ hphys
    have hx := backwardMagnetizationInverse_nonneg β hβ μ τ v hg hv hv0
    have hh := (backwardHx_bounds β hβ μ _ (backwardMagnetizationInverse β μ τ v) hphys hx).1
    rw [hc _ ⟨ht.1.le,ht.2⟩] at hh
    rw [(hasDerivAt_spatial_slope_sqrt_backwardChi_time β hβ μ ha hab hb hc ht hv).deriv]
    exact div_nonneg hh (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))

end FRSB
