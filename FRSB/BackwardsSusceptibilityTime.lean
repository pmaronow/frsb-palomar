module

public import FRSB.BackwardsInverseTime

@[expose] public section

/-! The fixed-magnetization susceptibility dynamics of Remark 3.2. -/
noncomputable section
open Set Filter Paper
open scoped Topology
namespace FRSB

theorem hasDerivAt_backwardChi_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => backwardChi β μ r v)
      (-backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v) * backwardChi β μ τ v) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  let x := backwardMagnetizationInverse β μ τ v
  have htotal := (hasStrictFDerivAt_constantCDF_backwardTauD β hβ μ ha hab hb hc 2 (x := x) hτ).hasFDerivAt
    |>.comp_hasDerivAt τ ((hasDerivAt_id τ).prodMk
      (hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc hτ hv))
  convert htotal using 1
  · rfl
  · simp only [ContinuousLinearMap.coprod_apply,ContinuousLinearMap.toSpanSingleton_apply,
      smul_eq_mul,one_mul]
    rw [backwardTauForcing_two,backwardMagnetizationInverse_eq β hβ μ τ v hg hv]
    have hn := (backwardChi_pos β hβ μ τ v hg).ne'
    dsimp [backwardTauQ,backwardQ,backwardQJet,backwardZxJet,backwardTauZ,
      backwardZ,backwardZJet,backwardCtJet,backwardChi,backwardTauD,backwardC] at *
    field_simp
    ring

theorem hasDerivAt_backwardChi_time_PDE (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => backwardChi β μ r v)
      (backwardChi β μ τ v^2 * (deriv (deriv (backwardChi β μ τ)) v / 2 + m)) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  have hd := hasDerivAt_backwardChi_time β hβ μ ha hab hb hc hτ hv
  rw [backwardChi_Q_identity β hβ μ m τ v hg hv] at hd
  convert hd using 1
  ring

theorem hasDerivAt_log_backwardChi_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => Real.log (backwardChi β μ r v))
      (-backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v)) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  have hp := backwardChi_pos β hβ μ τ v hg
  convert (hasDerivAt_backwardChi_time β hβ μ ha hab hb hc hτ hv).log hp.ne' using 1
  exact (mul_div_cancel_right₀ _ hp.ne').symm

theorem hasDerivAt_sqrt_backwardChi_time (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun r => Real.sqrt (backwardChi β μ r v))
      (-backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v) *
        Real.sqrt (backwardChi β μ τ v) / 2) τ := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  have hp := backwardChi_pos β hβ μ τ v hg
  convert (hasDerivAt_backwardChi_time β hβ μ ha hab hb hc hτ hv).sqrt hp.ne' using 1
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have he := Real.sq_sqrt hp.le
  field_simp
  rw [he]

theorem hasDerivAt_sqrt_backwardChi_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (τ v : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun b => Real.sqrt (backwardChi β μ τ b))
      (-backwardTauZ β μ (τ,backwardMagnetizationInverse β μ τ v) /
        Real.sqrt (backwardChi β μ τ v)) v := by
  have hp := backwardChi_pos β hβ μ τ v hτ
  convert (hasDerivAt_backwardChi_spatial β hβ μ τ v hτ hv).sqrt hp.ne' using 1
  ring

theorem hasDerivAt_deriv_sqrt_backwardChi_time_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (fun b => deriv (fun r => Real.sqrt (backwardChi β μ r b)) τ)
      (backwardHx β μ m (backwardTime β τ,backwardMagnetizationInverse β μ τ v) /
        (4 * Real.sqrt (backwardChi β μ τ v))) v := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  have hp := backwardChi_pos β hβ μ τ v hg
  let x := backwardMagnetizationInverse β μ τ v
  have hq := (hasDerivAt_backwardQ β hβ μ m (backwardTime β τ) x
    ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩).comp v
      (hasDerivAt_backwardMagnetizationInverse_spatial β hβ μ τ v hg hv)
  have hd := ((hq.neg).mul (hasDerivAt_sqrt_backwardChi_spatial β hβ μ τ v hg hv)).div_const 2
  have he : (fun b => deriv (fun r => Real.sqrt (backwardChi β μ r b)) τ) =ᶠ[𝓝 v]
      (fun b => -backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ b) *
        Real.sqrt (backwardChi β μ τ b) / 2) := by
    filter_upwards [isOpen_Ioo.mem_nhds hv] with b hb'
    exact (hasDerivAt_sqrt_backwardChi_time β hβ μ ha hab hb hc hτ hb').deriv
  convert hd.congr_of_eventuallyEq he using 1
  have hs := (Real.sqrt_pos.mpr hp).ne'
  have hsq := Real.sq_sqrt hp.le
  have hid := backwardHx_eq_zQ_Qx m (backwardChi β μ τ v)
    (backwardTauD β μ 3 (τ,x)) (backwardTauD β μ 4 (τ,x)) (backwardTauD β μ 5 (τ,x)) hp.ne'
  dsimp [x] at *
  dsimp [backwardHx,backwardQ,backwardTauZ,backwardTauQ,backwardZ,backwardChi,
    backwardTauD,backwardC] at *
  rw [div_eq_mul_inv]
  field_simp
  rw [hsq,hid]
  ring

end FRSB
