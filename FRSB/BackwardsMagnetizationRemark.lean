module

public import FRSB.BackwardsSlopeTime

@[expose] public section

/-! One closed endpoint for all identities of Remark 3.2. The global
backward clock differs from the paper's cell clock by a constant only. -/
noncomputable section
open Set Paper
namespace FRSB

theorem backward_magnetization_identities (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1) :
    deriv (fun r => backwardMagnetizationInverse β μ r v) τ =
      backwardTauZ β μ (τ,backwardMagnetizationInverse β μ τ v) - m*v ∧
    deriv (fun r => backwardChi β μ r v) τ =
      backwardChi β μ τ v^2 * (deriv (deriv (backwardChi β μ τ)) v / 2 + m) ∧
    deriv (fun r => Real.log (backwardChi β μ r v)) τ =
      -backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v) ∧
    deriv (fun b => deriv (fun r => Real.sqrt (backwardChi β μ r b)) τ) v =
      backwardHx β μ m (backwardTime β τ,backwardMagnetizationInverse β μ τ v) /
        (4 * Real.sqrt (backwardChi β μ τ v)) ∧
    deriv (backwardChi β μ τ) v =
      -2 * backwardTauZ β μ (τ,backwardMagnetizationInverse β μ τ v) ∧
    backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v) =
      -backwardChi β μ τ v * (deriv (deriv (backwardChi β μ τ)) v / 2 + m) := by
  have hg := backwardTime_mem_converse β hβ τ ⟨ha.trans hτ.1.le,hτ.2.le.trans hb⟩
  exact ⟨(hasDerivAt_backwardMagnetizationInverse_time β hβ μ ha hab hb hc hτ hv).deriv,
    (hasDerivAt_backwardChi_time_PDE β hβ μ ha hab hb hc hτ hv).deriv,
    (hasDerivAt_log_backwardChi_time β hβ μ ha hab hb hc hτ hv).deriv,
    (hasDerivAt_deriv_sqrt_backwardChi_time_spatial β hβ μ ha hab hb hc hτ hv).deriv,
    (hasDerivAt_backwardChi_spatial β hβ μ τ v hg hv).deriv,
    backwardChi_Q_identity β hβ μ m τ v hg hv⟩

end FRSB
