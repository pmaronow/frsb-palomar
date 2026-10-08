module

public import FRSB.BackwardsSmooth
public import FRSB.MagnetizationCoordinate
public import Paper.ATImplicit

@[expose] public section

noncomputable section
open Set Filter Paper
open scoped Topology ContDiff
namespace FRSB

def backwardMagnetizationInverse (β : ℝ) (μ : ParisiMeasure) (τ b : ℝ) : ℝ :=
  magnetizationInverse β μ (backwardTime β τ) b

def backwardChi (β : ℝ) (μ : ParisiMeasure) (τ b : ℝ) : ℝ :=
  backwardTauD β μ 2 (τ, backwardMagnetizationInverse β μ τ b)

theorem backwardMagnetizationInverse_eq (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (τ b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    backwardTauD β μ 1 (τ, backwardMagnetizationInverse β μ τ b) = b := by
  rw [backwardTauD, show backwardD β μ 1 = backwardB β μ from rfl,
    backwardB_eq_gradient β μ (backwardTime β τ) _ (backwardTime_mem β hβ τ hτ)]
  exact parisiGradient_magnetizationInverse β hβ μ _ b (backwardTime_mem β hβ τ hτ) hb

theorem backwardChi_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (τ b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2)) : 0 < backwardChi β μ τ b :=
  (backwardTauC_pos_le_one β hβ μ τ _ hτ).1

theorem contDiffOn_backwardChi_spatial (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2)) :
    ContDiffOn ℝ ∞ (backwardChi β μ τ) (Ioo (-1 : ℝ) 1) := by
  intro v hv
  have ht := backwardTime_mem β hβ τ hτ
  have hc := (contDiff_backwardD_spatial β μ (backwardTime β τ) ht 2).contDiffAt
    (x := magnetizationInverse β μ (backwardTime β τ) v)
  have hi := contDiffAt_magnetizationInverse β hβ μ (backwardTime β τ) v ht hv
  exact (hc.comp v hi).contDiffWithinAt

theorem hasDerivAt_backwardMagnetizationInverse_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (τ b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (backwardMagnetizationInverse β μ τ) (backwardChi β μ τ b)⁻¹ b := by
  have hd := hasDerivAt_magnetizationInverse β hβ μ (backwardTime β τ) b
    (backwardTime_mem β hβ τ hτ) hb
  convert hd using 1
  · rfl
  · rw [backwardChi, backwardTauD,
      show backwardD β μ 2 = backwardC β μ from rfl,
      backwardC_eq_hessian β μ (backwardTime β τ) _ (backwardTime_mem β hβ τ hτ)]
    rfl

theorem hasDerivAt_backwardChi_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (τ b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (backwardChi β μ τ)
      (-2 * backwardTauZ β μ (τ, backwardMagnetizationInverse β μ τ b)) b := by
  have hd := (hasDerivAt_backwardTauD_spatial β hβ μ 2 τ _ hτ).comp b
    (hasDerivAt_backwardMagnetizationInverse_spatial β hβ μ τ b hτ hb)
  convert hd using 1
  · rfl
  · have hc := (backwardChi_pos β hβ μ τ b hτ).ne'
    dsimp [backwardTauZ, backwardZ, backwardZJet, backwardChi, backwardTauD, backwardC] at *
    field_simp

theorem hasDerivAt_deriv_backwardChi_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (τ b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (deriv (backwardChi β μ τ))
      (-2 * backwardZx β μ (backwardTime β τ,
        backwardMagnetizationInverse β μ τ b) / backwardChi β μ τ b) b := by
  have hz := (hasDerivAt_backwardZ β hβ μ (backwardTime β τ)
    (backwardMagnetizationInverse β μ τ b) (backwardTime_mem β hβ τ hτ)).comp b
      (hasDerivAt_backwardMagnetizationInverse_spatial β hβ μ τ b hτ hb)
  have he : deriv (backwardChi β μ τ) =ᶠ[𝓝 b]
      (fun y => -2 * backwardTauZ β μ (τ, backwardMagnetizationInverse β μ τ y)) := by
    filter_upwards [isOpen_Ioo.mem_nhds hb] with y hy
    exact (hasDerivAt_backwardChi_spatial β hβ μ τ y hτ hy).deriv
  convert (hz.const_mul (-2)).congr_of_eventuallyEq he using 1
  rw [div_eq_mul_inv]
  ring

theorem backwardChi_Q_identity (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (a τ b : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β^2))
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    backwardTauQ β μ a (τ, backwardMagnetizationInverse β μ τ b) =
      -backwardChi β μ τ b * (deriv (deriv (backwardChi β μ τ)) b / 2 + a) := by
  rw [(hasDerivAt_deriv_backwardChi_spatial β hβ μ τ b hτ hb).deriv]
  have hc := (backwardChi_pos β hβ μ τ b hτ).ne'
  dsimp [backwardTauQ, backwardQ, backwardQJet, backwardZx, backwardZxJet, backwardChi,
    backwardTauD, backwardC] at *
  field_simp
  ring

end FRSB
