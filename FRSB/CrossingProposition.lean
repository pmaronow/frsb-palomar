module

public import FRSB.FullSupport

@[expose] public section

/-! The literal crossing and turning-point statements on genuine constant
positive-CDF intervals of the actual Parisi diffusion. -/
noncomputable section
open Set Paper
open scoped ContDiff
namespace FRSB

theorem crossing_proposition (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (m a b : ℝ) (hm : 0 < m) (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hCDF : ∀ s ∈ Ioo a b, parisiCDF μ s = m) :
    ContDiffOn ℝ 3 (Gamma β μ) (Ioo a b) ∧
      ∀ s ∈ Ioo a b, deriv (deriv (Gamma β μ)) s = 0 →
        0 < deriv (deriv (deriv (Gamma β μ))) s := by
  refine ⟨contDiffOn_Gamma_three_of_constant_CDF β hβ μ m a b hI hCDF,?_⟩
  intro s hs hz
  rw [(hasDerivAt_deriv_deriv_Gamma_of_constant_CDF β hβ μ m a b hI hCDF hs).deriv]
  have hz' : GammaSecond β μ s = 0 := by
    rwa [(hasDerivAt_deriv_Gamma_of_constant_CDF β hβ μ m a b hI hCDF hs).deriv] at hz
  have hm' : 0 < parisiCDF μ s := by rw [hCDF s hs];exact hm
  simpa only [hCDF s hs] using GammaThird_pos_of_GammaSecond_zero β hβ μ s
    ⟨(hI hs).1,(hI hs).2.le⟩ hm' hz'

theorem crossing_shape (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (m a b : ℝ) (hab : a < b) (hm : 0 < m)
    (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hCDF : ∀ s ∈ Ioo a b, parisiCDF μ s = m) :
    ∃ c ∈ Icc a b,
      StrictAntiOn (GammaPrime β μ) (Ioc a c ∩ Ioo a b) ∧
      StrictMonoOn (GammaPrime β μ) (Ico c b ∩ Ioo a b) := by
  apply crossing_shape_of_positive_derivative_at_zeros (GammaPrime β μ)
    (GammaSecond β μ) (GammaThird β μ m) a b hab
  · exact fun s hs => hasDerivAt_GammaPrime_of_constant_CDF β hβ μ m a b hI hCDF hs
  · exact fun s hs => hasDerivAt_GammaSecond_of_constant_CDF β hβ μ m a b hI hCDF hs
  · intro s hs hz
    have hm' : 0 < parisiCDF μ s := by rw [hCDF s hs];exact hm
    simpa only [hCDF s hs] using GammaThird_pos_of_GammaSecond_zero β hβ μ s
      ⟨(hI hs).1,(hI hs).2.le⟩ hm' hz

end FRSB
