module

public import FRSB.ScalarZeroCrossing
public import FRSB.CrossMomentTransfer
public import FRSB.SupportConnected
public import FRSB.SupportMinimum

@[expose] public section

/-! The actual minimizer has no holes in its support. Every analytic input
to the geometric argument is supplied by the selected Parisi solution. -/
noncomputable section
open Set MeasureTheory Paper
namespace FRSB

theorem constantMassGammaShape (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) :
    ConstantMassGammaShape β μ := by
  intro a b ha hab hb hm hCDF
  have hI : Ioo a b ⊆ Ioo (0 : ℝ) 1 := fun s hs =>
    ⟨ha.trans_lt hs.1, hs.2.trans_le hb⟩
  have hc : ∀ s ∈ Ioo a b, parisiCDF μ s = parisiCDF μ a :=
    fun s hs => hCDF s ⟨hs.1.le, hs.2⟩
  apply crossing_shape_of_positive_derivative_at_zeros (GammaPrime β μ)
    (GammaSecond β μ) (GammaThird β μ (parisiCDF μ a)) a b hab
  · exact fun s hs => hasDerivAt_GammaPrime_of_constant_CDF β hβ μ
      (parisiCDF μ a) a b hI hc hs
  · exact fun s hs => hasDerivAt_GammaSecond_of_constant_CDF β hβ μ
      (parisiCDF μ a) a b hI hc hs
  · intro s hs hz
    have hms : 0 < parisiCDF μ s := by rw [hc s hs]; exact hm
    have ht : s ∈ Ioc (0 : ℝ) 1 := ⟨(hI hs).1, (hI hs).2.le⟩
    simpa only [hc s hs] using GammaThird_pos_of_GammaSecond_zero β hβ μ s ht hms hz

theorem minimizer_full_support (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) :
    ∃ q ∈ Ioo (0 : ℝ) 1, parisiSupport μ = Icc (0 : ℝ) q := by
  have hn : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  obtain ⟨q, hq, hz, htop, hsub⟩ := minimizer_support_endpoints β hβ μ hmin
  exact ⟨q, hq, support_eq_Icc_of_crossing_and_zero β hn μ hmin
    (constantMassGammaShape β hn μ) hz htop (fun x hx => (hsub hx).2)⟩

theorem selected_minimizer_full_support (β : ℝ) (hβ : 1 < β) :
    ∃ q ∈ Ioo (0 : ℝ) 1,
      parisiSupport (parisiMinimizer β 0) = Icc (0 : ℝ) q :=
  minimizer_full_support β hβ _ (isParisiMinimizer_selected β 0)

end FRSB
