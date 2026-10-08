module

public import FRSB.SupportGeometry
public import FRSB.OptimalCurvatureMoment
public import Paper.ParisiDiracIdentification

@[expose] public section

/-! Exact degenerate-support identification and its actual initial curvature. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace FRSB
open Paper

theorem parisiMeasure_eq_dirac_zero_of_support_le_zero (μ : ParisiMeasure)
    (hq : ∀ x ∈ parisiSupport μ, x ≤ 0) :
    μ = diracOverlap 0 (by norm_num) := by
  apply parisiMeasure_eq_dirac_of_support_subset_singleton μ (⟨0, by norm_num⟩ : Overlap)
  intro x hx
  apply Set.mem_singleton_iff.mpr
  apply Subtype.ext
  exact le_antisymm (hq x ⟨x, hx, rfl⟩) x.property.1

theorem curvatureMoment2_dirac_zero_initial (β : ℝ) (hβ : 0 < β) :
    curvatureMoment2 β (diracOverlap 0 (by norm_num)) 0 = 1 := by
  unfold curvatureMoment2
  have he (ω : BrownianSample) : C β (diracOverlap 0 (by norm_num)) 0 ω = 1 := by
    rw [C_eq_hessian, optimalState_initial,
      parisiHessian_dirac_hard β 0 hβ (by norm_num) 0 0 (by norm_num)]
    simp [sech]
  simp_rw [he]
  simp

theorem curvatureMoment2_initial_of_support_le_zero (β : ℝ) (hβ : 0 < β)
    (μ : ParisiMeasure) (hq : ∀ x ∈ parisiSupport μ, x ≤ 0) :
    curvatureMoment2 β μ 0 = 1 := by
  rw [parisiMeasure_eq_dirac_zero_of_support_le_zero μ hq]
  exact curvatureMoment2_dirac_zero_initial β hβ

end FRSB
