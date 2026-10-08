module

public import FRSB.SupportDensityFormula
public import FRSB.TerminalAtomSupport

@[expose] public section

/-! Exact normalization of the actual smooth density below the terminal
overlap, retaining the endpoint atom. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff
namespace FRSB

theorem parisiSmoothDensity_total_mass_of_support_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0:ℝ) q) :
    (∫ x in 0..q, parisiSmoothDensity β μ q x) = parisiLeftMass μ q := by
  have hF := (moments_contDiffOn_on_support_interval β hβ μ hmin q hq hq1 hsupp).2
  have hρ := (parisiSmoothDensity_regular_of_support_interval β hβ μ hmin q hq hq1 hsupp).1
  have hi : (∫ x in 0..q, parisiSmoothDensity β μ q x) =
      momentQuotient β μ q - momentQuotient β μ 0 := by
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hq.le hF.continuousOn
    · intro x hx
      have hd := (hF.differentiableOn (by simp) x ⟨hx.1.le,hx.2.le⟩).hasDerivWithinAt
      change HasDerivWithinAt (momentQuotient β μ) (parisiSmoothDensity β μ q x) (Icc 0 q) x at hd
      exact (hd.hasDerivAt (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
    · have hu : ContinuousOn (parisiSmoothDensity β μ q) (uIcc 0 q) := by
        simpa only [uIcc_of_le hq.le] using hρ.continuousOn
      exact hu.intervalIntegrable
  rw [hi,momentQuotient_initial_zero,sub_zero]
  exact (momentQuotient_terminal_mass_of_support_interval β hβ μ hmin q hq hq1 hsupp).symm

theorem parisiSmoothDensity_atom_normalization_of_support_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0:ℝ) q) :
    (∫ x in 0..q, parisiSmoothDensity β μ q x) + parisiAtomMass μ q hq = 1 := by
  rw [parisiSmoothDensity_total_mass_of_support_interval β hβ μ hmin q hq.1 hq.2 hsupp,
    ← parisiCDF_eq_left_add_atom]
  exact parisiCDF_eq_one_above_support μ (fun x hx => (hsupp ▸ hx).2) le_rfl

end FRSB
