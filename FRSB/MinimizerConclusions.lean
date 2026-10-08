module

public import FRSB.Main

@[expose] public section

/-! Quotient and endpoint conclusions with the support geometry discharged.
The terminal point is specified only as the actual maximum of support. -/
noncomputable section
open Set MeasureTheory Paper
open scoped ContDiff
namespace FRSB

theorem minimizer_support_eq_Icc_of_max (β : ℝ) (hβ : 1 < β)
    (μ : ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ)
    (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) :
    q ∈ Ioo (0 : ℝ) 1 ∧ parisiSupport μ = Icc (0 : ℝ) q := by
  obtain ⟨r,hr,hsupp⟩ := minimizer_full_support β hβ μ hmin
  have hqr : q ≤ r := (hsupp ▸ hq).2
  have hrq : r ≤ q := hmax r (hsupp ▸ ⟨hr.1.le,le_rfl⟩)
  have he : q = r := le_antisymm hqr hrq
  simpa only [he] using (show r ∈ Ioo (0 : ℝ) 1 ∧ parisiSupport μ = Icc (0 : ℝ) r from ⟨hr,hsupp⟩)

theorem minimizer_quotient (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) :
    ContinuousOn (quotientNumerator β μ) (Icc (0 : ℝ) 1) ∧
    ContinuousOn (quotientDenominator β μ) (Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, 0 < quotientDenominator β μ s) ∧
    (∀ s ∈ Ico (0 : ℝ) q, parisiCDF μ s = momentQuotient β μ s) ∧
    parisiLeftMass μ q = momentQuotient β μ q ∧
    (μ : Measure Overlap) {⟨0,by simp⟩} = 0 := by
  have hn : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  obtain ⟨hqI,hsupp⟩ := minimizer_support_eq_Icc_of_max β hβ μ hmin q hq hmax
  exact ⟨continuousOn_quotientNumerator β hn μ,continuousOn_quotientDenominator β hn μ,
    quotientDenominator_pos β hn μ,
    parisiCDF_eq_momentQuotient_on_support_interval β hn μ hmin q hqI.1 hqI.2.le hsupp,
    momentQuotient_terminal_mass_of_support_interval β hn μ hmin q hqI.1 hqI.2.le hsupp,
    parisiMeasure_no_atom_zero_of_support_interval β hn μ hmin q hqI.1 hqI.2.le hsupp⟩

theorem minimizer_moments_smooth (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) :
    (∀ f : MomentPolynomial, ContDiffOn ℝ ∞ (moment β μ f) (Icc (0 : ℝ) q)) ∧
      ContDiffOn ℝ ∞ (momentQuotient β μ) (Icc (0 : ℝ) q) := by
  obtain ⟨hqI,hsupp⟩ := minimizer_support_eq_Icc_of_max β hβ μ hmin q hq hmax
  exact moments_contDiffOn_on_support_interval β (zero_lt_one.trans hβ).ne' μ hmin
    q hqI.1 hqI.2.le hsupp

/-- The SK application in Remark 6.4 and the additional endpoint result:
the actual CDF is smooth below the atom, and every derivative of its smooth
left extension, of the density, and of every polynomial moment is continuous
through the closed support interval. -/
theorem minimizer_endpoint_regular (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) :
    ContDiffOn ℝ ∞ (parisiCDF μ) (Ico (0 : ℝ) q) ∧
    (∀ n : ℕ, ContinuousOn
      (iteratedDerivWithin n (momentQuotient β μ) (Icc (0 : ℝ) q)) (Icc (0 : ℝ) q)) ∧
    (∀ n : ℕ, ContinuousOn
      (iteratedDerivWithin n (parisiSmoothDensity β μ q) (Icc (0 : ℝ) q)) (Icc (0 : ℝ) q)) ∧
    (∀ (f : MomentPolynomial) (n : ℕ), ContinuousOn
      (iteratedDerivWithin n (moment β μ f) (Icc (0 : ℝ) q)) (Icc (0 : ℝ) q)) := by
  have hn : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  obtain ⟨hqI,hsupp⟩ := minimizer_support_eq_Icc_of_max β hβ μ hmin q hq hmax
  have hm := minimizer_moments_smooth β hβ μ hmin q hq hmax
  have hρ := (parisiSmoothDensity_regular_of_support_interval β hn μ hmin q
    hqI.1 hqI.2.le hsupp).1
  have hu := uniqueDiffOn_Icc hqI.1
  refine ⟨?_,?_,?_,?_⟩
  · apply (hm.2.mono Ico_subset_Icc_self).congr
    exact fun s hs => (minimizer_quotient β hβ μ hmin q hq hmax).2.2.2.1 s hs
  · exact fun n => hm.2.continuousOn_iteratedDerivWithin (by simp) hu
  · exact fun n => hρ.continuousOn_iteratedDerivWithin (by simp) hu
  · exact fun f n => (hm.1 f).continuousOn_iteratedDerivWithin (by simp) hu

end FRSB
