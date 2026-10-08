module

public import FRSB.SupportQuotient
public import FRSB.PolynomialMomentIdentity
public import FRSB.MomentBootstrap
public import FRSB.DensityRepresentation

@[expose] public section

/-! Actual closed-interval moment and density regularity, including the
left endpoint of the terminal atom. The CDF jump at q is removed only
inside interval integrals, where that singleton has zero Lebesgue mass. -/
noncomputable section
open Set Filter MeasureTheory Paper MvPolynomial
open scoped Topology ContDiff
namespace FRSB

theorem support_moment_integral (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (f : MomentPolynomial) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    moment β μ f t = moment β μ f 0 + ∫ s in 0..t,
      β ^ 2 * (moment β μ (momentDrift0 f) s +
        momentQuotient β μ s * moment β μ (momentDrift1 f) s) := by
  have hh := moment_interval_integral_physical β hβ μ f
    (show (0 : ℝ) ∈ Icc 0 1 by constructor <;> norm_num) ⟨ht.1,ht.2.trans hq1⟩
  have he : (∫ s in 0..t, β ^ 2 * (moment β μ (momentDrift0 f) s +
      momentQuotient β μ s * moment β μ (momentDrift1 f) s)) =
      β ^ 2 * ∫ s in 0..t, moment β μ (momentDrift0 f) s +
        parisiCDF μ s * moment β μ (momentDrift1 f) s := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le ht.1
    intro s hs
    dsimp only
    rw [parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq hq1 hsupp s
      ⟨hs.1.le,hs.2.trans_le ht.2⟩]
  rw [he]
  linarith

/-- Lemma 6.3 for every genuine polynomial moment and the CDF's smooth
extension. No moment differential law or regularity is an extra input. -/
theorem moments_contDiffOn_on_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    (∀ f : MomentPolynomial, ContDiffOn ℝ ∞ (moment β μ f) (Icc 0 q)) ∧
      ContDiffOn ℝ ∞ (momentQuotient β μ) (Icc 0 q) := by
  apply moments_contDiffOn_of_interval_identity (moment β μ) momentDrift0 momentDrift1
    quotientNumeratorPolynomial quotientDenominatorPolynomial β q hq
  · intro f
    exact (continuousOn_moment β hβ μ f).mono (fun _ ht => ⟨ht.1,ht.2.trans hq1⟩)
  · exact fun s hs => quotientDenominator_pos β hβ μ s ⟨hs.1,hs.2.trans hq1⟩
  · exact support_moment_integral β hβ μ hmin q hq hq1 hsupp

/-- Actual physical within derivatives of every polynomial moment,
including zero and the left endpoint q. -/
theorem hasDerivWithinAt_moment_on_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q)
    (f : MomentPolynomial) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) q) :
    HasDerivWithinAt (moment β μ f)
      (β ^ 2 * (moment β μ (momentDrift0 f) t +
        momentQuotient β μ t * moment β μ (momentDrift1 f) t)) (Icc 0 q) t := by
  have hc := moments_contDiffOn_on_support_interval β hβ μ hmin q hq hq1 hsupp
  apply hasDerivWithinAt_of_interval_identity _ _ q
    (continuousOn_const.mul ((hc.1 (momentDrift0 f)).continuousOn.add
      (hc.2.continuousOn.mul (hc.1 (momentDrift1 f)).continuousOn)))
    (support_moment_integral β hβ μ hmin q hq hq1 hsupp f) t ht

/-- The actual nonnegative density is the derivative of the smooth left
CDF, not a two-sided derivative across the terminal atom. -/
def parisiSmoothDensity (β : ℝ) (μ : ParisiMeasure) (q : ℝ) : ℝ → ℝ :=
  smoothCDFDensity (momentQuotient β μ) q

theorem parisiSmoothDensity_regular_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    ContDiffOn ℝ ∞ (parisiSmoothDensity β μ q) (Icc 0 q) ∧
      ∀ s ∈ Icc (0 : ℝ) q, 0 ≤ parisiSmoothDensity β μ q s := by
  let ν : ProbabilityMeasure ℝ := μ.map (fun x : Overlap => (x : ℝ))
  apply smoothCDFDensity_regular (ν : Measure ℝ) (momentQuotient β μ) q hq
    (moments_contDiffOn_on_support_interval β hβ μ hmin q hq hq1 hsupp).2
  intro s hs
  rw [← parisiCDF_eq_momentQuotient_on_support_interval β hβ μ hmin q hq hq1 hsupp s hs,
    ProbabilityMeasure.map_apply' μ measurable_subtype_coe.aemeasurable
      measurableSet_Iic]
  rfl

theorem parisiMeasure_eq_density_add_atom_of_support_interval
    (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : 0 < q) (hq1 : q ≤ 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    (μ : Measure Overlap).map (fun x : Overlap => (x : ℝ)) =
      (volume.restrict (Ico (0 : ℝ) q)).withDensity
        (fun s => ENNReal.ofReal (parisiSmoothDensity β μ q s)) +
      ENNReal.ofReal (1 - momentQuotient β μ q) • Measure.dirac q := by
  apply parisiMeasure_eq_smooth_density_Ico_add_terminal_atom μ (momentQuotient β μ) q hq
  · filter_upwards [Measure.support_mem_ae (μ := (μ : Measure Overlap))] with x hx
    have hs : (x : ℝ) ∈ parisiSupport μ := ⟨x,hx,rfl⟩
    rwa [hsupp] at hs
  · exact (moments_contDiffOn_on_support_interval β hβ μ hmin q hq hq1 hsupp).2
  · exact momentQuotient_initial_zero β μ
  · exact fun s hs => (parisiCDF_eq_momentQuotient_on_support_interval
      β hβ μ hmin q hq hq1 hsupp s hs).symm

end FRSB
