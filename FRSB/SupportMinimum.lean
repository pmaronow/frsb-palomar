module

public import FRSB.BeforeSupport
public import FRSB.SupportMinimumCalculus
public import FRSB.Optimality
public import FRSB.ParisiMinimizerGeometry
public import FRSB.CurvatureIdentity
public import FRSB.SupportTopPositive

@[expose] public section

/-! Assembly of the support-minimum argument. The private calculus assembly
is separated from the actual curvature-evolution instantiation. -/
noncomputable section
open Set MeasureTheory
namespace FRSB
open Paper

theorem support_min_zero_of_deriv_pos (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : IsParisiMinimizer β 0 μ) {a : ℝ}
    (ha : a ∈ parisiSupport μ)
    (hd : ∀ s ∈ Ioo (0 : ℝ) a, 0 < deriv (GammaPrime β μ) s) : a = 0 := by
  have ha0 := (parisiSupport_subset μ ha).1
  have ha1 := (parisiSupport_subset μ ha).2
  by_contra hne
  have hap : 0 < a := lt_of_le_of_ne ha0 (Ne.symm hne)
  have hsubset : Icc (0 : ℝ) a ⊆ Icc (0 : ℝ) 1 :=
    fun _ hs => ⟨hs.1, hs.2.trans ha1⟩
  obtain ⟨q, hq, hqa⟩ := ha
  have hGa := Gamma_eq_overlap_of_support β hβ μ hmin q hq
  have hpa := GammaPrime_le_one_of_support β hβ μ hmin q hq
  rw [hqa] at hGa hpa
  exact no_positive_first_endpoint (Gamma β μ) (GammaPrime β μ) hap
    ((continuousOn_Gamma β hβ μ).mono hsubset)
    ((continuousOn_GammaPrime β hβ μ).mono hsubset)
    (fun s hs => hasDerivAt_Gamma_GammaPrime β hβ μ ⟨hs.1, hs.2.trans_le ha1⟩)
    hd (Gamma_initial_zero β hβ μ) hGa hpa

theorem hasDerivAt_GammaPrime_before_support (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a t : ℝ} (hmin : ∀ x ∈ parisiSupport μ, a ≤ x)
    (ha1 : a ≤ 1) (ht : t ∈ Ioo (0 : ℝ) a) :
    HasDerivAt (GammaPrime β μ)
      (β^4*∫ω,D β μ t ω ^ 2 ∂canonicalBrownianMeasure) t := by
  have hEq : parisiCDF μ =ᶠ[nhds t] fun _ => (0 : ℝ) := by
    filter_upwards [isOpen_Iio.mem_nhds ht.2] with s hs
    exact parisiCDF_eq_zero_below_support μ hmin hs
  have hh := hasDerivAt_GammaPrime_of_continuousAt_CDF β hβ μ
    ⟨ht.1,ht.2.trans_le ha1⟩ hEq.continuousAt
  rw [parisiCDF_eq_zero_below_support μ hmin ht.2] at hh
  simpa only [mul_zero,zero_mul,sub_zero] using hh

/-- The first point of support of an actual zero-field minimizer is zero.
All stochastic, curvature-evolution, Gaussian-law and nontriviality inputs
are discharged by the preceding actual foundations. -/
theorem support_min_zero (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) {a : ℝ} (ha : a ∈ parisiSupport μ)
    (hminimum : ∀ x ∈ parisiSupport μ, a ≤ x) : a = 0 := by
  apply support_min_zero_of_deriv_pos β hβ μ hmin ha
  intro t ht
  have ha1 := (parisiSupport_subset μ ha).2
  rw [(hasDerivAt_GammaPrime_before_support β hβ μ hminimum ha1 ht).deriv]
  have hfour : 0 < β^4 := by nlinarith [sq_pos_of_ne_zero (pow_ne_zero 2 hβ)]
  exact mul_pos hfour
    (thirdMoment2_pos_before_support β hβ μ hminimum ⟨ht.1,ht.2.le.trans ha1⟩ ht.2.le)

theorem zero_mem_parisiSupport (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) : 0 ∈ parisiSupport μ := by
  obtain ⟨a, q, ha, _hq, hbounds⟩ := parisiSupport_extrema μ
  have hz := support_min_zero β hβ μ hmin ha (fun x hx => (hbounds x hx).1)
  simpa only [hz] using ha

/-- Literal first steps of Section 6: the actual support begins at zero and
has a top point strictly between zero and one. -/
theorem minimizer_support_endpoints (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) :
    ∃ q ∈ Ioo (0 : ℝ) 1, 0 ∈ parisiSupport μ ∧ q ∈ parisiSupport μ ∧
      parisiSupport μ ⊆ Icc (0 : ℝ) q := by
  obtain ⟨q, hqI, hq, hmax⟩ := exists_support_max_interior β hβ μ hmin
  exact ⟨q, hqI, zero_mem_parisiSupport β (zero_lt_one.trans hβ).ne' μ hmin, hq,
    fun x hx => ⟨(parisiSupport_subset μ hx).1,hmax x hx⟩⟩

theorem selected_minimizer_support_endpoints (β : ℝ) (hβ : 1 < β) :
    ∃ q ∈ Ioo (0 : ℝ) 1, 0 ∈ parisiSupport (parisiMinimizer β 0) ∧
      q ∈ parisiSupport (parisiMinimizer β 0) ∧
      parisiSupport (parisiMinimizer β 0) ⊆ Icc (0 : ℝ) q :=
  minimizer_support_endpoints β hβ _ (isParisiMinimizer_selected β 0)

end FRSB
