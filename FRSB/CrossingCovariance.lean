module

public import Mathlib

@[expose] public section

/-! Covariance signs for the actual half-line probability law used in the
 crossing representation. These lemmas use independent copies on the real
 product probability space. Strict positivity is proved from positive mass
 on two ordered sets, so no unstated nondegeneracy assumption is hidden. -/
noncomputable section
open Set Filter MeasureTheory Measure ProbabilityTheory
namespace FRSB

/-- Moment form of covariance, meaningful under the integrability hypotheses
 imposed by the lemmas below. -/
def crossingCovariance (μ : Measure ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ x, f x * g x ∂μ) - (∫ x, f x ∂μ) * (∫ x, g x ∂μ)

theorem crossingCovariance_eq_covariance (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    crossingCovariance μ f g = covariance f g μ := by
  symm
  simpa only [crossingCovariance, Pi.mul_apply] using covariance_eq_sub hf hg

/-- Integrability of the independent-copy difference product follows from
 integrability of each variable and of their same-copy product. -/
theorem integrable_crossing_difference (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    Integrable (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2)) (μ.prod μ) := by
  convert ((hfg.comp_fst μ).sub (hf.mul_prod hg)).sub (hg.mul_prod hf) |>.add
    (hfg.comp_snd μ) using 1
  funext p
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- The independent-copy covariance identity, including all integrability
 conditions needed to expand the four terms by Fubini. -/
theorem crossingCovariance_independent_copies (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    2 * crossingCovariance μ f g =
      ∫ p : ℝ × ℝ, (f p.1 - f p.2) * (g p.1 - g p.2) ∂(μ.prod μ) := by
  have he : (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2)) =
      (fun p => f p.1 * g p.1 - f p.1 * g p.2 - g p.1 * f p.2 + f p.2 * g p.2) := by
    funext p
    ring
  have h1 : Integrable (fun p : ℝ × ℝ => f p.1 * g p.1 - f p.1 * g p.2) (μ.prod μ) :=
    (hfg.comp_fst μ).sub (hf.mul_prod hg)
  have h2 : Integrable (fun p : ℝ × ℝ => f p.1 * g p.1 - f p.1 * g p.2 -
      g p.1 * f p.2) (μ.prod μ) := h1.sub (hg.mul_prod hf)
  rw [he, integral_add h2 (hfg.comp_snd μ), integral_sub h1 (hg.mul_prod hf),
    integral_sub (hfg.comp_fst μ) (hf.mul_prod hg), integral_prod_mul, integral_prod_mul,
    integral_prod _ (hfg.comp_fst μ), integral_prod _ (hfg.comp_snd μ)]
  simp only [integral_const, probReal_univ, one_smul]
  dsimp [crossingCovariance]
  ring

theorem monotone_difference_product_nonneg (f g : ℝ → ℝ)
    (hf : MonotoneOn f (Ici 0)) (hg : MonotoneOn g (Ici 0))
    {x y : ℝ} (hx : x ∈ Ici (0 : ℝ)) (hy : y ∈ Ici (0 : ℝ)) :
    0 ≤ (f x - f y) * (g x - g y) := by
  rcases le_total x y with hxy | hyx
  · exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hf hx hy hxy))
      (sub_nonpos.mpr (hg hx hy hxy))
  · exact mul_nonneg (sub_nonneg.mpr (hf hy hx hyx)) (sub_nonneg.mpr (hg hy hx hyx))

theorem crossing_difference_nonneg_ae (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hs : ∀ᵐ x ∂μ, x ∈ Ici (0 : ℝ))
    (hf : MonotoneOn f (Ici 0)) (hg : MonotoneOn g (Ici 0)) :
    0 ≤ᵐ[μ.prod μ] fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2) := by
  have hp : ∀ᵐ p ∂μ.prod μ, p ∈ Ici (0 : ℝ) ×ˢ Ici (0 : ℝ) := by
    apply (ae_prod_mem_iff_ae_ae_mem (measurableSet_Ici.prod measurableSet_Ici)).mpr
    filter_upwards [hs] with x hx
    filter_upwards [hs] with y hy
    exact ⟨hx, hy⟩
  filter_upwards [hp] with p hp
  exact monotone_difference_product_nonneg f g hf hg hp.1 hp.2

/-- Chebyshev's covariance sign on a law carried by the nonnegative half-line. -/
theorem crossingCovariance_nonneg (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun x => f x * g x) μ)
    (hs : ∀ᵐ x ∂μ, x ∈ Ici (0 : ℝ))
    (hf : MonotoneOn f (Ici 0)) (hg : MonotoneOn g (Ici 0)) :
    0 ≤ crossingCovariance μ f g := by
  have hi := integral_nonneg_of_ae (crossing_difference_nonneg_ae μ f g hs hf hg)
  rw [← crossingCovariance_independent_copies μ f g hfi hgi hfgi] at hi
  linarith

/-- Strict covariance from strictly increasing variables and two disjoint
 ordered sets of positive mass. A positive half-line density supplies these
 mass conditions directly. -/
theorem crossingCovariance_pos (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (f g : ℝ → ℝ) (hfi : Integrable f μ) (hgi : Integrable g μ)
    (hfgi : Integrable (fun x => f x * g x) μ)
    (hs : ∀ᵐ x ∂μ, x ∈ Ici (0 : ℝ))
    (hf : StrictMonoOn f (Ici 0)) (hg : StrictMonoOn g (Ici 0))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a < b)
    (hleft : 0 < μ (Icc 0 a)) (hright : 0 < μ (Ici b)) :
    0 < crossingCovariance μ f g := by
  have hp : 0 < (μ.prod μ) (Function.support
      (fun p : ℝ × ℝ => (f p.1 - f p.2) * (g p.1 - g p.2))) := by
    have hr : 0 < (μ.prod μ) (Icc (0 : ℝ) a ×ˢ Ici b) := by
      rw [Measure.prod_prod]
      exact ENNReal.mul_pos hleft.ne' hright.ne'
    apply hr.trans_le
    apply measure_mono
    intro p hp
    have hx : p.1 ∈ Ici (0 : ℝ) := hp.1.1
    have hy : p.2 ∈ Ici (0 : ℝ) := ha.trans (hab.le.trans hp.2)
    have hxy : p.1 < p.2 := hp.1.2.trans_lt (hab.trans_le hp.2)
    have hval : 0 < (f p.1 - f p.2) * (g p.1 - g p.2) :=
      mul_pos_of_neg_of_neg (sub_neg.mpr (hf hx hy hxy)) (sub_neg.mpr (hg hx hy hxy))
    exact hval.ne'
  have hi := (integral_pos_iff_support_of_nonneg_ae
    (crossing_difference_nonneg_ae μ f g hs hf.monotoneOn hg.monotoneOn)
    (integrable_crossing_difference μ f g hfi hgi hfgi)).mpr hp
  rw [← crossingCovariance_independent_copies μ f g hfi hgi hfgi] at hi
  linarith

end FRSB
