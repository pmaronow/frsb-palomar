module

public import FRSB.SupportGapCalculus
public import FRSB.SupportGeometry
public import FRSB.Optimality

@[expose] public section

/-! The geometric assembly of the support argument. The crossing-shape input
is kept explicit until it is discharged by the forward/backward analysis. -/
noncomputable section
open Set MeasureTheory Paper
namespace FRSB

def ConstantMassGammaShape (β : ℝ) (μ : ParisiMeasure) : Prop :=
  ∀ a b : ℝ, 0 ≤ a → a < b → b ≤ 1 →
    0 < parisiCDF μ a → (∀ s ∈ Ico a b, parisiCDF μ s = parisiCDF μ a) →
    ∃ c ∈ Icc a b,
      StrictAntiOn (GammaPrime β μ) (Ioc a c ∩ Ioo a b) ∧
      StrictMonoOn (GammaPrime β μ) (Ico c b ∩ Ioo a b)

theorem no_support_gap_of_constantMassGammaShape (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (hshape : ConstantMassGammaShape β μ) {a b : ℝ}
    (ha : a ∈ parisiSupport μ) (hb : b ∈ parisiSupport μ) (hab : a < b)
    (hgap : ∀ x ∈ Ioo a b, x ∉ parisiSupport μ) : False := by
  have ha01 := parisiSupport_subset μ ha
  have hb01 := parisiSupport_subset μ hb
  have hsub : Icc a b ⊆ Icc (0 : ℝ) 1 := fun x hx =>
    ⟨ha01.1.trans hx.1, hx.2.trans hb01.2⟩
  apply no_gap_of_crossing_shape (Gamma β μ) (GammaPrime β μ) hab
    ((continuousOn_Gamma β hβ μ).mono hsub)
    ((continuousOn_GammaPrime β hβ μ).mono hsub)
    (fun x hx => hasDerivAt_Gamma_GammaPrime β hβ μ
      ⟨ha01.1.trans_lt hx.1, hx.2.trans_le hb01.2⟩)
  · rcases ha with ⟨qa, hqa, rfl⟩
    exact Gamma_eq_overlap_of_support β hβ μ hmin qa hqa
  · rcases hb with ⟨qb, hqb, rfl⟩
    exact Gamma_eq_overlap_of_support β hβ μ hmin qb hqb
  · rcases ha with ⟨qa, hqa, rfl⟩
    exact GammaPrime_le_one_of_support β hβ μ hmin qa hqa
  · rcases hb with ⟨qb, hqb, rfl⟩
    exact GammaPrime_le_one_of_support β hβ μ hmin qb hqb
  · exact hshape a b ha01.1 hab hb01.2
      (parisiCDF_positive_before_support_gap μ hab ha hgap)
      (fun s hs => parisiCDF_constant_on_support_gap μ hgap hs)

theorem support_eq_Icc_of_crossing_and_zero (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure)
    (hmin : ∀ ν : ParisiMeasure, parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (hshape : ConstantMassGammaShape β μ) {q : ℝ}
    (hzero : 0 ∈ parisiSupport μ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) : parisiSupport μ = Icc (0 : ℝ) q := by
  apply Subset.antisymm
  · intro x hx
    exact ⟨(parisiSupport_subset μ hx).1, hmax x hx⟩
  · intro x hx
    by_contra hxn
    obtain ⟨a, b, ha, hb, hax, hxb, hgap⟩ :=
      compact_support_has_gap (parisiSupport_compact μ) hzero hq hx hxn
    exact no_support_gap_of_constantMassGammaShape β hβ μ hmin hshape ha hb
      (hax.trans hxb) hgap

end FRSB
