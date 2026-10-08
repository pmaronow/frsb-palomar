module

public import FRSB.Optimality
public import FRSB.SupportInitial
public import FRSB.ParisiMinimizerGeometry

@[expose] public section

/-! A minimizing zero-field overlap law at beta greater than one has a
strictly positive top point of support. -/
noncomputable section
open Set MeasureTheory
namespace FRSB
open Paper

theorem support_max_pos (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) {q : ℝ} (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q) : 0 < q := by
  have hb : 0 < β := zero_lt_one.trans hβ
  have hq0 := (parisiSupport_subset μ hq).1
  by_contra hn
  have hqz : q = 0 := le_antisymm (le_of_not_gt hn) hq0
  have hc : curvatureMoment2 β μ 0 = 1 :=
    curvatureMoment2_initial_of_support_le_zero β hb μ (by simpa only [hqz] using hmax)
  obtain ⟨p, hp, hpq⟩ := hq
  have hh := GammaPrime_le_one_of_support β hb.ne' μ hmin p hp
  rw [hpq, hqz] at hh
  unfold GammaPrime at hh
  rw [hc, mul_one] at hh
  nlinarith

theorem selected_support_max_pos (β : ℝ) (hβ : 1 < β)
    {q : ℝ} (hq : q ∈ parisiSupport (parisiMinimizer β 0))
    (hmax : ∀ x ∈ parisiSupport (parisiMinimizer β 0), x ≤ q) : 0 < q :=
  support_max_pos β hβ _ (isParisiMinimizer_selected β 0) hq hmax

theorem exists_support_max_interior (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) :
    ∃ q ∈ Ioo (0 : ℝ) 1, q ∈ parisiSupport μ ∧ ∀ x ∈ parisiSupport μ, x ≤ q := by
  obtain ⟨a, q, _, hq, hbounds⟩ := parisiSupport_extrema μ
  have hmax : ∀ x ∈ parisiSupport μ, x ≤ q := fun x hx => (hbounds x hx).2
  have hqpos := support_max_pos β hβ μ hmin hq hmax
  obtain ⟨p, hp, hpq⟩ := hq
  have hqlt := support_overlap_lt_one β (zero_lt_one.trans hβ).ne' μ hmin p hp
  rw [hpq] at hqlt
  exact ⟨q, ⟨hqpos, hqlt⟩, ⟨p, hp, hpq⟩, hmax⟩

theorem exists_selected_support_max_interior (β : ℝ) (hβ : 1 < β) :
    ∃ q ∈ Ioo (0 : ℝ) 1, q ∈ parisiSupport (parisiMinimizer β 0) ∧
      ∀ x ∈ parisiSupport (parisiMinimizer β 0), x ≤ q :=
  exists_support_max_interior β hβ _ (isParisiMinimizer_selected β 0)

end FRSB
