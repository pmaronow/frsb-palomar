module

public import FRSB.BackwardsLower

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardRelativeConstant (β : ℝ) : ℝ :=
  max 1 (max (backwardRelativeK3 β) (max (backwardRelativeK4 β) (backwardRelativeK5 β)))

theorem backwardRelativeConstant_pos (β : ℝ) : 0 < backwardRelativeConstant β :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem backwardClock_mem (β t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardClock β t ∈ Icc (0 : ℝ) (β ^ 2) := by
  dsimp [backwardClock]
  constructor <;> nlinarith [sq_nonneg β,ht.1,ht.2]

theorem finiteScheme_relative_derivative_bound {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ)
    (hj : j ∈ Finset.Icc 2 5) :
    |backwardD β (Paper.parisiSchemeMeasure s) j (t,x)| ≤
      backwardRelativeConstant β*backwardC β (Paper.parisiSchemeMeasure s) (t,x) := by
  have hc := (backwardC_pos β hβ (Paper.parisiSchemeMeasure s) t x ht).le
  have hτ := backwardClock_mem β t ht
  have hk1 : 1 ≤ backwardRelativeConstant β := le_max_left _ _
  have hk3 : backwardRelativeK3 β ≤ backwardRelativeConstant β :=
    (le_max_left _ _).trans (le_max_right _ _)
  have hk4 : backwardRelativeK4 β ≤ backwardRelativeConstant β :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  have hk5 : backwardRelativeK5 β ≤ backwardRelativeConstant β :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)
  rcases Finset.mem_Icc.mp hj with ⟨hjlo,hjhi⟩
  interval_cases j
  · rw [show backwardD β (Paper.parisiSchemeMeasure s) 2 (t,x) = backwardC β (Paper.parisiSchemeMeasure s) (t,x) by rfl,
      abs_of_nonneg hc]
    exact (by simpa using mul_le_mul_of_nonneg_right hk1 hc)
  · have hh := finiteScheme_D3_relative s β hβ hτ x
    simp only [backwardTauD,backwardTime_clock β hβ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hk3 hc)
  · have hh := finiteScheme_D4_relative s β hβ hτ x
    simp only [backwardTauD,backwardTime_clock β hβ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hk4 hc)
  · have hh := finiteScheme_D5_relative s β hβ hτ x
    simp only [backwardTauD,backwardTime_clock β hβ] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right hk5 hc)

/-- A beta-dependent relative bound for the actual arbitrary-measure
solution, stronger than the finite-measure statement needed in Lemma 3.4. -/
theorem backward_relative_derivative_bound (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) (hj : j ∈ Finset.Icc 2 5) :
    |backwardD β μ j (t,x)| ≤ backwardRelativeConstant β*backwardC β μ (t,x) := by
  let ν := preservingMeasure μ ∅
  have hν := tendsto_preservingMeasure μ ∅
  have hn : Tendsto (fun n => backwardD β (ν n) j (t,x)) atTop (𝓝 (backwardD β μ j (t,x))) := by
    have he := tendsto_backwardD_of_weak β (j-1) μ ν hν (t,x)
    simpa only [Nat.sub_add_cancel (by have := Finset.mem_Icc.mp hj; omega : 1 ≤ j)] using he
  have hc : Tendsto (fun n => backwardRelativeConstant β*backwardC β (ν n) (t,x)) atTop
      (𝓝 (backwardRelativeConstant β*backwardC β μ (t,x))) :=
    tendsto_const_nhds.mul (tendsto_backwardD_of_weak β 1 μ ν hν (t,x))
  apply le_of_tendsto_of_tendsto hn.abs hc
  apply Eventually.of_forall
  intro n
  have he := finiteScheme_relative_derivative_bound (preservingRSBScheme μ ∅ n) β hβ t x ht j hj
  simpa only [parisiSchemeMeasure_preservingRSBScheme] using he

theorem relative_derivative_bounds (β : ℝ) (hβ : β ≠ 0) :
    ∃ K > 0, ∀ (μ : Paper.ParisiMeasure) (t x : ℝ), t ∈ Icc (0 : ℝ) 1 →
      ∀ j ∈ Finset.Icc 2 5, |iteratedDeriv j (fun y => Paper.parisiPotential β μ (t,y)) x| ≤
        K*backwardC β μ (t,x) := by
  refine ⟨backwardRelativeConstant β,backwardRelativeConstant_pos β,fun μ t x ht j hj => ?_⟩
  rw [← Paper.parisiSpatialField_eq_iteratedDeriv β μ j t x ht]
  exact backward_relative_derivative_bound β hβ μ t x ht j hj

end FRSB
