module

public import FRSB.BackwardsHxBounds
public import FRSB.BackwardsJetContinuity

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem tendsto_backwardHx_of_weak {A : Type*} {l : Filter A} (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (ν : A → Paper.ParisiMeasure) (hν : Tendsto ν l (𝓝 μ))
    (a t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => backwardHx β (ν n) a (t,x)) l (𝓝 (backwardHx β μ a (t,x))) := by
  have h2 := tendsto_backwardD_of_weak β 1 μ ν hν (t,x)
  have h3 := tendsto_backwardD_of_weak β 2 μ ν hν (t,x)
  have h4 := tendsto_backwardD_of_weak β 3 μ ν hν (t,x)
  have h5 := tendsto_backwardD_of_weak β 4 μ ν hν (t,x)
  exact tendsto_backwardHxJet h2 h3 h4 h5 (backwardC_pos β hβ μ t x ht).ne'

theorem finiteScheme_backwardHx_bounds {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    0 ≤ backwardHx β (Paper.parisiSchemeMeasure s) (Paper.parisiCDF (Paper.parisiSchemeMeasure s) t) (t,x) ∧
    backwardHx β (Paper.parisiSchemeMeasure s) (Paper.parisiCDF (Paper.parisiSchemeMeasure s) t) (t,x) ≤
      6*(1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) t) := by
  by_cases ht1 : t = 1
  · subst t
    rw [Paper.parisiCDF_eq_one_of_one_le _ le_rfl,backwardHx_terminal β hβ _ x]
    norm_num
  obtain ⟨p,hp,hcell,hq⟩ := Paper.exists_parisiFinite_right_cell s
    (t := t) ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩
  rw [Paper.parisiCDF_scheme_cell s hp hcell]
  have he := finiteScheme_Hx_bounds_on_cells s β hβ hp
    (backwardClock_cell_mem s β ⟨hcell.1,hcell.2.le⟩) x hx
  simpa only [backwardTime_clock β hβ] using he

/-- The sharp Hx bounds survive the genuine finite-support approximations,
which preserve the actual cumulative mass at the evaluation point. -/
theorem backwardHx_bounds (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    0 ≤ backwardHx β μ (Paper.parisiCDF μ t) (t,x) ∧
      backwardHx β μ (Paper.parisiCDF μ t) (t,x) ≤ 6*(1-Paper.parisiCDF μ t) := by
  let q : Paper.Overlap := ⟨t,ht⟩
  let S : Finset Paper.Overlap := {q}
  let ν := preservingMeasure μ S
  have hn := tendsto_backwardHx_of_weak β hβ μ ν (tendsto_preservingMeasure μ S)
    (Paper.parisiCDF μ t) t x ht
  have he (n : ℕ) : 0 ≤ backwardHx β (ν n) (Paper.parisiCDF μ t) (t,x) ∧
      backwardHx β (ν n) (Paper.parisiCDF μ t) (t,x) ≤ 6*(1-Paper.parisiCDF μ t) := by
    have hh := finiteScheme_backwardHx_bounds (preservingRSBScheme μ S n) β hβ t x ht hx
    rw [parisiSchemeMeasure_preservingRSBScheme] at hh
    have hm : Paper.parisiCDF (ν n) t = Paper.parisiCDF μ t :=
      preservingMeasure_cdf_mass μ S n q (by simp [S])
    change 0 ≤ backwardHx β (ν n) (Paper.parisiCDF (ν n) t) (t,x) ∧
      backwardHx β (ν n) (Paper.parisiCDF (ν n) t) (t,x) ≤ 6*(1-Paper.parisiCDF (ν n) t) at hh
    rw [hm] at hh
    exact hh
  exact ⟨ge_of_tendsto hn (Eventually.of_forall (fun n => (he n).1)),
    le_of_tendsto hn (Eventually.of_forall (fun n => (he n).2))⟩

/-- Proposition 3.1, for the actual arbitrary-measure Parisi potential.
The conclusion also holds when the cumulative mass is zero. -/
theorem backward_inequalities (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    Paper.parisiCDF μ t*backwardB β μ (t,x) ≤ backwardZ β μ (t,x) ∧
    backwardZ β μ (t,x) ≤ Paper.parisiCDF μ t*backwardB β μ (t,x)+1-Paper.parisiCDF μ t ∧
    Paper.parisiCDF μ t*backwardB β μ (t,x)+1-Paper.parisiCDF μ t ≤ 1 ∧
    0 ≤ backwardQ β μ (Paper.parisiCDF μ t) (t,x) ∧
    backwardQ β μ (Paper.parisiCDF μ t) (t,x) ≤ 1-Paper.parisiCDF μ t ∧
    0 ≤ backwardHx β μ (Paper.parisiCDF μ t) (t,x) ∧
    backwardHx β μ (Paper.parisiCDF μ t) (t,x) ≤ 6*(1-Paper.parisiCDF μ t) := by
  refine ⟨backwardZ_ge_massB β hβ μ t x ht hx,backwardZ_le_massB_add β hβ μ t x ht hx,?_,
    backwardQ_nonneg β hβ μ t x ht,backwardQ_le β hβ μ t x ht,
    (backwardHx_bounds β hβ μ t x ht hx).1,(backwardHx_bounds β hβ μ t x ht hx).2⟩
  have hb : backwardB β μ (t,x) ≤ 1 := by
    rw [backwardB_eq_gradient β μ t x ht]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using Paper.norm_parisiGradient_le_one β μ (t,x))).2
  nlinarith [mul_le_mul_of_nonneg_left hb (Paper.parisiCDF_nonneg μ t)]

end FRSB
