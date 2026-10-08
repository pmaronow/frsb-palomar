module

public import FRSB.BackwardsLower
public import FRSB.BackwardsClassicalCell

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardCellDrift (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  a * backwardTauD β μ 1 q

theorem finiteCell_classical_D {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) (j : ℕ) (hj : 0 < j) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauD β (Paper.parisiSchemeMeasure s) j) := by
  refine ⟨(continuous_backwardTauD β _ j).continuousOn,?_,?_,?_,?_⟩
  · refine ⟨uniformSpatialConstant β (j-1),(uniformSpatialConstant_pos β _).le,fun t ht x => ?_⟩
    have hh := backwardTauD_uniform_bound β (Paper.parisiSchemeMeasure s) (j-1) (t,x)
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ j)] using hh
  · intro t ht x
    exact (hasDerivAt_finiteCell_backwardTauD s β hβ hp
      (backwardCell_strict_of_mem s β hβ ht) j ht x).differentiableAt
  · intro t ht x
    exact (hasDerivAt_backwardTauD_spatial β hβ _ j t x (backwardCell_mem_global s β hp ht)).differentiableAt
  · intro t ht x
    rw [deriv_backwardTauD_spatial β hβ _ j t (backwardCell_mem_global s β hp ht)]
    exact (hasDerivAt_backwardTauD_spatial β hβ _ (j+1) t x
      (backwardCell_mem_global s β hp ht)).differentiableAt

theorem finiteCell_classical_Z {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauZ β (Paper.parisiSchemeMeasure s)) := by
  refine ⟨(continuousOn_backwardTauZ β hβ _).mono ?_,?_,?_,?_,?_⟩
  · exact fun q hq => ⟨backwardCell_mem_global s β hp hq.1,mem_univ _⟩
  · refine ⟨backwardRationalBound β,(backwardRationalBound_pos β).le,fun t ht x => ?_⟩
    exact (finiteScheme_backward_fields_bounded s β hβ 0 (by norm_num)
      (backwardCell_mem_global s β hp ht) x).1
  · intro t ht x
    exact (hasDerivAt_finiteCell_backwardTauZ s β hβ hp
      (backwardCell_strict_of_mem s β hβ ht) ht x).differentiableAt
  · intro t ht x
    exact (hasDerivAt_backwardTauZ_spatial β hβ _ t x
      (backwardCell_mem_global s β hp ht)).differentiableAt
  · intro t ht x
    exact (hasDerivAt_deriv_backwardTauZ_spatial β hβ _ t x
      (backwardCell_mem_global s β hp ht)).differentiableAt

theorem finiteCell_classical_P {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p)) := by
  refine ⟨(continuousOn_backwardTauP β hβ _ _).mono ?_,?_,?_,?_,?_⟩
  · exact fun q hq => ⟨backwardCell_mem_global s β hp hq.1,mem_univ _⟩
  · refine ⟨backwardRationalBound β,(backwardRationalBound_pos β).le,fun t ht x => ?_⟩
    exact (finiteScheme_backward_weighted_fields_bounded s β hβ (s.m p) ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ht) x).1
  · intro t ht x
    exact (hasDerivAt_finiteCell_backwardTauP s β hβ hp
      (backwardCell_strict_of_mem s β hβ ht) ht x).differentiableAt
  · intro t ht x
    exact (hasDerivAt_backwardTauP_spatial β hβ _ (s.m p) t x
      (backwardCell_mem_global s β hp ht)).differentiableAt
  · intro t ht x
    rw [deriv_backwardTauP_spatial β hβ _ (s.m p) t (backwardCell_mem_global s β hp ht)]
    exact (hasDerivAt_backwardTauPx_spatial β hβ _ (s.m p) t x
      (backwardCell_mem_global s β hp ht)).differentiableAt

theorem finiteCell_classical_R {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) :
    IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p)) := by
  refine ⟨(continuousOn_backwardTauR β hβ _ _).mono ?_,?_,?_,?_,?_⟩
  · exact fun q hq => ⟨backwardCell_mem_global s β hp hq.1,mem_univ _⟩
  · refine ⟨backwardRationalBound β,(backwardRationalBound_pos β).le,fun t ht x => ?_⟩
    exact (finiteScheme_backward_weighted_fields_bounded s β hβ (s.m p) ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ht) x).2
  · intro t ht x
    exact (hasDerivAt_finiteCell_backwardTauR s β hβ hp
      (backwardCell_strict_of_mem s β hβ ht) ht x).differentiableAt
  · intro t ht x
    exact (hasDerivAt_backwardTauR_spatial β hβ _ (s.m p) t x
      (backwardCell_mem_global s β hp ht)).differentiableAt
  · intro t ht x
    rw [deriv_backwardTauR_spatial β hβ _ (s.m p) t (backwardCell_mem_global s β hp ht)]
    exact (hasDerivAt_backwardTauRx_spatial β hβ _ (s.m p) t x
      (backwardCell_mem_global s β hp ht)).differentiableAt

theorem finiteCell_generator_C {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {t : ℝ}
    (ht : t ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 2) (t,x) =
      s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (t,x) ^ 2 := by
  dsimp [backwardGenerator,backwardCellDrift]
  rw [(hasDerivAt_finiteCell_backwardTauD s β hβ hp (backwardCell_strict_of_mem s β hβ ht) 2 ht x).deriv,
    deriv2_backwardTauD_spatial β hβ _ 2 t x (backwardCell_mem_global s β hp ⟨ht.1.le,ht.2.le⟩),
    (hasDerivAt_backwardTauD_spatial β hβ _ 2 t x (backwardCell_mem_global s β hp ⟨ht.1.le,ht.2.le⟩)).deriv,
    backwardTauForcing_two]
  dsimp [backwardCtJet]
  ring

theorem finiteCell_generator_B {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {t : ℝ}
    (ht : t ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 1) (t,x) = 0 := by
  dsimp [backwardGenerator,backwardCellDrift]
  rw [(hasDerivAt_finiteCell_backwardTauD s β hβ hp (backwardCell_strict_of_mem s β hβ ht) 1 ht x).deriv,
    deriv2_backwardTauD_spatial β hβ _ 1 t x (backwardCell_mem_global s β hp ⟨ht.1.le,ht.2.le⟩),
    (hasDerivAt_backwardTauD_spatial β hβ _ 1 t x (backwardCell_mem_global s β hp ⟨ht.1.le,ht.2.le⟩)).deriv,
    backwardTauForcing_one]
  ring

theorem finiteCell_generator_P {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {t : ℝ}
    (ht : t ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p)) (t,x) =
      -2 * backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (t,x) *
        backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (t,x) :=
  finiteCell_backward_weightedQ_equation s β hβ hp (backwardCell_strict_of_mem s β hβ ht) ht x

theorem finiteCell_generator_Z {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {t : ℝ}
    (ht : t ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauZ β (Paper.parisiSchemeMeasure s)) (t,x) =
      -2 * backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (t,x) *
        backwardTauZ β (Paper.parisiSchemeMeasure s) (t,x) :=
  finiteCell_backward_z_equation s β hβ hp (backwardCell_strict_of_mem s β hβ ht) ht x

theorem finiteCell_generator_R {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {t : ℝ}
    (ht : t ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p)) (t,x) =
      -5 * backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (t,x) *
        backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (t,x) +
      6 * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (t,x) *
        backwardTauZ β (Paper.parisiSchemeMeasure s) (t,x) *
        backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (t,x) ^ 2 :=
  finiteCell_backward_weightedHx_equation s β hβ hp (backwardCell_strict_of_mem s β hβ ht) ht x

end FRSB
