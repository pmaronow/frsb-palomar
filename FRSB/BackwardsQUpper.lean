module

public import FRSB.BackwardsCellFields

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem backwardCell_order {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) {p : ℕ} (hp : p ≤ k+1) : backwardCellStart s β p ≤ backwardCellEnd s β p := by
  have hq := s.q_mono p hp
  dsimp [backwardCellStart,backwardCellEnd]
  nlinarith [sq_nonneg β]

def backwardTauQUpper (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  (1-a)*backwardTauD β μ 2 q - backwardTauP β μ a q

theorem finiteCell_QUpper_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hinitial : ∀ x, 0 ≤ backwardTauQUpper β (Paper.parisiSchemeMeasure s) (s.m p)
      (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      0 ≤ backwardTauQUpper β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  let μ := Paper.parisiSchemeMeasure s
  let a := s.m p
  have hC := finiteCell_classical_D s β hβ hp 2 (by norm_num)
  have hP := finiteCell_classical_P s β hβ hp
  have hv : IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauQUpper β μ a) := hC.const_mul.sub hP
  have he := hv.supersolution_nonneg (backwardCell_order s β hp) false
    (backwardCellDrift β μ a) (fun q => -2*backwardTauQ β μ a q) 1 (by norm_num)
    (fun τ hτ x _ => backwardTau_drift_outward β hβ μ a τ x ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩))
    (fun τ hτ x _ => by
      have hq := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      dsimp [μ,a]
      linarith)
    (fun τ hτ x _ => by
      change 0 ≤ backwardGenerator (backwardCellDrift β μ a)
        (fun q => (1-a)*backwardTauD β μ 2 q - backwardTauP β μ a q) (τ,x) -
          (-2*backwardTauQ β μ a (τ,x)) * backwardTauQUpper β μ a (τ,x)
      rw [backwardGenerator_sub hC.const_mul hP (backwardCellDrift β μ a) hτ x,
        backwardGenerator_const_mul hC (backwardCellDrift β μ a) hτ x,finiteCell_generator_C s β hβ hp hτ x,
        finiteCell_generator_P s β hβ hp hτ x]
      have hq := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      have hc := (backwardTauC_pos_le_one β hβ μ τ x
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)).1.le
      have ha0 := s.m_nonneg hp
      have ha1 := s.m_le_one hp
      have hs : 0 ≤ (1-a)*backwardTauD β μ 2 (τ,x)*
          (a*backwardTauD β μ 2 (τ,x)+2*backwardTauQ β μ a (τ,x)) := by
        exact mul_nonneg (mul_nonneg (sub_nonneg.mpr ha1) hc)
          (add_nonneg (mul_nonneg ha0 hc) (by positivity))
      dsimp [backwardTauQUpper,backwardTauP] at *
      nlinarith)
    (fun x _ => hinitial x) (by simp)
  exact fun τ hτ x => he τ hτ x (mem_univ _)

theorem finiteScheme_QUpper_nonneg_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ p ≤ k+1, ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      0 ≤ backwardTauQUpper β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  apply backward_scheme_coefficient_induction s β
    (fun a τ => ∀ x, 0 ≤ backwardTauQUpper β (Paper.parisiSchemeMeasure s) a (τ,x))
  · intro x
    have he := backwardQ_terminal β hβ (Paper.parisiSchemeMeasure s) x
    have hq : backwardTauQ β (Paper.parisiSchemeMeasure s) 1 (0,x) = 0 := by
      simpa [backwardTauQ,backwardTauD,backwardTime,backwardQ,backwardC] using he
    simp [backwardTauQUpper,backwardTauP,hq]
  · exact fun p hp => finiteCell_QUpper_nonneg s β hβ hp
  · intro p hp hprev x
    have hg := backwardCell_mem_global s β (by omega : p ≤ k+1)
      ⟨le_rfl,backwardCell_order s β (by omega : p ≤ k+1)⟩
    have hc := backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) (backwardCellStart s β p) x hg
    have he := (backward_barrier_atom_updates (s.m (p+1)) (s.m (p+1)-s.m p) 0
      (backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 4 (backwardCellStart s β p,x)) 0 hc.1.ne').1
    rw [sub_sub_cancel] at he
    change 0 ≤ (1-s.m p)*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x) -
      backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x) * backwardQJet (s.m p) _ _ _
    rw [he]
    exact add_nonneg (hprev x) (mul_nonneg
      (mul_nonneg (sub_nonneg.mpr (s.m_mono p hp)) hc.1.le) (sub_nonneg.mpr hc.2))

theorem finiteScheme_Q_le_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) ≤ 1-s.m p := by
  have hv := finiteScheme_QUpper_nonneg_on_cells s β hβ p hp τ hτ x
  have hc := (backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) τ x
    (backwardCell_mem_global s β hp hτ)).1
  dsimp [backwardTauQUpper,backwardTauP] at hv
  nlinarith

theorem finiteScheme_backwardQ_le {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardQ β (Paper.parisiSchemeMeasure s)
      (Paper.parisiCDF (Paper.parisiSchemeMeasure s) t) (t,x) ≤
      1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) t := by
  by_cases ht1 : t = 1
  · subst t
    rw [Paper.parisiCDF_eq_one_of_one_le _ le_rfl,backwardQ_terminal β hβ _ x]
    norm_num
  obtain ⟨p,hp,hcell,hq⟩ := Paper.exists_parisiFinite_right_cell s
    (t := t) ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩
  rw [Paper.parisiCDF_scheme_cell s hp hcell]
  have he := finiteScheme_Q_le_on_cells s β hβ hp (backwardClock_cell_mem s β ⟨hcell.1,hcell.2.le⟩) x
  simpa only [backwardTauQ,backwardTauD,backwardTime_clock β hβ,backwardQ,backwardC] using he

theorem backwardQ_le (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    backwardQ β μ (Paper.parisiCDF μ t) (t,x) ≤ 1-Paper.parisiCDF μ t := by
  let q : Paper.Overlap := ⟨t,ht⟩
  let S : Finset Paper.Overlap := {q}
  let ν := preservingMeasure μ S
  have hn := tendsto_backwardQ_of_weak β hβ μ ν (tendsto_preservingMeasure μ S)
    (Paper.parisiCDF μ t) t x ht
  apply le_of_tendsto hn
  apply Eventually.of_forall
  intro n
  have he := finiteScheme_backwardQ_le (preservingRSBScheme μ S n) β hβ t x ht
  rw [parisiSchemeMeasure_preservingRSBScheme] at he
  have hm : Paper.parisiCDF (ν n) t = Paper.parisiCDF μ t :=
    preservingMeasure_cdf_mass μ S n q (by simp [S])
  change backwardQ β (ν n) (Paper.parisiCDF (ν n) t) (t,x) ≤ 1-Paper.parisiCDF (ν n) t at he
  rw [hm] at he
  exact he

end FRSB
