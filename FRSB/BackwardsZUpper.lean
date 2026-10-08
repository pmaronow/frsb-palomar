module

public import FRSB.BackwardsQUpper

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardTauZUpper (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  a*backwardTauD β μ 1 q - (a-1) - backwardTauZ β μ q

theorem finiteCell_ZUpper_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hinitial : ∀ x ≥ 0, 0 ≤ backwardTauZUpper β (Paper.parisiSchemeMeasure s) (s.m p)
      (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x ≥ 0,
      0 ≤ backwardTauZUpper β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  let μ := Paper.parisiSchemeMeasure s
  let a := s.m p
  let A := backwardCellStart s β p
  let T := backwardCellEnd s β p
  let b := backwardCellDrift β μ a
  have hB := finiteCell_classical_D s β hβ hp 1 (by norm_num)
  have hZ := finiteCell_classical_Z s β hβ hp
  have hcst := IsBoundedClassicalCell.const A T (a-1)
  have hv : IsBoundedClassicalCell A T (backwardTauZUpper β μ a) := (hB.const_mul.sub hcst).sub hZ
  have he := hv.supersolution_nonneg (backwardCell_order s β hp) true b
    (fun q => -2*backwardTauQ β μ a q) 1 (by norm_num)
    (fun τ hτ x _ => backwardTau_drift_outward β hβ μ a τ x ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩))
    (fun τ hτ x _ => by
      have hq := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      dsimp [μ,a]
      linarith)
    (fun τ hτ x hx => by
      change 0 ≤ backwardGenerator b
        (fun q => (a*backwardTauD β μ 1 q - (a-1)) - backwardTauZ β μ q) (τ,x) -
          (-2*backwardTauQ β μ a (τ,x)) * backwardTauZUpper β μ a (τ,x)
      rw [backwardGenerator_sub (hB.const_mul.sub hcst) hZ b hτ x,
        backwardGenerator_sub hB.const_mul hcst b hτ x,
        backwardGenerator_const_mul hB b hτ x,backwardGenerator_const,
        finiteCell_generator_B s β hβ hp hτ x,finiteCell_generator_Z s β hβ hp hτ x]
      have hq := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      have hglobal := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
      have ht := backwardTime_mem β hβ τ hglobal
      have hx0 : 0 ≤ x := (show 0 < x from hx).le
      have hB0 : 0 ≤ backwardTauD β μ 1 (τ,x) := backwardB_nonneg β hβ μ _ x ht hx0
      have ha0 := s.m_nonneg hp
      have ha1 := s.m_le_one hp
      have hs : 0 ≤ 2*backwardTauQ β μ a (τ,x)*(a*backwardTauD β μ 1 (τ,x)+1-a) :=
        mul_nonneg (by positivity) (by nlinarith [mul_nonneg ha0 hB0])
      dsimp [backwardTauZUpper]
      nlinarith)
    (fun x hx => hinitial x hx)
    (fun _ τ hτ => by
      have ht := backwardTime_mem β hβ τ (backwardCell_mem_global s β hp hτ)
      have hB0 : backwardTauD β μ 1 (τ,0) = 0 := backwardB_at_zero β hβ μ _ ht
      rw [backwardTauZUpper,hB0,backwardTauZ_at_zero β hβ μ τ (backwardCell_mem_global s β hp hτ)]
      have ha1 := s.m_le_one hp
      dsimp [a]
      linarith)
  exact fun τ hτ x hx => he τ hτ x hx

theorem finiteScheme_ZUpper_nonneg_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ p ≤ k+1, ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x ≥ 0,
      0 ≤ backwardTauZUpper β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  apply backward_scheme_coefficient_induction s β
    (fun a τ => ∀ x ≥ 0, 0 ≤ backwardTauZUpper β (Paper.parisiSchemeMeasure s) a (τ,x))
  · intro x hx
    have hB : backwardTauD β (Paper.parisiSchemeMeasure s) 1 (0,x) = Real.tanh x := by
      simpa [backwardTauD,backwardTime,backwardB] using backwardB_terminal β (Paper.parisiSchemeMeasure s) x
    have hZ : backwardTauZ β (Paper.parisiSchemeMeasure s) (0,x) = Real.tanh x := by
      simpa [backwardTauZ,backwardTauD,backwardTime,backwardZ,backwardC] using
        backwardZ_terminal β (Paper.parisiSchemeMeasure s) x
    simp [backwardTauZUpper,hB,hZ]
  · exact fun p hp => finiteCell_ZUpper_nonneg s β hβ hp
  · intro p hp hprev x hx
    have hg := backwardCell_mem_global s β (by omega : p ≤ k+1)
      ⟨le_rfl,backwardCell_order s β (by omega : p ≤ k+1)⟩
    have hB := (abs_le.mp (backwardTauB_abs_le_one β hβ (Paper.parisiSchemeMeasure s)
      (backwardCellStart s β p) x hg)).2
    have hdelta := sub_nonneg.mpr (s.m_mono p hp)
    have he : backwardTauZUpper β (Paper.parisiSchemeMeasure s) (s.m p) (backwardCellStart s β p,x) =
        backwardTauZUpper β (Paper.parisiSchemeMeasure s) (s.m (p+1)) (backwardCellStart s β p,x) +
          (s.m (p+1)-s.m p)*(1-backwardTauD β (Paper.parisiSchemeMeasure s) 1 (backwardCellStart s β p,x)) := by
      dsimp [backwardTauZUpper]
      ring
    rw [he]
    exact add_nonneg (hprev x hx) (mul_nonneg hdelta (sub_nonneg.mpr hB))

theorem finiteScheme_backwardZ_le {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    backwardZ β (Paper.parisiSchemeMeasure s) (t,x) ≤
      Paper.parisiCDF (Paper.parisiSchemeMeasure s) t * backwardB β (Paper.parisiSchemeMeasure s) (t,x) +
        1-Paper.parisiCDF (Paper.parisiSchemeMeasure s) t := by
  by_cases ht1 : t = 1
  · subst t
    rw [Paper.parisiCDF_eq_one_of_one_le _ le_rfl,backwardZ_terminal,backwardB_terminal]
    linarith
  obtain ⟨p,hp,hcell,hq⟩ := Paper.exists_parisiFinite_right_cell s
    (t := t) ⟨ht.1,lt_of_le_of_ne ht.2 ht1⟩
  rw [Paper.parisiCDF_scheme_cell s hp hcell]
  have he := finiteScheme_ZUpper_nonneg_on_cells s β hβ p hp (backwardClock β t)
    (backwardClock_cell_mem s β ⟨hcell.1,hcell.2.le⟩) x hx
  simp only [backwardTauZUpper,backwardTauZ,backwardTauD,backwardTime_clock β hβ] at he
  change backwardZ β (Paper.parisiSchemeMeasure s) (t,x) ≤ s.m p*backwardB β (Paper.parisiSchemeMeasure s) (t,x)+1-s.m p
  change 0 ≤ s.m p*backwardB β (Paper.parisiSchemeMeasure s) (t,x)-(s.m p-1)-backwardZ β (Paper.parisiSchemeMeasure s) (t,x) at he
  linarith

theorem tendsto_backwardZ_of_weak {A : Type*} {l : Filter A} (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (ν : A → Paper.ParisiMeasure) (hν : Tendsto ν l (𝓝 μ))
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Tendsto (fun n => backwardZ β (ν n) (t,x)) l (𝓝 (backwardZ β μ (t,x))) :=
  (tendsto_backwardD_of_weak β 2 μ ν hν (t,x)).neg.div
    (tendsto_const_nhds.mul (tendsto_backwardD_of_weak β 1 μ ν hν (t,x)))
    (mul_ne_zero (by norm_num) (backwardC_pos β hβ μ t x ht).ne')

theorem backwardZ_le_massB_add (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    backwardZ β μ (t,x) ≤ Paper.parisiCDF μ t*backwardB β μ (t,x)+1-Paper.parisiCDF μ t := by
  let q : Paper.Overlap := ⟨t,ht⟩
  let S : Finset Paper.Overlap := {q}
  let ν := preservingMeasure μ S
  have hB : Tendsto (fun n => backwardB β (ν n) (t,x)) atTop (𝓝 (backwardB β μ (t,x))) :=
    tendsto_backwardD_of_weak β 0 μ ν (tendsto_preservingMeasure μ S) (t,x)
  have hZ := tendsto_backwardZ_of_weak β hβ μ ν (tendsto_preservingMeasure μ S) t x ht
  have hn : Tendsto (fun n => Paper.parisiCDF μ t*backwardB β (ν n) (t,x)-
      (Paper.parisiCDF μ t-1)-backwardZ β (ν n) (t,x)) atTop
      (𝓝 (Paper.parisiCDF μ t*backwardB β μ (t,x)-(Paper.parisiCDF μ t-1)-backwardZ β μ (t,x))) :=
    ((tendsto_const_nhds.mul hB).sub tendsto_const_nhds).sub hZ
  have hs : 0 ≤ Paper.parisiCDF μ t*backwardB β μ (t,x)-(Paper.parisiCDF μ t-1)-backwardZ β μ (t,x) := by
    apply ge_of_tendsto hn
    apply Eventually.of_forall
    intro n
    have he := finiteScheme_backwardZ_le (preservingRSBScheme μ S n) β hβ t x ht hx
    rw [parisiSchemeMeasure_preservingRSBScheme] at he
    have hm : Paper.parisiCDF (ν n) t = Paper.parisiCDF μ t :=
      preservingMeasure_cdf_mass μ S n q (by simp [S])
    change backwardZ β (ν n) (t,x) ≤ Paper.parisiCDF (ν n) t*backwardB β (ν n) (t,x)+1-Paper.parisiCDF (ν n) t at he
    rw [hm] at he
    linarith
  linarith

theorem backwardZ_le_one (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x) : backwardZ β μ (t,x) ≤ 1 := by
  have hb : backwardB β μ (t,x) ≤ 1 := by
    rw [backwardB_eq_gradient β μ t x ht]
    exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using Paper.norm_parisiGradient_le_one β μ (t,x))).2
  have hm := Paper.parisiCDF_nonneg μ t
  have he := backwardZ_le_massB_add β hβ μ t x ht hx
  nlinarith [mul_le_mul_of_nonneg_left hb hm]

end FRSB
