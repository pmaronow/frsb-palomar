module

public import FRSB.BackwardsRegularity
public import FRSB.BackwardsCellInduction
public import FRSB.BackwardsTerminal
public import FRSB.ComparisonInterior

@[expose] public section

noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

theorem backwardCell_strict_of_mem {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) :
    s.q p < s.q (p+1) := by
  have hs := sq_pos_of_ne_zero hβ
  dsimp [backwardCellStart,backwardCellEnd] at hτ
  nlinarith [hτ.1,hτ.2]

theorem finiteCell_weightedQ_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hinitial : ∀ x, 0 ≤ backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p)
      (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      0 ≤ backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  let μ := Paper.parisiSchemeMeasure s
  let a := s.m p
  let A := backwardCellStart s β p
  let T := backwardCellEnd s β p
  let M := backwardRationalBound β
  let v := backwardTauP β μ a
  let vt : ℝ × ℝ → ℝ := fun q => deriv (fun r => v (r,q.2)) q.1
  let b : ℝ × ℝ → ℝ := fun q => a * backwardTauD β μ 1 q
  let κ : ℝ × ℝ → ℝ := fun q => -2 * backwardTauQ β μ a q
  have hm : a ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg hp,s.m_le_one hp⟩
  have hM : 0 < M := backwardRationalBound_pos β
  have hAT : A ≤ T := by
    have hq := s.q_mono p hp
    dsimp [A,T,backwardCellStart,backwardCellEnd]
    nlinarith [sq_nonneg β]
  have hmap : Icc A T ×ˢ comparisonSpace false ⊆ backwardTauStrip β := by
    intro q hq
    exact ⟨backwardCell_mem_global s β hp hq.1,mem_univ _⟩
  have hreg := (continuousOn_backwardTauP β hβ μ a).mono hmap
  have ht (τ : ℝ) (hτ : τ ∈ Ioo A T) (x : ℝ) : HasDerivAt (fun r => v (r,x)) (vt (τ,x)) τ := by
    have hd := hasDerivAt_finiteCell_backwardTauP s β hβ hp
      (backwardCell_strict_of_mem s β hβ hτ) hτ x
    exact hd.differentiableAt.hasDerivAt
  have hcmp := interval_supersolution_nonneg_interior false A T (1+2*M) M hAT
    (by linarith) hM.le v vt b κ hreg (fun τ hτ x _ => ht τ hτ x)
    (fun τ hτ x _ => (hasDerivAt_backwardTauP_spatial β hβ μ a τ x
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)).differentiableAt)
    (fun τ hτ x _ => by
      rw [deriv_backwardTauP_spatial β hβ μ a τ
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)]
      exact (hasDerivAt_backwardTauPx_spatial β hβ μ a τ x
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)).differentiableAt)
    (fun τ hτ x _ => (finiteScheme_backward_weighted_fields_bounded s β hβ a hm
      (backwardCell_mem_global s β hp hτ) x).1)
    (fun τ hτ x _ => (backwardTau_drift_outward β hβ μ a τ x hm
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)).trans (by linarith))
    (fun τ hτ x _ => by
      have hb := (finiteScheme_backward_fields_bounded s β hβ a hm
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩) x).2.1
      dsimp [κ]
      linarith [abs_le.mp hb])
    (fun τ hτ x _ => by
      have he := finiteCell_backward_weightedQ_equation s β hβ hp
        (backwardCell_strict_of_mem s β hβ hτ) hτ x
      dsimp [vt,v,b,κ,μ,a]
      nlinarith [he])
    (fun x _ => hinitial x) (by simp)
  intro τ hτ x
  exact hcmp (τ,x) ⟨hτ,mem_univ _⟩

theorem finiteScheme_weightedQ_nonneg_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ p ≤ k+1, ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      0 ≤ backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  apply backward_scheme_coefficient_induction s β
    (fun a τ => ∀ x, 0 ≤ backwardTauP β (Paper.parisiSchemeMeasure s) a (τ,x))
  · intro x
    have he := backwardQ_terminal β hβ (Paper.parisiSchemeMeasure s) x
    change 0 ≤ backwardTauD β (Paper.parisiSchemeMeasure s) 2 (0,x) *
      backwardTauQ β (Paper.parisiSchemeMeasure s) 1 (0,x)
    have hq : backwardTauQ β (Paper.parisiSchemeMeasure s) 1 (0,x) = 0 := by
      simpa [backwardTauQ,backwardTauD,backwardTime,backwardQ,backwardC] using he
    rw [hq,mul_zero]
  · exact fun p hp => finiteCell_weightedQ_nonneg s β hβ hp
  · intro p hp hprev x
    have hg : backwardCellStart s β p ∈ Icc (0 : ℝ) (β ^ 2) :=
      backwardCell_mem_global s β (by omega) ⟨le_rfl,by
        have hq := s.q_mono p (by omega)
        dsimp [backwardCellStart,backwardCellEnd]
        nlinarith [sq_nonneg β]⟩
    have hc := (backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s)
      (backwardCellStart s β p) x hg).1.ne'
    have he := (backward_atom_updates (s.m (p+1)) (s.m (p+1)-s.m p)
      (backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 4 (backwardCellStart s β p,x)) 0 hc).1
    rw [sub_sub_cancel] at he
    change 0 ≤ backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x) *
      backwardQJet (s.m p) _ _ _
    rw [he]
    exact add_nonneg (hprev x) (mul_nonneg (sub_nonneg.mpr (s.m_mono p hp)) (sq_nonneg _))

theorem finiteScheme_Q_nonneg_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    0 ≤ backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  have hp0 := finiteScheme_weightedQ_nonneg_on_cells s β hβ p hp τ hτ x
  exact nonneg_of_mul_nonneg_right hp0
    (backwardTauC_pos_le_one β hβ _ τ x (backwardCell_mem_global s β hp hτ)).1

end FRSB
