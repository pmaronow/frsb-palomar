module

public import FRSB.BackwardsZUpper

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardTauRUpper (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  (6*(1-a))*backwardTauD β μ 2 q - backwardTauR β μ a q

theorem backwardRJet_atom_update (m δ C D E F : ℝ) (hC : C ≠ 0) :
    backwardRJet (m-δ) C D E F = backwardRJet m C D E F + 6*δ*C^2*backwardZJet C D := by
  rw [backwardRJet_eq_weightedHx _ _ _ _ _ hC,backwardRJet_eq_weightedHx _ _ _ _ _ hC]
  exact (backward_atom_updates m δ C D E F hC).2.2

theorem finiteCell_R_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hinitial : ∀ x ≥ 0, 0 ≤ backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p)
      (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x ≥ 0,
      0 ≤ backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  let μ := Paper.parisiSchemeMeasure s
  let a := s.m p
  have hv := finiteCell_classical_R s β hβ hp
  have he := hv.supersolution_nonneg (backwardCell_order s β hp) true
    (backwardCellDrift β μ a) (fun q => -5*backwardTauQ β μ a q) 1 (by norm_num)
    (fun τ hτ x _ => backwardTau_drift_outward β hβ μ a τ x ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩))
    (fun τ hτ x _ => by
      have hq := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      dsimp [μ,a]
      linarith)
    (fun τ hτ x hx => by
      rw [finiteCell_generator_R s β hβ hp hτ x]
      have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
      have hc := (backwardTauC_pos_le_one β hβ μ τ x hg).1.le
      have hz : 0 ≤ backwardTauZ β μ (τ,x) :=
        backwardZ_nonneg β hβ μ _ x (backwardTime_mem β hβ τ hg) (show 0 < x from hx).le
      have hs : 0 ≤ 6*backwardTauD β μ 2 (τ,x)*backwardTauZ β μ (τ,x)*backwardTauQ β μ a (τ,x)^2 := by positivity
      nlinarith)
    (fun x hx => hinitial x hx)
    (fun _ τ hτ => by rw [backwardTauR_at_zero β hβ μ a τ (backwardCell_mem_global s β hp hτ)])
  exact fun τ hτ x hx => he τ hτ x hx

theorem finiteScheme_R_nonneg_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ p ≤ k+1, ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x ≥ 0,
      0 ≤ backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  apply backward_scheme_coefficient_induction s β
    (fun a τ => ∀ x ≥ 0, 0 ≤ backwardTauR β (Paper.parisiSchemeMeasure s) a (τ,x))
  · intro x hx
    rw [backwardTauR_eq_weightedHx β hβ _ 1 0 x (by constructor <;> positivity)]
    have he : backwardTime β 0 = 1 := by simp [backwardTime]
    rw [he,backwardHx_terminal β hβ _ x,mul_zero]
  · exact fun p hp => finiteCell_R_nonneg s β hβ hp
  · intro p hp hprev x hx
    have hg := backwardCell_mem_global s β (by omega : p ≤ k+1)
      ⟨le_rfl,backwardCell_order s β (by omega : p ≤ k+1)⟩
    have hc := (backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) (backwardCellStart s β p) x hg).1.ne'
    have hz : 0 ≤ backwardTauZ β (Paper.parisiSchemeMeasure s) (backwardCellStart s β p,x) :=
      backwardZ_nonneg β hβ _ _ x (backwardTime_mem β hβ _ hg) hx
    have he := backwardRJet_atom_update (s.m (p+1)) (s.m (p+1)-s.m p)
      (backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 4 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 5 (backwardCellStart s β p,x)) hc
    rw [sub_sub_cancel] at he
    change 0 ≤ backwardRJet (s.m p) _ _ _ _
    rw [he]
    have hd := sub_nonneg.mpr (s.m_mono p hp)
    exact add_nonneg (hprev x hx) (by positivity)

theorem finiteCell_RUpper_nonneg {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1)
    (hinitial : ∀ x ≥ 0, 0 ≤ backwardTauRUpper β (Paper.parisiSchemeMeasure s) (s.m p)
      (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x ≥ 0,
      0 ≤ backwardTauRUpper β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  let μ := Paper.parisiSchemeMeasure s
  let a := s.m p
  let b := backwardCellDrift β μ a
  have hC := finiteCell_classical_D s β hβ hp 2 (by norm_num)
  have hR := finiteCell_classical_R s β hβ hp
  have hv : IsBoundedClassicalCell (backwardCellStart s β p) (backwardCellEnd s β p)
      (backwardTauRUpper β μ a) := hC.const_mul.sub hR
  have he := hv.supersolution_nonneg (backwardCell_order s β hp) true b
    (fun q => -5*backwardTauQ β μ a q) 1 (by norm_num)
    (fun τ hτ x _ => backwardTau_drift_outward β hβ μ a τ x ⟨s.m_nonneg hp,s.m_le_one hp⟩
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩))
    (fun τ hτ x _ => by
      have hq := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      dsimp [μ,a]
      linarith)
    (fun τ hτ x hx => by
      change 0 ≤ backwardGenerator b
        (fun q => (6*(1-a))*backwardTauD β μ 2 q - backwardTauR β μ a q) (τ,x) -
          (-5*backwardTauQ β μ a (τ,x)) * backwardTauRUpper β μ a (τ,x)
      rw [backwardGenerator_sub hC.const_mul hR b hτ x,backwardGenerator_const_mul hC b hτ x,
        finiteCell_generator_C s β hβ hp hτ x,finiteCell_generator_R s β hβ hp hτ x]
      have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
      have hc := (backwardTauC_pos_le_one β hβ μ τ x hg).1.le
      have hz0 : 0 ≤ backwardTauZ β μ (τ,x) :=
        backwardZ_nonneg β hβ μ _ x (backwardTime_mem β hβ τ hg) (show 0 < x from hx).le
      have hz1 : backwardTauZ β μ (τ,x) ≤ 1 :=
        backwardZ_le_one β hβ μ _ x (backwardTime_mem β hβ τ hg) (show 0 < x from hx).le
      have hq0 := finiteScheme_Q_nonneg_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      have hq1 := finiteScheme_Q_le_on_cells s β hβ hp ⟨hτ.1.le,hτ.2.le⟩ x
      have hs := backward_last_source_nonneg a (backwardTauD β μ 2 (τ,x))
        (backwardTauQ β μ a (τ,x)) (backwardTauZ β μ (τ,x))
        (s.m_nonneg hp) (s.m_le_one hp) hc hq0 hq1 hz0 hz1
      dsimp [backwardTauRUpper]
      nlinarith)
    (fun x hx => hinitial x hx)
    (fun _ τ hτ => by
      rw [backwardTauRUpper,backwardTauR_at_zero β hβ μ a τ (backwardCell_mem_global s β hp hτ)]
      have hc := (backwardTauC_pos_le_one β hβ μ τ 0 (backwardCell_mem_global s β hp hτ)).1.le
      have ha1 := s.m_le_one hp
      dsimp [a]
      simpa only [sub_zero] using mul_nonneg
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (sub_nonneg.mpr ha1)) hc)
  exact fun τ hτ x hx => he τ hτ x hx

theorem finiteScheme_RUpper_nonneg_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ p ≤ k+1, ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x ≥ 0,
      0 ≤ backwardTauRUpper β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) := by
  apply backward_scheme_coefficient_induction s β
    (fun a τ => ∀ x ≥ 0, 0 ≤ backwardTauRUpper β (Paper.parisiSchemeMeasure s) a (τ,x))
  · intro x hx
    have he : backwardTauR β (Paper.parisiSchemeMeasure s) 1 (0,x) = 0 := by
      rw [backwardTauR_eq_weightedHx β hβ _ 1 0 x (by constructor <;> positivity)]
      have he : backwardTime β 0 = 1 := by simp [backwardTime]
      rw [he,backwardHx_terminal β hβ _ x,mul_zero]
    simp [backwardTauRUpper,he]
  · exact fun p hp => finiteCell_RUpper_nonneg s β hβ hp
  · intro p hp hprev x hx
    have hg := backwardCell_mem_global s β (by omega : p ≤ k+1)
      ⟨le_rfl,backwardCell_order s β (by omega : p ≤ k+1)⟩
    have hc := backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) (backwardCellStart s β p) x hg
    have hz0 : 0 ≤ backwardTauZ β (Paper.parisiSchemeMeasure s) (backwardCellStart s β p,x) :=
      backwardZ_nonneg β hβ _ _ x (backwardTime_mem β hβ _ hg) hx
    have hz1 : backwardTauZ β (Paper.parisiSchemeMeasure s) (backwardCellStart s β p,x) ≤ 1 :=
      backwardZ_le_one β hβ _ _ x (backwardTime_mem β hβ _ hg) hx
    have hcz : backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x) *
        backwardTauZ β (Paper.parisiSchemeMeasure s) (backwardCellStart s β p,x) ≤ 1 :=
      mul_le_one₀ hc.2 hz0 hz1
    have he := backwardRJet_atom_update (s.m (p+1)) (s.m (p+1)-s.m p)
      (backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 4 (backwardCellStart s β p,x))
      (backwardTauD β (Paper.parisiSchemeMeasure s) 5 (backwardCellStart s β p,x)) hc.1.ne'
    rw [sub_sub_cancel] at he
    have he' : backwardTauRUpper β (Paper.parisiSchemeMeasure s) (s.m p) (backwardCellStart s β p,x) =
        backwardTauRUpper β (Paper.parisiSchemeMeasure s) (s.m (p+1)) (backwardCellStart s β p,x) +
          6*(s.m (p+1)-s.m p)*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x)*
            (1-backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x)*
              backwardTauZ β (Paper.parisiSchemeMeasure s) (backwardCellStart s β p,x)) := by
      dsimp [backwardTauRUpper,backwardTauR]
      rw [he]
      dsimp [backwardTauZ]
      ring
    rw [he']
    have hd := sub_nonneg.mpr (s.m_mono p hp)
    exact add_nonneg (hprev x hx) (mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hd) hc.1.le) (sub_nonneg.mpr hcz))

theorem finiteScheme_Hx_bounds_on_cells {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) (hx : 0 ≤ x) :
    0 ≤ backwardHx β (Paper.parisiSchemeMeasure s) (s.m p) (backwardTime β τ,x) ∧
    backwardHx β (Paper.parisiSchemeMeasure s) (s.m p) (backwardTime β τ,x) ≤ 6*(1-s.m p) := by
  have hg := backwardCell_mem_global s β hp hτ
  have hc := (backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) τ x hg).1
  have h0 := finiteScheme_R_nonneg_on_cells s β hβ p hp τ hτ x hx
  have h1 := finiteScheme_RUpper_nonneg_on_cells s β hβ p hp τ hτ x hx
  dsimp [backwardTauRUpper] at h1
  rw [backwardTauR_eq_weightedHx β hβ _ (s.m p) τ x hg] at h0 h1
  constructor <;> nlinarith

end FRSB
