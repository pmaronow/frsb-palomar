module

public import FRSB.BackwardsEquations
public import FRSB.BackwardsRelativeInterior

@[expose] public section

noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

theorem backwardTau_drift_outward (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ x : ℝ) (ha : a ∈ Icc (0 : ℝ) 1) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    a * backwardTauD β μ 1 (τ,x) * sign x ≤ 1 := by
  have hB := abs_le.mp (backwardTauB_abs_le_one β hβ μ τ x hτ)
  have hmul : |a * backwardTauD β μ 1 (τ,x)| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha.1]
    exact (mul_le_mul_of_nonneg_left (backwardTauB_abs_le_one β hβ μ τ x hτ) ha.1).trans
      (by simpa using ha.2)
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [sign_neg hx]
    norm_num
    linarith [(abs_le.mp hmul).1]
  · simp [hx]
  · simpa [sign_pos hx] using (abs_le.mp hmul).2

/-- Actual differentiated finite-measure PDE comparison, with only its scalar
forcing estimate and initial barrier left as reusable algebraic inputs. -/
theorem finiteCell_relative_barrier {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1) (j : ℕ) (hj : 0 < j)
    (r J L σ : ℝ) (hr : 1 ≤ r) (hJ : 0 ≤ J) (hL : 1 ≤ L) (hσ : |σ| ≤ 1)
    (F : ℝ × ℝ → ℝ)
    (hforcing : ∀ τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      backwardTauForcing β (Paper.parisiSchemeMeasure s) (s.m p) j (τ,x) -
        backwardTauD β (Paper.parisiSchemeMeasure s) (j+2) (τ,x) / 2 -
        s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 1 (τ,x) *
          backwardTauD β (Paper.parisiSchemeMeasure s) (j+1) (τ,x) =
      r * s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) *
        backwardTauD β (Paper.parisiSchemeMeasure s) j (τ,x) + F (τ,x))
    (hF : ∀ τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      |F (τ,x)| ≤ J * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x))
    (hinitial : ∀ x, σ * backwardTauD β (Paper.parisiSchemeMeasure s) j (backwardCellStart s β p,x) ≤
      relativeFactor L (r+J) (backwardCellStart s β p) *
        backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      σ * backwardTauD β (Paper.parisiSchemeMeasure s) j (τ,x) ≤
        relativeFactor L (r+J) τ * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  have hqle := s.q_mono p hp
  have hac : backwardCellStart s β p ≤ backwardCellEnd s β p := by
    dsimp [backwardCellStart, backwardCellEnd]
    nlinarith [sq_nonneg β]
  have ha : 0 ≤ backwardCellStart s β p :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_le_one (by omega)))
  have hm : s.m p ∈ Icc (0 : ℝ) 1 := ⟨s.m_nonneg hp, s.m_le_one hp⟩
  let μ := Paper.parisiSchemeMeasure s
  have htime (n : ℕ) (τ : ℝ) (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
      HasDerivAt (fun r => backwardTauD β μ n (r,x)) (backwardTauForcing β μ (s.m p) n (τ,x)) τ := by
    have hq : s.q p < s.q (p+1) := by
      dsimp [backwardCellStart, backwardCellEnd] at hτ
      have hs := sq_pos_of_ne_zero hβ
      nlinarith [hτ.1,hτ.2]
    exact hasDerivAt_finiteCell_backwardTauD s β hβ hp hq n hτ x
  have hs (n : ℕ) (τ : ℝ) (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :=
    hasDerivAt_backwardTauD_spatial β hβ μ n τ x
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)
  apply relative_linear_cell_barrier_interior (backwardCellStart s β p) (backwardCellEnd s β p)
    r J L σ (uniformSpatialConstant β (j-1)) ha hac hr hJ hL hσ
    (uniformSpatialConstant_pos β (j-1)).le
    (backwardTauD β μ 2) (backwardTauForcing β μ (s.m p) 2)
    (backwardTauD β μ j) (backwardTauForcing β μ (s.m p) j)
    (fun q => s.m p * backwardTauD β μ 1 q) (fun _ => s.m p) F
    (continuous_backwardTauD β μ 2).continuousOn (continuous_backwardTauD β μ j).continuousOn
    (htime 2) (htime j)
    (fun τ hτ x => (hs 2 τ hτ x).differentiableAt)
    (fun τ hτ x => (hs j τ hτ x).differentiableAt)
    (fun τ hτ x => by
      rw [deriv_backwardTauD_spatial β hβ μ 2 τ (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)]
      exact (hs 3 τ hτ x).differentiableAt)
    (fun τ hτ x => by
      rw [deriv_backwardTauD_spatial β hβ μ j τ (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)]
      exact (hs (j+1) τ hτ x).differentiableAt)
    (fun τ hτ x => ⟨(backwardTauC_pos_le_one β hβ μ τ x (backwardCell_mem_global s β hp hτ)).1.le,
      (backwardTauC_pos_le_one β hβ μ τ x (backwardCell_mem_global s β hp hτ)).2⟩)
    (fun τ _ x => by
      have hb := backwardTauD_uniform_bound β μ (j-1) (τ,x)
      simpa only [Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hj))] using hb)
    (fun _ _ _ => hm)
    (fun τ hτ x => backwardTau_drift_outward β hβ μ (s.m p) τ x hm
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩))
    (fun τ hτ x => by
      rw [deriv2_backwardTauD_spatial β hβ μ 2 τ x
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩),
        (hs 2 τ hτ x).deriv, backwardTauForcing_two]
      dsimp [backwardCtJet]
      ring)
    (fun τ hτ x => by
      rw [deriv2_backwardTauD_spatial β hβ μ j τ x
        (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩), (hs j τ hτ x).deriv]
      exact hforcing τ hτ x)
    hF hinitial

end FRSB
