module

public import FRSB.BackwardsRelativeActual
public import FRSB.BackwardsTerminalBounds
public import FRSB.MeasureCellInduction

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardRelativeK3 (β : ℝ) : ℝ := relativeFactor 2 3 (β ^ 2)
def backwardRelativeK4 (β : ℝ) : ℝ := relativeFactor 10 (4 + 3 * backwardRelativeK3 β ^ 2) (β ^ 2)
def backwardRelativeK5 (β : ℝ) : ℝ :=
  relativeFactor 32 (5 + 10 * backwardRelativeK3 β * backwardRelativeK4 β) (β ^ 2)

theorem backwardRelativeK3_pos (β : ℝ) : 0 < backwardRelativeK3 β := by
  dsimp [backwardRelativeK3,relativeFactor]; positivity
theorem backwardRelativeK4_pos (β : ℝ) : 0 < backwardRelativeK4 β := by
  dsimp [backwardRelativeK4,relativeFactor]; positivity
theorem backwardRelativeK5_pos (β : ℝ) : 0 < backwardRelativeK5 β := by
  dsimp [backwardRelativeK5,relativeFactor]; positivity

theorem relativeFactor_mono_time {L r a b : ℝ} (hL : 0 ≤ L) (hr : 0 ≤ r) (hab : a ≤ b) :
    relativeFactor L r a ≤ relativeFactor L r b :=
  mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hr)) hL

theorem finiteCell_relative_abs_barrier {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1) (j : ℕ) (hj : 0 < j)
    (r J L : ℝ) (hr : 1 ≤ r) (hJ : 0 ≤ J) (hL : 1 ≤ L)
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
    (hinitial : ∀ x, |backwardTauD β (Paper.parisiSchemeMeasure s) j (backwardCellStart s β p,x)| ≤
      relativeFactor L (r+J) (backwardCellStart s β p) *
        backwardTauD β (Paper.parisiSchemeMeasure s) 2 (backwardCellStart s β p,x)) :
    ∀ τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p), ∀ x,
      |backwardTauD β (Paper.parisiSchemeMeasure s) j (τ,x)| ≤
        relativeFactor L (r+J) τ * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  have hplus := finiteCell_relative_barrier s β hβ hp j hj r J L 1 hr hJ hL
    (by norm_num) F hforcing hF (fun x => by
      simpa only [one_mul] using (le_abs_self _).trans (hinitial x))
  have hminus := finiteCell_relative_barrier s β hβ hp j hj r J L (-1) hr hJ hL
    (by norm_num) F hforcing hF (fun x => by
      have he := (neg_le_abs _).trans (hinitial x)
      simpa only [neg_one_mul] using he)
  intro τ hτ x
  rw [abs_le]
  have hp0 := hplus τ hτ x
  have hm0 := hminus τ hτ x
  constructor <;> linarith

theorem finiteScheme_D3_relative_factor {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ τ ∈ Icc (0 : ℝ) (β ^ 2), ∀ x,
      |backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x)| ≤
        relativeFactor 2 3 τ * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  apply backward_scheme_cell_induction s β
    (fun τ => ∀ x, |backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x)| ≤
      relativeFactor 2 3 τ * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x))
  · intro x
    simpa [backwardTauD,backwardTime,relativeFactor,backwardC] using
      (backward_terminal_relative_bounds β (Paper.parisiSchemeMeasure s) x).1
  · intro p hp hinit
    have hh := finiteCell_relative_abs_barrier s β hβ hp 3
      (by norm_num) 3 0 2 (by norm_num) (by norm_num) (by norm_num) (fun _ => 0)
      (by
        intro τ _ x
        rw [backwardTauForcing_three]
        dsimp [backwardDtJet]
        ring)
      (by intro τ hτ x; simp)
      (by simpa only [add_zero,backwardCellStart] using hinit)
    simpa only [add_zero,backwardCellStart,backwardCellEnd] using hh

theorem finiteScheme_D3_relative {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) (x : ℝ) :
    |backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x)| ≤
      backwardRelativeK3 β * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  apply (finiteScheme_D3_relative_factor s β hβ τ hτ x).trans
  exact mul_le_mul_of_nonneg_right (relativeFactor_mono_time (by norm_num) (by norm_num) hτ.2)
    (backwardTauC_pos_le_one β hβ _ τ x hτ).1.le

theorem finiteScheme_D4_relative_factor {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ τ ∈ Icc (0 : ℝ) (β ^ 2), ∀ x,
      |backwardTauD β (Paper.parisiSchemeMeasure s) 4 (τ,x)| ≤
        relativeFactor 10 (4 + 3 * backwardRelativeK3 β ^ 2) τ *
          backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  apply backward_scheme_cell_induction s β
    (fun τ => ∀ x, |backwardTauD β (Paper.parisiSchemeMeasure s) 4 (τ,x)| ≤
      relativeFactor 10 (4 + 3 * backwardRelativeK3 β ^ 2) τ *
        backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x))
  · intro x
    simpa [backwardTauD,backwardTime,relativeFactor,backwardC] using
      (backward_terminal_relative_bounds β (Paper.parisiSchemeMeasure s) x).2.1
  · intro p hp hinit
    apply finiteCell_relative_abs_barrier s β hβ hp 4 (by norm_num) 4
      (3 * backwardRelativeK3 β ^ 2) 10 (by norm_num) (by positivity) (by norm_num)
      (fun q => 3 * s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 3 q ^ 2)
    · intro τ _ x
      rw [backwardTauForcing_four]
      dsimp [backwardEtJet]
      ring
    · intro τ hτ x
      have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
      have hc := backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) τ x hg
      have hd := finiteScheme_D3_relative s β hβ hg x
      have hk := (backwardRelativeK3_pos β).le
      have hdsq : backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x) ^ 2 ≤
          (backwardRelativeK3 β * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x)) ^ 2 := by
        nlinarith [abs_le.mp hd]
      have hsqC : backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) ^ 2 ≤
          backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by nlinarith [hc.1,hc.2]
      have hdsq' : backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x) ^ 2 ≤
          backwardRelativeK3 β ^ 2 * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
        nlinarith [mul_le_mul_of_nonneg_left hsqC (sq_nonneg (backwardRelativeK3 β))]
      have hm0 := s.m_nonneg hp
      have hm1 := s.m_le_one hp
      rw [abs_of_nonneg (by positivity)]
      have hmD := mul_le_mul_of_nonneg_right hm1
        (sq_nonneg (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x)))
      nlinarith
    · exact hinit

theorem finiteScheme_D4_relative {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) (x : ℝ) :
    |backwardTauD β (Paper.parisiSchemeMeasure s) 4 (τ,x)| ≤
      backwardRelativeK4 β * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  apply (finiteScheme_D4_relative_factor s β hβ τ hτ x).trans
  exact mul_le_mul_of_nonneg_right (relativeFactor_mono_time (by norm_num) (by positivity) hτ.2)
    (backwardTauC_pos_le_one β hβ _ τ x hτ).1.le

theorem finiteScheme_D5_relative_factor {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) :
    ∀ τ ∈ Icc (0 : ℝ) (β ^ 2), ∀ x,
      |backwardTauD β (Paper.parisiSchemeMeasure s) 5 (τ,x)| ≤
        relativeFactor 32 (5 + 10 * backwardRelativeK3 β * backwardRelativeK4 β) τ *
          backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  apply backward_scheme_cell_induction s β
    (fun τ => ∀ x, |backwardTauD β (Paper.parisiSchemeMeasure s) 5 (τ,x)| ≤
      relativeFactor 32 (5 + 10 * backwardRelativeK3 β * backwardRelativeK4 β) τ *
        backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x))
  · intro x
    simpa [backwardTauD,backwardTime,relativeFactor,backwardC] using
      (backward_terminal_relative_bounds β (Paper.parisiSchemeMeasure s) x).2.2
  · intro p hp hinit
    apply finiteCell_relative_abs_barrier s β hβ hp 5 (by norm_num) 5
      (10 * backwardRelativeK3 β * backwardRelativeK4 β) 32 (by norm_num)
      (by positivity [backwardRelativeK3_pos β,backwardRelativeK4_pos β]) (by norm_num)
      (fun q => 10 * s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 3 q *
        backwardTauD β (Paper.parisiSchemeMeasure s) 4 q)
    · intro τ _ x
      rw [backwardTauForcing_five]
      dsimp [backwardFtJet]
      ring
    · intro τ hτ x
      have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
      have hc := backwardTauC_pos_le_one β hβ (Paper.parisiSchemeMeasure s) τ x hg
      have hd := finiteScheme_D3_relative s β hβ hg x
      have he := finiteScheme_D4_relative s β hβ hg x
      have hk3 := (backwardRelativeK3_pos β).le
      have hk4 := (backwardRelativeK4_pos β).le
      have hm0 := s.m_nonneg hp
      have hm1 := s.m_le_one hp
      have hde := mul_le_mul hd he (abs_nonneg _) (mul_nonneg hk3 hc.1.le)
      have hc2 : backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) ^ 2 ≤
          backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by nlinarith [hc.1,hc.2]
      have hdec : |backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x)| *
          |backwardTauD β (Paper.parisiSchemeMeasure s) 4 (τ,x)| ≤
          backwardRelativeK3 β * backwardRelativeK4 β *
            backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
        nlinarith [mul_le_mul_of_nonneg_left hc2 (mul_nonneg hk3 hk4)]
      rw [abs_mul,abs_mul,abs_mul,abs_of_nonneg hm0]
      norm_num
      have hmde := mul_le_mul_of_nonneg_right hm1
        (mul_nonneg (abs_nonneg (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x)))
          (abs_nonneg (backwardTauD β (Paper.parisiSchemeMeasure s) 4 (τ,x))))
      nlinarith
    · exact hinit

theorem finiteScheme_D5_relative {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) (x : ℝ) :
    |backwardTauD β (Paper.parisiSchemeMeasure s) 5 (τ,x)| ≤
      backwardRelativeK5 β * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x) := by
  apply (finiteScheme_D5_relative_factor s β hβ τ hτ x).trans
  exact mul_le_mul_of_nonneg_right (relativeFactor_mono_time (by norm_num)
    (by positivity [backwardRelativeK3_pos β,backwardRelativeK4_pos β]) hτ.2)
    (backwardTauC_pos_le_one β hβ _ τ x hτ).1.le

end FRSB
