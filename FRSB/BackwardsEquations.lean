module

public import FRSB.BackwardsWeightedFields

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem backwardCell_mem_global {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) {p : ℕ} (hp : p ≤ k + 1) {τ : ℝ}
    (hτ : τ ∈ Icc (backwardCellStart s β p) (backwardCellEnd s β p)) :
    τ ∈ Icc (0 : ℝ) (β ^ 2) := by
  have hlo : 0 ≤ backwardCellStart s β p :=
    mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (s.q_le_one (by omega)))
  have hhi : backwardCellEnd s β p ≤ β ^ 2 := by
    have hq := s.q_nonneg (p := p) (by omega)
    dsimp [backwardCellEnd]
    nlinarith [sq_nonneg β]
  exact ⟨hlo.trans hτ.1, hτ.2.trans hhi⟩

theorem hasDerivAt_finiteCell_backwardTauZ {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    HasDerivAt (fun r => backwardTauZ β (Paper.parisiSchemeMeasure s) (r, x))
      (backwardTauZt β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x)) τ := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le, hτ.2.le⟩
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_backwardZJet
    (s := univ)
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 2 hτ x).hasDerivWithinAt
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 3 hτ x).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne')

theorem hasDerivAt_finiteCell_backwardTauP {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    HasDerivAt (fun r => backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (r, x))
      (backwardTauPt β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x)) τ := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le, hτ.2.le⟩
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_backwardWeightedQJet
    (s := univ) (a := s.m p)
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 2 hτ x).hasDerivWithinAt
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 3 hτ x).hasDerivWithinAt
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 4 hτ x).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne')

theorem hasDerivAt_finiteCell_backwardTauR {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    HasDerivAt (fun r => backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (r, x))
      (backwardTauRt β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x)) τ := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le, hτ.2.le⟩
  exact hasDerivWithinAt_univ.mp (hasDerivWithinAt_backwardRJet
    (s := univ) (a := s.m p)
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 2 hτ x).hasDerivWithinAt
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 3 hτ x).hasDerivWithinAt
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 4 hτ x).hasDerivWithinAt
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 5 hτ x).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne')

/-- Lemma 3.3: the actual weighted Q equation on every genuine finite-measure cell. -/
theorem finiteCell_backward_weightedQ_equation {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    deriv (fun r => backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (r, x)) τ -
      deriv (deriv (fun y => backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (τ, y))) x / 2 -
      s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 1 (τ, x) *
        deriv (fun y => backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (τ, y)) x =
      -2 * backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x) *
        backwardTauP β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x) := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le, hτ.2.le⟩
  rw [(hasDerivAt_finiteCell_backwardTauP s β hβ hp hq hτ x).deriv,
    deriv_backwardTauP_spatial β hβ _ (s.m p) τ hg,
    (hasDerivAt_backwardTauPx_spatial β hβ _ (s.m p) τ x hg).deriv]
  dsimp [backwardTauPt, backwardTauPxx, backwardTauPx, backwardTauP, backwardTauQ]
  rw [backwardTauForcing_two, backwardTauForcing_three, backwardTauForcing_four]
  exact backward_weightedQ_evolution_jet _ _ _ _ _ _ _
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'

/-- Lemma 3.3: the actual CHx equation, including its nonnegative source. -/
theorem finiteCell_backward_weightedHx_equation {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    deriv (fun r => backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (r, x)) τ -
      deriv (deriv (fun y => backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (τ, y))) x / 2 -
      s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 1 (τ, x) *
        deriv (fun y => backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (τ, y)) x =
      -5 * backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x) *
        backwardTauR β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x) +
      6 * backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ, x) *
        backwardTauZ β (Paper.parisiSchemeMeasure s) (τ, x) *
        backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x) ^ 2 := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le, hτ.2.le⟩
  rw [(hasDerivAt_finiteCell_backwardTauR s β hβ hp hq hτ x).deriv,
    deriv_backwardTauR_spatial β hβ _ (s.m p) τ hg,
    (hasDerivAt_backwardTauRx_spatial β hβ _ (s.m p) τ x hg).deriv]
  dsimp [backwardTauRt, backwardTauRxx, backwardTauRx, backwardTauR, backwardTauQ, backwardTauZ]
  rw [backwardTauForcing_two, backwardTauForcing_three, backwardTauForcing_four, backwardTauForcing_five]
  have hh := backward_weightedHx_evolution_jet (s.m p)
    (backwardTauD β (Paper.parisiSchemeMeasure s) 1 (τ,x))
    (backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x))
    (backwardTauD β (Paper.parisiSchemeMeasure s) 3 (τ,x))
    (backwardTauD β (Paper.parisiSchemeMeasure s) 4 (τ,x))
    (backwardTauD β (Paper.parisiSchemeMeasure s) 5 (τ,x))
    (backwardTauD β (Paper.parisiSchemeMeasure s) 6 (τ,x))
    (backwardTauD β (Paper.parisiSchemeMeasure s) 7 (τ,x))
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'
  rw [← backwardRJet_eq_weightedHx _ _ _ _ _
    (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'] at hh
  exact hh

theorem finiteCell_backward_z_equation {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    deriv (fun r => backwardTauZ β (Paper.parisiSchemeMeasure s) (r, x)) τ -
      deriv (deriv (fun y => backwardTauZ β (Paper.parisiSchemeMeasure s) (τ, y))) x / 2 -
      s.m p * backwardTauD β (Paper.parisiSchemeMeasure s) 1 (τ, x) *
        deriv (fun y => backwardTauZ β (Paper.parisiSchemeMeasure s) (τ, y)) x =
      -2 * backwardTauQ β (Paper.parisiSchemeMeasure s) (s.m p) (τ, x) *
        backwardTauZ β (Paper.parisiSchemeMeasure s) (τ, x) := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le, hτ.2.le⟩
  have ht := backwardTime_mem β hβ τ hg
  have he : deriv (fun y => backwardTauZ β (Paper.parisiSchemeMeasure s) (τ,y)) =
      fun y => backwardZx β (Paper.parisiSchemeMeasure s) (backwardTime β τ,y) :=
    funext fun y => (hasDerivAt_backwardZ β hβ _ _ y ht).deriv
  rw [(hasDerivAt_finiteCell_backwardTauZ s β hβ hp hq hτ x).deriv, he,
    (hasDerivAt_backwardZx β hβ _ _ x ht).deriv]
  dsimp [backwardTauZt, backwardTauQ, backwardTauZ, backwardZx, backwardZxx]
  rw [backwardTauForcing_two, backwardTauForcing_three]
  exact backward_z_evolution_jet _ _ _ _ _ _ (backwardTauC_pos_le_one β hβ _ τ x hg).1.ne'

/-- The differentiated PDE is a genuine classical equation on each open cell. -/
theorem finiteCell_backwardD_equation {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k + 1)
    (hq : s.q p < s.q (p + 1)) (j : ℕ) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    deriv (fun r => backwardTauD β (Paper.parisiSchemeMeasure s) j (r, x)) τ -
      deriv (deriv (fun y => backwardTauD β (Paper.parisiSchemeMeasure s) j (τ, y))) x / 2 =
      backwardTauForcing β (Paper.parisiSchemeMeasure s) (s.m p) j (τ, x) -
        backwardTauD β (Paper.parisiSchemeMeasure s) (j + 2) (τ, x) / 2 := by
  rw [(hasDerivAt_finiteCell_backwardTauD s β hβ hp hq j hτ x).deriv,
    deriv2_backwardTauD_spatial β hβ _ j τ x
      (backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩)]

end FRSB
