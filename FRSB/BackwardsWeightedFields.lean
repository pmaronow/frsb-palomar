module

public import FRSB.BackwardsTimeSpatial
public import FRSB.BackwardsJetCalculus

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardTauZ (β : ℝ) (μ : Paper.ParisiMeasure) (p : ℝ × ℝ) : ℝ :=
  backwardZJet (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
def backwardTauQ (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardQJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p) (backwardTauD β μ 4 p)
def backwardTauP (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardTauD β μ 2 p * backwardTauQ β μ a p
def backwardTauR (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardRJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauD β μ 4 p) (backwardTauD β μ 5 p)
def backwardTauPx (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardPxJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauD β μ 4 p) (backwardTauD β μ 5 p)
def backwardTauPxx (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardPxxJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauD β μ 4 p) (backwardTauD β μ 5 p) (backwardTauD β μ 6 p)
def backwardTauRx (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardRxJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauD β μ 4 p) (backwardTauD β μ 5 p) (backwardTauD β μ 6 p)
def backwardTauRxx (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardRxxJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauD β μ 4 p) (backwardTauD β μ 5 p) (backwardTauD β μ 6 p) (backwardTauD β μ 7 p)
def backwardTauZt (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardZtJet (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauForcing β μ a 2 p) (backwardTauForcing β μ a 3 p)
def backwardTauPt (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardPtJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p) (backwardTauD β μ 4 p)
    (backwardTauForcing β μ a 2 p) (backwardTauForcing β μ a 3 p) (backwardTauForcing β μ a 4 p)
def backwardTauRt (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (p : ℝ × ℝ) : ℝ :=
  backwardRtJet a (backwardTauD β μ 2 p) (backwardTauD β μ 3 p)
    (backwardTauD β μ 4 p) (backwardTauD β μ 5 p)
    (backwardTauForcing β μ a 2 p) (backwardTauForcing β μ a 3 p)
    (backwardTauForcing β μ a 4 p) (backwardTauForcing β μ a 5 p)

theorem backwardTauR_eq_weightedHx (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    backwardTauR β μ a (τ, x) = backwardTauD β μ 2 (τ, x) *
      backwardHx β μ a (backwardTime β τ, x) :=
  backwardRJet_eq_weightedHx _ _ _ _ _ (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'

theorem backwardPtJet_spatial (a C D E F : ℝ) (hC : C ≠ 0) :
    backwardPtJet a C D E D E F = backwardPxJet a C D E F := by
  dsimp [backwardPtJet, backwardPxJet]
  field_simp

theorem backwardRtJet_spatial (a C D E F G : ℝ) (hC : C ≠ 0) :
    backwardRtJet a C D E F D E F G = backwardRxJet a C D E F G := by
  dsimp [backwardRtJet, backwardRxJet]
  field_simp
  ring

theorem hasDerivAt_backwardTauP_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (fun y => backwardTauP β μ a (τ, y)) (backwardTauPx β μ a (τ, x)) x := by
  have h := hasDerivWithinAt_backwardWeightedQJet
    (s := univ) (a := a)
    (hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ).hasDerivWithinAt
    (hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ).hasDerivWithinAt
    (hasDerivAt_backwardTauD_spatial β hβ μ 4 τ x hτ).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'
  rw [backwardPtJet_spatial _ _ _ _ _ (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'] at h
  exact hasDerivWithinAt_univ.mp h

theorem hasDerivAt_backwardTauPx_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (fun y => backwardTauPx β μ a (τ, y)) (backwardTauPxx β μ a (τ, x)) x :=
  hasDerivAt_backwardPxJet
    (hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 4 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 5 τ x hτ)
    (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'

theorem hasDerivAt_backwardTauR_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (fun y => backwardTauR β μ a (τ, y)) (backwardTauRx β μ a (τ, x)) x := by
  have h := hasDerivWithinAt_backwardRJet
    (s := univ) (a := a)
    (hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ).hasDerivWithinAt
    (hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ).hasDerivWithinAt
    (hasDerivAt_backwardTauD_spatial β hβ μ 4 τ x hτ).hasDerivWithinAt
    (hasDerivAt_backwardTauD_spatial β hβ μ 5 τ x hτ).hasDerivWithinAt
    (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'
  rw [backwardRtJet_spatial _ _ _ _ _ _ (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'] at h
  exact hasDerivWithinAt_univ.mp h

theorem hasDerivAt_backwardTauRx_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (fun y => backwardTauRx β μ a (τ, y)) (backwardTauRxx β μ a (τ, x)) x :=
  hasDerivAt_backwardRxJet
    (hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 4 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 5 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 6 τ x hτ)
    (backwardTauC_pos_le_one β hβ μ τ x hτ).1.ne'

theorem deriv_backwardTauP_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    deriv (fun y => backwardTauP β μ a (τ, y)) = fun y => backwardTauPx β μ a (τ, y) :=
  funext fun y => (hasDerivAt_backwardTauP_spatial β hβ μ a τ y hτ).deriv
theorem deriv_backwardTauR_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    deriv (fun y => backwardTauR β μ a (τ, y)) = fun y => backwardTauRx β μ a (τ, y) :=
  funext fun y => (hasDerivAt_backwardTauR_spatial β hβ μ a τ y hτ).deriv

end FRSB
