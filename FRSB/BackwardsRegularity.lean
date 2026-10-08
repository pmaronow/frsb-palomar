module

public import FRSB.BackwardsBoundedFields
public import FRSB.BackwardsParity

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def backwardTauStrip (β : ℝ) : Set (ℝ × ℝ) := Icc (0 : ℝ) (β ^ 2) ×ˢ univ

theorem continuousOn_backwardTauZ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) :
    ContinuousOn (backwardTauZ β μ) (backwardTauStrip β) := by
  have hC := (continuous_backwardTauD β μ 2).continuousOn (s := backwardTauStrip β)
  have hD := (continuous_backwardTauD β μ 3).continuousOn (s := backwardTauStrip β)
  exact hD.neg.div (hC.const_mul 2) (fun p hp =>
    mul_ne_zero (by norm_num) (backwardTauC_pos_le_one β hβ μ p.1 p.2 hp.1).1.ne')

theorem continuousOn_backwardTauQ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (a : ℝ) :
    ContinuousOn (backwardTauQ β μ a) (backwardTauStrip β) := by
  have hC := (continuous_backwardTauD β μ 2).continuousOn (s := backwardTauStrip β)
  have hD := (continuous_backwardTauD β μ 3).continuousOn (s := backwardTauStrip β)
  have hE := (continuous_backwardTauD β μ 4).continuousOn (s := backwardTauStrip β)
  have hn (p : ℝ × ℝ) (hp : p ∈ backwardTauStrip β) :=
    (backwardTauC_pos_le_one β hβ μ p.1 p.2 hp.1).1.ne'
  exact ((hE.neg.div (hC.const_mul 2) (fun p hp => mul_ne_zero (by norm_num) (hn p hp))).add
    ((hD.pow 2).div ((hC.pow 2).const_mul 2)
      (fun p hp => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hn p hp))))).sub (hC.const_mul a)

theorem continuousOn_backwardTauP (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (a : ℝ) :
    ContinuousOn (backwardTauP β μ a) (backwardTauStrip β) :=
  (continuous_backwardTauD β μ 2).continuousOn.mul (continuousOn_backwardTauQ β hβ μ a)

theorem continuousOn_backwardTauR (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (a : ℝ) :
    ContinuousOn (backwardTauR β μ a) (backwardTauStrip β) := by
  have hC := (continuous_backwardTauD β μ 2).continuousOn (s := backwardTauStrip β)
  have hD := (continuous_backwardTauD β μ 3).continuousOn (s := backwardTauStrip β)
  have hE := (continuous_backwardTauD β μ 4).continuousOn (s := backwardTauStrip β)
  have hF := (continuous_backwardTauD β μ 5).continuousOn (s := backwardTauStrip β)
  have hn (p : ℝ × ℝ) (hp : p ∈ backwardTauStrip β) :=
    (backwardTauC_pos_le_one β hβ μ p.1 p.2 hp.1).1.ne'
  have hh := (((hF.sub (((hD.mul hE).const_mul 5).div (hC.const_mul 2)
    (fun p hp => mul_ne_zero (by norm_num) (hn p hp)))).add
    (((hD.pow 3).const_mul 3).div ((hC.pow 2).const_mul 2)
      (fun p hp => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hn p hp))))).add
      ((hC.mul hD).const_mul (3*a)))
  convert hh using 1
  funext p
  dsimp [backwardTauR,backwardRJet]
  ring

theorem hasDerivAt_backwardTauZ_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (fun y => backwardTauZ β μ (τ,y))
      (backwardZx β μ (backwardTime β τ,x)) x :=
  hasDerivAt_backwardZ β hβ μ (backwardTime β τ) x (backwardTime_mem β hβ τ hτ)

theorem deriv_backwardTauZ_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    deriv (fun y => backwardTauZ β μ (τ,y)) = fun y => backwardZx β μ (backwardTime β τ,y) :=
  funext fun y => (hasDerivAt_backwardTauZ_spatial β hβ μ τ y hτ).deriv

theorem hasDerivAt_deriv_backwardTauZ_spatial (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (τ x : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) :
    HasDerivAt (deriv (fun y => backwardTauZ β μ (τ,y)))
      (backwardZxx β μ (backwardTime β τ,x)) x := by
  rw [deriv_backwardTauZ_spatial β hβ μ τ hτ]
  exact hasDerivAt_backwardZx β hβ μ (backwardTime β τ) x (backwardTime_mem β hβ τ hτ)

theorem backwardTauZ_at_zero (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) : backwardTauZ β μ (τ,0) = 0 :=
  backwardZ_at_zero β μ (backwardTime β τ) (backwardTime_mem β hβ τ hτ)

theorem backwardTauR_at_zero (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a τ : ℝ) (hτ : τ ∈ Icc (0 : ℝ) (β ^ 2)) : backwardTauR β μ a (τ,0) = 0 := by
  rw [backwardTauR_eq_weightedHx β hβ μ a τ 0 hτ,
    backwardHx_at_zero β μ a (backwardTime β τ) (backwardTime_mem β hβ τ hτ),mul_zero]

end FRSB
