module

public import FRSB.BackwardsRelativeGlobal

@[expose] public section

noncomputable section
open Set
namespace FRSB

/-- All six rational derivative fields have a beta-dependent bound, uniform
over the actual probability measure and every constant-mass coefficient. -/
theorem relative_fields_bounded (β : ℝ) (hβ : β ≠ 0) :
    ∃ L > 0, ∀ (μ : Paper.ParisiMeasure) (a t x : ℝ), a ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      |backwardZ β μ (t,x)| ≤ L ∧ |backwardZx β μ (t,x)| ≤ L ∧
      |backwardZxx β μ (t,x)| ≤ L ∧ |backwardQ β μ a (t,x)| ≤ L ∧
      |backwardH β μ a (t,x)| ≤ L ∧ |backwardHx β μ a (t,x)| ≤ L := by
  let K := backwardRelativeConstant β
  have hK := backwardRelativeConstant_pos β
  obtain ⟨M,hM,hb⟩ := exists_backwardJet_bound K K K
  refine ⟨M^2+3*M+3*K+3,by positivity,?_⟩
  intro μ a t x ha ht
  have hC0 := backwardC_pos β hβ μ t x ht
  have hC1 := backwardC_le_one β hβ μ t x ht
  have hD := backward_relative_derivative_bound β hβ μ t x ht 3 (by decide)
  have hE := backward_relative_derivative_bound β hβ μ t x ht 4 (by decide)
  have hF := backward_relative_derivative_bound β hβ μ t x ht 5 (by decide)
  have hv : |backwardZ β μ (t,x)| ≤ M ∧ |backwardQ β μ a (t,x)| ≤ M ∧
      |backwardHx β μ a (t,x)| ≤ M := hb a _ _ _ _ ha hC0 hC1 hD hE hF
  have hac0 : 0 ≤ a*backwardC β μ (t,x) := mul_nonneg ha.1 hC0.le
  have hac1 : a*backwardC β μ (t,x) ≤ 1 := mul_le_one₀ ha.2 hC0.le hC1
  have hzx : backwardZx β μ (t,x) = backwardQ β μ a (t,x)+a*backwardC β μ (t,x) := by
    dsimp [backwardQ,backwardQJet,backwardZx]
    ring
  have hzxb : |backwardZx β μ (t,x)| ≤ M+1 := by
    rw [hzx,abs_le]
    have hq := abs_le.mp hv.2.1
    constructor <;> linarith
  have hD0 : |backwardD β μ 3 (t,x)| ≤ K :=
    hD.trans (by nlinarith [mul_le_mul_of_nonneg_left hC1 hK.le])
  have haD : |a*backwardD β μ 3 (t,x)| ≤ K := by
    rw [abs_mul,abs_of_nonneg ha.1]
    have hh := mul_le_mul_of_nonneg_right ha.2 (abs_nonneg (backwardD β μ 3 (t,x)))
    nlinarith
  have hprod : |backwardZ β μ (t,x)*backwardZx β μ (t,x)| ≤ M*(M+1) := by
    rw [abs_mul]
    exact mul_le_mul hv.1 hzxb (abs_nonneg _) hM.le
  have hhx : backwardHx β μ a (t,x) =
      2*backwardZ β μ (t,x)*backwardZx β μ (t,x)+3*(a*backwardD β μ 3 (t,x))-
        2*backwardZxx β μ (t,x) := by
    dsimp [backwardHx,backwardHxJet,backwardQxJet,backwardZ,backwardZx,backwardZxx]
    ring
  have hzxxb : |backwardZxx β μ (t,x)| ≤ M*(M+1)+3*K/2+M/2 := by
    rw [abs_le]
    have hp := abs_le.mp hprod
    have hd := abs_le.mp haD
    have hh := abs_le.mp hv.2.2
    constructor <;> nlinarith [hhx]
  have hzsq : backwardZ β μ (t,x)^2 ≤ M^2 := by nlinarith [abs_le.mp hv.1]
  have hHb : |backwardH β μ a (t,x)| ≤ M^2+1+2*M := by
    rw [backwardH_eq_z_sq_mC_sub_twoQ,abs_le]
    have hq := abs_le.mp hv.2.1
    constructor <;> nlinarith [sq_nonneg (backwardZ β μ (t,x))]
  refine ⟨hv.1.trans ?_,hzxb.trans ?_,hzxxb.trans ?_,hv.2.1.trans ?_,hHb.trans ?_,hv.2.2.trans ?_⟩ <;>
    dsimp [K] at * <;> nlinarith [sq_nonneg M]

end FRSB
