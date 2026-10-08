module

public import FRSB.BackwardsTerminal

@[expose] public section

noncomputable section
open Set
namespace FRSB

theorem backwardD_four_terminal (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardD β μ 4 (1,x) = 4 * Paper.sech x ^ 2 - 6 * Paper.sech x ^ 4 := by
  have he : (fun y => backwardD β μ 3 (1,y)) =
      fun y => -2 * Real.tanh y * Paper.sech y ^ 2 :=
    funext (backwardD_three_terminal β μ)
  have hh := (hasDerivAt_backwardD β μ 3 1 x terminal_time_mem).deriv
  have hd := ((Paper.hasDerivAt_tanh x).const_mul (-2)).mul (Paper.hasDerivAt_sech_sq x)
  have hd' : HasDerivAt (fun y => -2 * Real.tanh y * Paper.sech y ^ 2)
      ((-2 * Paper.sech x ^ 2) * Paper.sech x ^ 2 +
        (-2 * Real.tanh x) * (-2 * Real.tanh x * Paper.sech x ^ 2)) x := by
    convert hd using 1
  rw [he, hd'.deriv] at hh
  have hi := Paper.tanh_sq_add_sech_sq x
  dsimp at hh
  nlinarith [hh]

theorem backwardD_five_terminal (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardD β μ 5 (1,x) =
      -8 * Real.tanh x * Paper.sech x ^ 2 + 24 * Real.tanh x * Paper.sech x ^ 4 := by
  have he : (fun y => backwardD β μ 4 (1,y)) =
      fun y => 4 * Paper.sech y ^ 2 - 6 * (Paper.sech y ^ 2) ^ 2 := by
    funext y
    rw [backwardD_four_terminal]
    ring
  have hh := (hasDerivAt_backwardD β μ 4 1 x terminal_time_mem).deriv
  have hd := ((Paper.hasDerivAt_sech_sq x).const_mul 4).sub
    (((Paper.hasDerivAt_sech_sq x).pow 2).const_mul 6)
  have hd' : HasDerivAt (fun y => 4 * Paper.sech y ^ 2 - 6 * (Paper.sech y ^ 2) ^ 2)
      (4 * (-2 * Real.tanh x * Paper.sech x ^ 2) -
        6 * (2 * Paper.sech x ^ 2 * (-2 * Real.tanh x * Paper.sech x ^ 2))) x := by
    convert hd using 1
    norm_num
  rw [he, hd'.deriv] at hh
  dsimp at hh
  nlinarith [hh]

theorem backward_terminal_relative_bounds (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    |backwardD β μ 3 (1,x)| ≤ 2 * backwardC β μ (1,x) ∧
    |backwardD β μ 4 (1,x)| ≤ 10 * backwardC β μ (1,x) ∧
    |backwardD β μ 5 (1,x)| ≤ 32 * backwardC β μ (1,x) := by
  have hC : 0 ≤ Paper.sech x ^ 2 := sq_nonneg _
  have hC1 := Paper.sech_sq_le_one x
  have hB : |Real.tanh x| ≤ 1 := le_of_lt (Real.abs_tanh_lt_one x)
  rw [backwardD_three_terminal, backwardD_four_terminal, backwardD_five_terminal, backwardC_terminal]
  constructor
  · rw [abs_mul, abs_mul, abs_of_nonneg hC]
    norm_num
    nlinarith
  constructor
  · have hi : Paper.sech x ^ 4 ≤ Paper.sech x ^ 2 := by nlinarith
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg (Paper.sech x ^ 2)]
  · have he : -8 * Real.tanh x * Paper.sech x ^ 2 + 24 * Real.tanh x * Paper.sech x ^ 4 =
        Real.tanh x * Paper.sech x ^ 2 * (-8 + 24 * Paper.sech x ^ 2) := by ring
    rw [he, abs_mul, abs_mul, abs_of_nonneg hC]
    have hf : |(-8 : ℝ) + 24 * Paper.sech x ^ 2| ≤ 32 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |Real.tanh x| * Paper.sech x ^ 2 * |(-8 : ℝ) + 24 * Paper.sech x ^ 2| ≤
          1 * Paper.sech x ^ 2 * 32 :=
        mul_le_mul (mul_le_mul_of_nonneg_right hB hC) hf (abs_nonneg _) (by positivity)
      _ = 32 * Paper.sech x ^ 2 := by ring

end FRSB
