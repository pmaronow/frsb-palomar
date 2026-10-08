module

public import FRSB.BackwardsDefinitions
public import Paper.ParisiMixContinuity

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

lemma terminal_time_mem : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num

theorem backwardB_terminal (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardB β μ (1, x) = Real.tanh x := by
  rw [backwardB_eq_gradient β μ 1 x terminal_time_mem]
  exact Paper.parisiGradient_terminal β μ x

theorem backwardC_terminal (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardC β μ (1, x) = Paper.sech x ^ 2 := by
  have he : (fun y => backwardD β μ 1 (1, y)) = Real.tanh :=
    funext (backwardB_terminal β μ)
  have hh := (hasDerivAt_backwardD β μ 1 1 x terminal_time_mem).deriv
  rw [he, (Paper.hasDerivAt_tanh x).deriv] at hh
  exact hh.symm

theorem backwardD_three_terminal (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardD β μ 3 (1, x) = -2 * Real.tanh x * Paper.sech x ^ 2 := by
  have he : (fun y => backwardD β μ 2 (1, y)) = fun y => Paper.sech y ^ 2 :=
    funext (backwardC_terminal β μ)
  have hh := (hasDerivAt_backwardD β μ 2 1 x terminal_time_mem).deriv
  rw [he, (Paper.hasDerivAt_sech_sq x).deriv] at hh
  exact hh.symm

theorem backwardZ_terminal (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardZ β μ (1, x) = Real.tanh x := by
  dsimp [backwardZ, backwardZJet]
  rw [backwardC_terminal, backwardD_three_terminal]
  field_simp [(Paper.sech_pos x).ne']

theorem backwardQ_terminal (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardQ β μ 1 (1, x) = 0 := by
  rw [backwardQ_eq_derivZ_sub_mC β hβ μ 1 1 x terminal_time_mem]
  have he : (fun y => backwardZ β μ (1, y)) = Real.tanh := funext (backwardZ_terminal β μ)
  rw [he, (Paper.hasDerivAt_tanh x).deriv, backwardC_terminal]
  ring

theorem backwardH_terminal (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardH β μ 1 (1, x) = 1 := by
  rw [backwardH_eq_z_sq_mC_sub_twoQ, backwardZ_terminal, backwardC_terminal,
    backwardQ_terminal β hβ μ x]
  simpa using Paper.tanh_sq_add_sech_sq x

theorem backwardHx_terminal (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardHx β μ 1 (1, x) = 0 := by
  rw [backwardHx_eq_derivH β hβ μ 1 1 x terminal_time_mem]
  have he : (fun y => backwardH β μ 1 (1, y)) = fun _ => 1 := funext (backwardH_terminal β hβ μ)
  rw [he, deriv_const]

end FRSB
