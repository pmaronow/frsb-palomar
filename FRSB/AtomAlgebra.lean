module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Tactic

@[expose] public section

/-! Algebraic consequences of the terminal-atom moment inequality. -/
namespace FRSB

theorem atom_mass_positive {m ell : ℝ} (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hell : 0 < ell) (hineq : m * (4 - m + ell) ≤ 2) : 0 < 1 - m := by
  by_contra h
  have heq : m = 1 := by linarith
  subst m
  nlinarith

theorem atom_mass_gt_sqrt_two_sub_one {m ell : ℝ}
    (hm : 0 ≤ m) (hm1 : m ≤ 1) (hell : 0 < ell)
    (hineq : m * (4 - m + ell) ≤ 2) : Real.sqrt 2 - 1 < 1 - m := by
  have hstrict : m * (4 - m) < 2 := by
    rcases hm.eq_or_lt with h | h
    · rw [← h]
      norm_num
    · nlinarith [mul_pos h hell]
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hp : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : Real.sqrt 2 < 2 - m := by
    by_contra h
    have ha : 0 ≤ 2 - m := by linarith
    have hb : 2 - m ≤ Real.sqrt 2 := by linarith
    have hc := mul_self_le_mul_self ha hb
    nlinarith
  linarith

theorem atom_mass_gt_beta_overlap_bound {β q m : ℝ}
    (hβ : β ≠ 0) (hq : 0 < q) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hineq : m * (4 - m + 1 / (β ^ 2 * q)) ≤ 2) :
    1 - 2 * β ^ 2 * q < 1 - m := by
  have hd : 0 < β ^ 2 * q := mul_pos (sq_pos_of_ne_zero hβ) hq
  have hlt : m / (β ^ 2 * q) < 2 := by
    rcases hm.eq_or_lt with h | h
    · rw [← h]
      norm_num
    · have hp : 0 < m * (4 - m) := mul_pos h (by linarith)
      nlinarith [show m * (1 / (β ^ 2 * q)) = m / (β ^ 2 * q) by ring]
  have h := (div_lt_iff₀ hd).mp hlt
  nlinarith

theorem atom_mass_strict_lower_bounds {β q m : ℝ}
    (hβ : β ≠ 0) (hq : 0 < q) (hm : 0 ≤ m) (hm1 : m ≤ 1)
    (hineq : m * (4 - m + 1 / (β ^ 2 * q)) ≤ 2) :
    max (Real.sqrt 2 - 1) (1 - 2 * β ^ 2 * q) < 1 - m := by
  rw [max_lt_iff]
  exact ⟨atom_mass_gt_sqrt_two_sub_one hm hm1
    (by positivity) hineq, atom_mass_gt_beta_overlap_bound hβ hq hm hm1 hineq⟩

end FRSB
