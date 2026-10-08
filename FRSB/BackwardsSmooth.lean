module

public import FRSB.BackwardsBounded
public import FRSB.BackwardsRelativeFields

@[expose] public section

noncomputable section
open Set
open scoped ContDiff
namespace FRSB

theorem _root_.ContDiff.const_mul_bwd {n : ℕ∞ω} {f : ℝ → ℝ}
    (hf : ContDiff ℝ n f) (a : ℝ) : ContDiff ℝ n (fun x => a*f x) :=
  contDiff_const.mul hf

theorem contDiff_backwardD_spatial (β : ℝ) (μ : Paper.ParisiMeasure) (t : ℝ)
    (ht : t ∈ Icc (0 : ℝ) 1) (j : ℕ) : ContDiff ℝ ∞ (fun x => backwardD β μ j (t,x)) := by
  induction j with
  | zero => exact Paper.contDiff_parisiPotential_spatial β μ t ht
  | succ j ih =>
    have he : (fun x => backwardD β μ (j+1) (t,x)) = deriv (fun x => backwardD β μ j (t,x)) :=
      funext fun x => (hasDerivAt_backwardD β μ j t x ht).deriv.symm
    rw [he]
    apply ContDiff.deriv'
    simpa using ih

/-- The paper's logarithmic-curvature fields are genuinely smooth functions
of space, built from the actual positive susceptibility. -/
theorem backward_fields_smooth (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiff ℝ ∞ (fun x => backwardZ β μ (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardZx β μ (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardZxx β μ (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardQ β μ a (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardH β μ a (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardHx β μ a (t,x)) := by
  have hC := contDiff_backwardD_spatial β μ t ht 2
  have hD := contDiff_backwardD_spatial β μ t ht 3
  have hE := contDiff_backwardD_spatial β μ t ht 4
  have hF := contDiff_backwardD_spatial β μ t ht 5
  have hne (x : ℝ) := (backwardC_pos β hβ μ t x ht).ne'
  have hz : ContDiff ℝ ∞ (fun x => backwardZ β μ (t,x)) :=
    hD.neg.div (hC.const_mul_bwd 2) (fun x => mul_ne_zero (by norm_num) (hne x))
  have hzx : ContDiff ℝ ∞ (fun x => backwardZx β μ (t,x)) :=
    (hE.neg.div (hC.const_mul_bwd 2) (fun x => mul_ne_zero (by norm_num) (hne x))).add
      ((hD.pow 2).div ((hC.pow 2).const_mul_bwd 2)
        (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hne x))))
  have hzxx : ContDiff ℝ ∞ (fun x => backwardZxx β μ (t,x)) :=
    ((hF.neg.div (hC.const_mul_bwd 2) (fun x => mul_ne_zero (by norm_num) (hne x))).add
      ((((hD.const_mul_bwd 3).mul hE).div ((hC.pow 2).const_mul_bwd 2)
        (fun x => mul_ne_zero (by norm_num) (pow_ne_zero 2 (hne x)))))).sub
      ((hD.pow 3).div (hC.pow 3) (fun x => pow_ne_zero 3 (hne x)))
  have hq : ContDiff ℝ ∞ (fun x => backwardQ β μ a (t,x)) := hzx.sub (hC.const_mul_bwd a)
  have hh : ContDiff ℝ ∞ (fun x => backwardH β μ a (t,x)) :=
    ((hz.pow 2).add (hC.const_mul_bwd a)).sub (hq.const_mul_bwd 2)
  have hhx : ContDiff ℝ ∞ (fun x => backwardHx β μ a (t,x)) :=
    (((hz.const_mul_bwd 2).mul hzx).add (hD.const_mul_bwd a)).sub
      ((hzxx.sub (hD.const_mul_bwd a)).const_mul_bwd 2)
  exact ⟨hz,hzx,hzxx,hq,hh,hhx⟩

end FRSB
