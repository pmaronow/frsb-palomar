module

public import FRSB.ConstantMassFarField

@[expose] public section

/-! The actual inverse magnetization coordinate in Remark 5.3. Its domain
 is all of (-1,1), proved using the far-field limits of the selected PDE
 gradient. Smoothness and reciprocal-curvature derivative are obtained
 from the genuine inverse function theorem. -/
noncomputable section
open Set Filter Paper
open scoped Topology ContDiff
namespace FRSB

def magnetizationInverse (β : ℝ) (μ : ParisiMeasure) (t b : ℝ) : ℝ :=
  Function.invFun (fun x => parisiGradient β μ (t, x)) b

theorem parisiGradient_magnetizationInverse (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t b : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    parisiGradient β μ (t, magnetizationInverse β μ t b) = b := by
  unfold magnetizationInverse
  have hex : ∃ x, parisiGradient β μ (t, x) = b := by
    change b ∈ Set.range (fun x => parisiGradient β μ (t, x))
    rw [parisiGradient_range β hβ μ t ht]
    exact hb
  exact Function.invFun_eq hex

theorem magnetizationInverse_parisiGradient (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    magnetizationInverse β μ t (parisiGradient β μ (t, x)) = x :=
  Function.leftInverse_invFun (parisiGradient_strictMono β hβ μ t ht).injective x

/-- A global injective function's chosen inverse agrees locally with the
 smooth inverse supplied by the inverse function theorem. -/
theorem contDiffAt_invFun_of_injective (f : ℝ → ℝ) (x f' : ℝ)
    (hi : Function.Injective f) (hc : ContDiffAt ℝ ∞ f x)
    (hd : HasDerivAt f f' x) (hfn : f' ≠ 0) :
    ContDiffAt ℝ ∞ (Function.invFun f) (f x) := by
  have hh := (hc.hasStrictDerivAt' hd (by simp)).hasStrictFDerivAt_equiv hfn
  let e := hh.toOpenPartialHomeomorph f
  have heinv : e.symm (f x) = x := e.left_inv hh.mem_toOpenPartialHomeomorph_source
  have hloc : ContDiffAt ℝ ∞ e.symm (f x) := by
    apply e.contDiffAt_symm hh.image_mem_toOpenPartialHomeomorph_target
    · rw [heinv]
      simpa only [e, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hh.hasFDerivAt
    · rw [heinv]
      simpa only [e, HasStrictFDerivAt.toOpenPartialHomeomorph_coe] using hc
  have heq := hh.localInverse_unique (Filter.Eventually.of_forall (Function.leftInverse_invFun hi))
  exact hloc.congr_of_eventuallyEq heq

theorem contDiffAt_magnetizationInverse (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t b : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) : ContDiffAt ℝ ∞ (magnetizationInverse β μ t) b := by
  let x := magnetizationInverse β μ t b
  have hx := parisiGradient_magnetizationInverse β hβ μ t b ht hb
  change parisiGradient β μ (t, x) = b at hx
  have hc := (contDiff_parisiGradient_spatial β μ t).contDiffAt (x := x)
  have hd := hasDerivAt_parisiGradient_spatial_all β μ t x
  have hp := (parisiHessian_pos β hβ μ t x ht).ne'
  have hh := contDiffAt_invFun_of_injective (fun y => parisiGradient β μ (t, y)) x _
    (parisiGradient_strictMono β hβ μ t ht).injective hc hd hp
  rw [hx] at hh
  exact hh

theorem hasDerivAt_magnetizationInverse (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t b : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
    (hb : b ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (magnetizationInverse β μ t)
      (parisiHessian β μ (t, magnetizationInverse β μ t b))⁻¹ b := by
  apply HasDerivAt.of_local_left_inverse
    (contDiffAt_magnetizationInverse β hβ μ t b ht hb).continuousAt
    (hasDerivAt_parisiGradient_spatial_all β μ t _) (parisiHessian_pos β hβ μ t _ ht).ne'
  filter_upwards [isOpen_Ioo.mem_nhds hb] with y hy
  exact parisiGradient_magnetizationInverse β hβ μ t y ht hy

theorem contDiffOn_magnetizationInverse (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ContDiffOn ℝ ∞ (magnetizationInverse β μ t) (Ioo (-1 : ℝ) 1) := by
  intro b hb
  exact (contDiffAt_magnetizationInverse β hβ μ t b ht hb).contDiffWithinAt

end FRSB
