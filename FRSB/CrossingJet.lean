module

public import FRSB.CrossingAlgebra

@[expose] public section

/-! The constant-mass Parisi spatial jet determines the transport identities.
No ratio or evolution identity is assumed: the scalar formulas are expanded
from the strictly nonzero curvature and the differentiated Parisi equation. -/

noncomputable section
namespace FRSB

def crossingZ (C D : ℝ) : ℝ := -D / (2 * C)
def crossingQ (m C D A : ℝ) : ℝ := -A / (2 * C) + D ^ 2 / (2 * C ^ 2) - m * C
def crossingQx (m C D A E : ℝ) : ℝ :=
  -E / (2 * C) + 3 * A * D / (2 * C ^ 2) - D ^ 3 / C ^ 3 - m * D

def crossingBt (m B C D : ℝ) : ℝ := -D / 2 - m * B * C
def crossingCt (m B C D A : ℝ) : ℝ := -A / 2 - m * (C ^ 2 + B * D)
def crossingDt (m B C D A E : ℝ) : ℝ := -E / 2 - m * (3 * C * D + B * A)

def crossingZt (m B C D A E : ℝ) : ℝ :=
  -(crossingDt m B C D A E) / (2 * C) +
    D * (crossingCt m B C D A) / (2 * C ^ 2)

theorem crossing_transport_B_from_jet (m B C D : ℝ) (hC : C ≠ 0) :
    crossingBt m B C D + crossingVelocity m B (crossingZ C D) * C = 0 := by
  unfold crossingBt crossingVelocity crossingZ
  field_simp
  ring

theorem crossing_transport_C_from_jet (m B C D A : ℝ) (hC : C ≠ 0) :
    crossingCt m B C D A + crossingVelocity m B (crossingZ C D) * D =
      C * crossingQ m C D A := by
  unfold crossingCt crossingVelocity crossingZ crossingQ
  field_simp
  ring

theorem crossing_transport_z_from_jet (m B C D A E : ℝ) (hC : C ≠ 0) :
    crossingZt m B C D A E + crossingVelocity m B (crossingZ C D) *
      (crossingQ m C D A + m * C) =
      crossingZ C D * crossingQ m C D A - crossingQx m C D A E / 2 := by
  unfold crossingZt crossingDt crossingCt crossingVelocity crossingZ crossingQ crossingQx
  field_simp
  ring

theorem crossingZ_hasDerivAt (C D A : ℝ → ℝ) (x : ℝ) (hC : C x ≠ 0)
    (hdC : HasDerivAt C (D x) x) (hdD : HasDerivAt D (A x) x) :
    HasDerivAt (fun y => crossingZ (C y) (D y))
      (-A x / (2 * C x) + D x ^ 2 / (2 * C x ^ 2)) x := by
  convert hdD.neg.div (hdC.const_mul 2) (mul_ne_zero (by norm_num) hC) using 1
  · rfl
  · simp only [Pi.neg_apply]
    field_simp
    ring

theorem crossingZ_hasDerivAt_Q (m : ℝ) (C D A : ℝ → ℝ) (x : ℝ) (hC : C x ≠ 0)
    (hdC : HasDerivAt C (D x) x) (hdD : HasDerivAt D (A x) x) :
    HasDerivAt (fun y => crossingZ (C y) (D y))
      (crossingQ m (C x) (D x) (A x) + m * C x) x := by
  simpa only [crossingQ, sub_add_cancel] using crossingZ_hasDerivAt C D A x hC hdC hdD

theorem crossingQ_hasDerivAt (m : ℝ) (C D A E : ℝ → ℝ) (x : ℝ) (hC : C x ≠ 0)
    (hdC : HasDerivAt C (D x) x) (hdD : HasDerivAt D (A x) x)
    (hdA : HasDerivAt A (E x) x) :
    HasDerivAt (fun y => crossingQ m (C y) (D y) (A y))
      (crossingQx m (C x) (D x) (A x) (E x)) x := by
  have hfirst := hdA.neg.div (hdC.const_mul 2) (mul_ne_zero (by norm_num) hC)
  have hsecond := (hdD.pow 2).div ((hdC.pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC))
  convert (hfirst.add hsecond).sub (hdC.const_mul m) using 1
  · ext y
    simp [crossingQ]
  · unfold crossingQx
    simp only [Pi.neg_apply, Pi.pow_apply]
    field_simp
    ring

theorem crossingH_spatial_identity (m C D A E : ℝ) (hC : C ≠ 0) :
    2 * crossingZ C D * (crossingQ m C D A + m * C) + m * D -
      2 * crossingQx m C D A E =
      2 * crossingZ C D * crossingQ m C D A - 2 * crossingQx m C D A E := by
  unfold crossingZ
  field_simp
  ring

end FRSB
