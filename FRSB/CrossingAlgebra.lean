module

public import Mathlib

@[expose] public section

/-!
# Exact transport and covariance algebra for Section 5

These are scalar identities and derivative calculations. Their differential
inputs are explicit; the actual PDE and density inputs must be discharged by
the backward/forward constructions before asserting the paper's crossing
theorem.
-/

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

def crossingPhi (m C z : ℝ) : ℝ := 2 * z ^ 2 - m * C
def crossingH (m C z Q : ℝ) : ℝ := z ^ 2 + m * C - 2 * Q
def crossingK (m C z N Vxx : ℝ) : ℝ := N ^ 2 - Vxx + z ^ 2 + m * C
def crossingPsi (z N Q : ℝ) : ℝ := z * (N + z) - Q
def crossingVelocity (m B z : ℝ) : ℝ := m * B - z

theorem crossingPhi_transport_identity (m C z Q Qx Hx : ℝ)
    (hHx : Hx = 2 * z * Q - 2 * Qx) :
    4 * z * (z * Q - Qx / 2) - m * (C * Q) =
      Q * crossingPhi m C z + z * Hx := by
  rw [hHx]
  unfold crossingPhi
  ring

theorem crossing_logp_transport_identity (m C z N Vxx : ℝ) :
    (m * C - Vxx) / 2 + (z - N) ^ 2 / 2 - m * C - z * (z - N) =
      crossingK m C z N Vxx / 2 - z ^ 2 - m * C := by
  unfold crossingK
  ring

theorem crossing_weight_transport_identity (m C z N Vxx Q : ℝ) :
    crossingK m C z N Vxx / 2 - z ^ 2 - m * C + 2 * Q - Q =
      crossingK m C z N Vxx / 2 - Q - crossingH m C z Q := by
  unfold crossingH
  ring

theorem crossing_centered_identity (m C z N Q omega : ℝ) (homega : omega ≠ 0) :
    -((-(N + 3 * z) * omega) * z + omega * (Q + m * C)) / omega =
      crossingPhi m C z + crossingPsi z N Q := by
  unfold crossingPhi crossingPsi
  field_simp
  ring

theorem crossing_centered_product_identity (m C z N Q omega : ℝ) :
    -((-(N + 3 * z) * omega) * z + omega * (Q + m * C)) =
      omega * (crossingPhi m C z + crossingPsi z N Q) := by
  unfold crossingPhi crossingPsi
  ring

theorem crossingPhi_hasDerivAt (m x : ℝ) (C z Q : ℝ → ℝ)
    (hC : HasDerivAt C (-2 * C x * z x) x)
    (hz : HasDerivAt z (Q x + m * C x) x) :
    HasDerivAt (fun y => crossingPhi m (C y) (z y))
      (2 * z x * (2 * Q x + 3 * m * C x)) x := by
  convert ((hz.pow 2).const_mul 2).sub (hC.const_mul m) using 1
  · ext y
    simp only [crossingPhi, Pi.sub_apply, Pi.pow_apply]
  · ring

theorem crossingN_hasDerivAt (m x : ℝ) (B C z Q Vx Vxx : ℝ → ℝ)
    (hB : HasDerivAt B (C x) x)
    (hz : HasDerivAt z (Q x + m * C x) x)
    (hVx : HasDerivAt Vx (Vxx x) x) :
    HasDerivAt (fun y => Vx y + z y - m * B y) (Vxx x + Q x) x := by
  convert (hVx.add hz).sub (hB.const_mul m) using 1
  ring

theorem crossingK_hasDerivAt (m x : ℝ) (C z Q N Vxx Vxxx : ℝ → ℝ)
    (hC : HasDerivAt C (-2 * C x * z x) x)
    (hz : HasDerivAt z (Q x + m * C x) x)
    (hN : HasDerivAt N (Vxx x + Q x) x)
    (hVxx : HasDerivAt Vxx (Vxxx x) x) :
    HasDerivAt (fun y => crossingK m (C y) (z y) (N y) (Vxx y))
      (2 * N x * (Vxx x + Q x) - Vxxx x + 2 * z x * Q x) x := by
  convert (((hN.pow 2).sub hVxx).add (hz.pow 2)).add (hC.const_mul m) using 1
  · ext y
    simp [crossingK]
  · ring

theorem crossingPsi_hasDerivAt (m x : ℝ) (C z Q N Vxx Hx : ℝ → ℝ)
    (hz : HasDerivAt z (Q x + m * C x) x)
    (hN : HasDerivAt N (Vxx x + Q x) x)
    (hQ : HasDerivAt Q (z x * Q x - Hx x / 2) x) :
    HasDerivAt (fun y => crossingPsi (z y) (N y) (Q y))
      ((Q x + m * C x) * N x + z x * (Vxx x + 2 * Q x + 2 * m * C x) +
        Hx x / 2) x := by
  convert (hz.mul (hN.add hz)).sub hQ using 1
  · ext y
    simp [crossingPsi]
  · simp only [Pi.add_apply]
    ring

theorem crossingPhi_slope_pos (m C z Q : ℝ)
    (hm : 0 < m) (hC : 0 < C) (hz : 0 < z) (hQ : 0 ≤ Q) :
    0 < 2 * z * (2 * Q + 3 * m * C) := by positivity

theorem crossingK_slope_pos (N Vxx Q Vxxx z : ℝ)
    (hN : 0 < N) (hVxx : 0 < Vxx) (hQ : 0 ≤ Q)
    (hVxxx : Vxxx ≤ 0) (hz : 0 ≤ z) :
    0 < 2 * N * (Vxx + Q) - Vxxx + 2 * z * Q := by
  have hp : 0 < 2 * N * (Vxx + Q) := by positivity
  have hq : 0 ≤ 2 * z * Q := by positivity
  linarith

theorem crossingPsi_slope_pos (m C Q N z Vxx Hx : ℝ)
    (hm : 0 < m) (hC : 0 < C) (hQ : 0 ≤ Q) (hN : 0 < N)
    (hz : 0 ≤ z) (hVxx : 0 < Vxx) (hHx : 0 ≤ Hx) :
    0 < (Q + m * C) * N + z * (Vxx + 2 * Q + 2 * m * C) + Hx / 2 := by
  positivity

/-- Cancellation of the Q and H covariances after genuine integration.
Symmetry and linearity of covariance must be supplied by their actual
probability-measure proofs, not by this scalar identity. -/
theorem crossing_covariance_cancellation (eq f cQPhi cHPhi cHPsi cPhiK : ℝ) :
    (eq * f + cQPhi) + (cHPhi + cHPsi) +
      (cPhiK / 2 - cQPhi - cHPhi) - eq * f = cPhiK / 2 + cHPsi := by ring

theorem crossing_representation_pos (cPhiK cHPsi : ℝ)
    (hstrict : 0 < cPhiK) (hnonneg : 0 ≤ cHPsi) :
    0 < cPhiK / 2 + cHPsi := by linarith

/-- The conversion from rescaled time t to physical time s. -/
theorem crossing_third_derivative_pos (beta Z ft : ℝ)
    (hbeta : beta ≠ 0) (hZ : 0 < Z) (hft : 0 < ft) :
    0 < 2 * beta ^ 6 * Z * ft := by
  have hb : 0 < beta ^ 6 := pow_pos (sq_pos_of_ne_zero hbeta) 3 |>.trans_eq (by ring)
  positivity

end FRSB
