module

public import FRSB.CrossingAlgebra

@[expose] public section

/-! Section 5's strict order conclusions follow from the exact spatial
derivatives and the backward/forward shape inequalities. All inputs here
remain explicit until specialized to the actual PDE and density. -/

noncomputable section
open Set
namespace FRSB

theorem halfLine_closed_mem {x : ℝ} (hx : x ∈ Ioi (0 : ℝ)) :
    x ∈ Ici (0 : ℝ) := by
  change (0 : ℝ) < x at hx
  change (0 : ℝ) ≤ x
  exact hx.le

theorem strictMonoOn_halfLine_of_hasDerivAt_pos (f df : ℝ → ℝ)
    (hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Ioi (0 : ℝ), 0 < df x) : StrictMonoOn f (Ici 0) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
  · intro x hx
    exact (hd x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hd x (halfLine_closed_mem hx)).deriv]
    exact hp x hx

theorem pos_on_halfLine_of_zero_and_derivative_pos (f df : ℝ → ℝ)
    (hzero : f 0 = 0)
    (hd : ∀ x ∈ Ici (0 : ℝ), HasDerivAt f (df x) x)
    (hp : ∀ x ∈ Ioi (0 : ℝ), 0 < df x) :
    ∀ x ∈ Ioi (0 : ℝ), 0 < f x := by
  intro x hx
  have hs := strictMonoOn_halfLine_of_hasDerivAt_pos f df hd hp
    (show (0 : ℝ) ∈ Ici 0 by simp) (halfLine_closed_mem hx) hx
  simpa only [hzero] using hs

theorem crossing_z_pos (m : ℝ) (hm : 0 < m) (C Q z : ℝ → ℝ)
    (hz0 : z 0 = 0)
    (hz : ∀ x ∈ Ici (0 : ℝ), HasDerivAt z (Q x + m * C x) x)
    (hC : ∀ x ∈ Ici (0 : ℝ), 0 < C x)
    (hQ : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Q x) : ∀ x ∈ Ioi (0 : ℝ), 0 < z x := by
  apply pos_on_halfLine_of_zero_and_derivative_pos z (fun x => Q x + m * C x) hz0 hz
  intro x hx
  have hc := hC x (halfLine_closed_mem hx)
  have hq := hQ x (halfLine_closed_mem hx)
  positivity

theorem crossing_N_pos (N Vxx Q : ℝ → ℝ) (hN0 : N 0 = 0)
    (hN : ∀ x ∈ Ici (0 : ℝ), HasDerivAt N (Vxx x + Q x) x)
    (hVxx : ∀ x ∈ Ici (0 : ℝ), 0 < Vxx x)
    (hQ : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Q x) : ∀ x ∈ Ioi (0 : ℝ), 0 < N x := by
  apply pos_on_halfLine_of_zero_and_derivative_pos N (fun x => Vxx x + Q x) hN0 hN
  intro x hx
  have hv := hVxx x (halfLine_closed_mem hx)
  have hq := hQ x (halfLine_closed_mem hx)
  positivity

theorem crossingPhi_strictMonoOn (m : ℝ) (hm : 0 < m) (C z Q : ℝ → ℝ)
    (hCpos : ∀ x ∈ Ici (0 : ℝ), 0 < C x)
    (hQnonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Q x)
    (hzpos : ∀ x ∈ Ioi (0 : ℝ), 0 < z x)
    (hC : ∀ x ∈ Ici (0 : ℝ), HasDerivAt C (-2 * C x * z x) x)
    (hz : ∀ x ∈ Ici (0 : ℝ), HasDerivAt z (Q x + m * C x) x) :
    StrictMonoOn (fun x => crossingPhi m (C x) (z x)) (Ici 0) := by
  apply strictMonoOn_halfLine_of_hasDerivAt_pos _
    (fun x => 2 * z x * (2 * Q x + 3 * m * C x))
  · intro x hx
    exact crossingPhi_hasDerivAt m x C z Q (hC x hx) (hz x hx)
  · intro x hx
    exact crossingPhi_slope_pos m (C x) (z x) (Q x) hm (hCpos x (halfLine_closed_mem hx))
      (hzpos x hx) (hQnonneg x (halfLine_closed_mem hx))

theorem crossingK_strictMonoOn (m : ℝ) (C z Q N Vxx Vxxx : ℝ → ℝ)
    (hQnonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Q x)
    (hznonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ z x)
    (hNpos : ∀ x ∈ Ioi (0 : ℝ), 0 < N x)
    (hVxxpos : ∀ x ∈ Ici (0 : ℝ), 0 < Vxx x)
    (hVxxxnonpos : ∀ x ∈ Ici (0 : ℝ), Vxxx x ≤ 0)
    (hC : ∀ x ∈ Ici (0 : ℝ), HasDerivAt C (-2 * C x * z x) x)
    (hz : ∀ x ∈ Ici (0 : ℝ), HasDerivAt z (Q x + m * C x) x)
    (hN : ∀ x ∈ Ici (0 : ℝ), HasDerivAt N (Vxx x + Q x) x)
    (hVxx : ∀ x ∈ Ici (0 : ℝ), HasDerivAt Vxx (Vxxx x) x) :
    StrictMonoOn (fun x => crossingK m (C x) (z x) (N x) (Vxx x)) (Ici 0) := by
  apply strictMonoOn_halfLine_of_hasDerivAt_pos _
    (fun x => 2 * N x * (Vxx x + Q x) - Vxxx x + 2 * z x * Q x)
  · intro x hx
    exact crossingK_hasDerivAt m x C z Q N Vxx Vxxx (hC x hx) (hz x hx) (hN x hx) (hVxx x hx)
  · intro x hx
    exact crossingK_slope_pos (N x) (Vxx x) (Q x) (Vxxx x) (z x)
      (hNpos x hx) (hVxxpos x (halfLine_closed_mem hx)) (hQnonneg x (halfLine_closed_mem hx))
      (hVxxxnonpos x (halfLine_closed_mem hx)) (hznonneg x (halfLine_closed_mem hx))

theorem crossingPsi_strictMonoOn (m : ℝ) (hm : 0 < m) (C z Q N Vxx Hx : ℝ → ℝ)
    (hCpos : ∀ x ∈ Ici (0 : ℝ), 0 < C x)
    (hQnonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Q x)
    (hznonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ z x)
    (hNpos : ∀ x ∈ Ioi (0 : ℝ), 0 < N x)
    (hVxxpos : ∀ x ∈ Ici (0 : ℝ), 0 < Vxx x)
    (hHxnonneg : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Hx x)
    (hz : ∀ x ∈ Ici (0 : ℝ), HasDerivAt z (Q x + m * C x) x)
    (hN : ∀ x ∈ Ici (0 : ℝ), HasDerivAt N (Vxx x + Q x) x)
    (hQ : ∀ x ∈ Ici (0 : ℝ), HasDerivAt Q (z x * Q x - Hx x / 2) x) :
    StrictMonoOn (fun x => crossingPsi (z x) (N x) (Q x)) (Ici 0) := by
  apply strictMonoOn_halfLine_of_hasDerivAt_pos _
    (fun x => (Q x + m * C x) * N x + z x * (Vxx x + 2 * Q x + 2 * m * C x) + Hx x / 2)
  · intro x hx
    exact crossingPsi_hasDerivAt m x C z Q N Vxx Hx (hz x hx) (hN x hx) (hQ x hx)
  · intro x hx
    exact crossingPsi_slope_pos m (C x) (Q x) (N x) (z x) (Vxx x) (Hx x)
      hm (hCpos x (halfLine_closed_mem hx)) (hQnonneg x (halfLine_closed_mem hx)) (hNpos x hx)
      (hznonneg x (halfLine_closed_mem hx)) (hVxxpos x (halfLine_closed_mem hx)) (hHxnonneg x (halfLine_closed_mem hx))

theorem crossingH_monotoneOn (H Hx : ℝ → ℝ)
    (hH : ∀ x ∈ Ici (0 : ℝ), HasDerivAt H (Hx x) x)
    (hHx : ∀ x ∈ Ici (0 : ℝ), 0 ≤ Hx x) : MonotoneOn H (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro x hx
    exact (hH x hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact (hH x (halfLine_closed_mem hx)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    rw [(hH x (halfLine_closed_mem hx)).deriv]
    exact hHx x (halfLine_closed_mem hx)

end FRSB
