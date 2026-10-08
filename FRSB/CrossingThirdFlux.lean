module

public import FRSB.CrossingBridgeIntegrability

@[expose] public section

/-! A direct spatial integration-by-parts form of the crossing argument.
It connects the exact polynomial third Gamma derivative with the positive
covariance expression, without presuming a time derivative of the density. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

def crossingThirdSource (m C z Q : ℝ) : ℝ :=
  2 * (crossingPhi m C z - Q) ^ 2 - 24 * m * C * z ^ 2 + 3 * m ^ 2 * C ^ 2

def crossingThirdFlux (m C z N : ℝ) : ℝ :=
  crossingPhi m C z * N / 2 - 2 * z ^ 3 + (11 / 2 : ℝ) * m * C * z

theorem crossingThirdFlux_identity (m C z Q N Vxx : ℝ) :
    (2 * z * (2 * Q + 3 * m * C) * N / 2 + crossingPhi m C z * (Vxx + Q) / 2 -
      6 * z ^ 2 * (Q + m * C) + (11 / 2 : ℝ) * m *
        (-2 * C * z ^ 2 + C * (Q + m * C))) -
      (N + 3 * z) * crossingThirdFlux m C z N =
    crossingThirdSource m C z Q - crossingPhi m C z * crossingK m C z N Vxx / 2 -
      crossingH m C z Q * crossingPsi z N Q := by
  unfold crossingThirdFlux crossingThirdSource crossingPhi crossingK crossingH crossingPsi
  ring

theorem crossingThirdFlux_hasDerivAt (m x : ℝ) (C z Q N Vxx : ℝ → ℝ)
    (hC : HasDerivAt C (-2 * C x * z x) x)
    (hz : HasDerivAt z (Q x + m * C x) x)
    (hN : HasDerivAt N (Vxx x + Q x) x) :
    HasDerivAt (fun y => crossingThirdFlux m (C y) (z y) (N y))
      ((2 * z x * (2 * Q x + 3 * m * C x) * N x / 2 +
        crossingPhi m (C x) (z x) * (Vxx x + Q x) / 2 -
        6 * z x ^ 2 * (Q x + m * C x) + (11 / 2 : ℝ) * m *
          (-2 * C x * z x ^ 2 + C x * (Q x + m * C x)))) x := by
  have hd := (((crossingPhi_hasDerivAt m x C z Q hC hz).mul hN).div_const 2).sub
    ((hz.pow 3).const_mul 2) |>.add ((hC.mul hz).const_mul ((11/2 : ℝ)*m))
  convert hd using 1
  · funext y
    dsimp only [crossingThirdFlux,Pi.add_apply,Pi.sub_apply,Pi.mul_apply,Pi.pow_apply]
    ring
  · ring

def bridgeCrossingThirdSource (β : ℝ) (μ : ParisiMeasure) (s x : ℝ) : ℝ :=
  crossingThirdSource (parisiCDF μ s) (backwardC β μ (s,x)) (backwardZ β μ (s,x))
    (backwardQ β μ (parisiCDF μ s) (s,x))

def bridgeCrossingThirdFlux (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  crossingThirdFlux (parisiCDF μ s) (backwardC β μ (s,x)) (backwardZ β μ (s,x))
    (bridgeCrossingN β μ s hs x)

/-- The exact flux identity evaluated on actual spatial jets and the
concrete forward density. -/
theorem hasDerivAt_bridgeCrossingThirdFlux_weight (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (fun y => bridgeCrossingThirdFlux β μ s hs y * bridgeCrossingWeight β μ s hs y)
      ((bridgeCrossingThirdSource β μ s x -
        actualCrossingPhi β μ (parisiCDF μ s) (s,x) * bridgeCrossingK β μ s hs x / 2 -
        backwardH β μ (parisiCDF μ s) (s,x) * bridgeCrossingPsi β μ s hs x) *
          bridgeCrossingWeight β μ s hs x) x := by
  have hC : HasDerivAt (fun y => backwardC β μ (s,y))
      (-2 * backwardC β μ (s,x) * backwardZ β μ (s,x)) x := by
    rw [← backwardD_three_eq_neg_two_C_z β hβ μ s x ⟨hs.1.le,hs.2⟩]
    exact hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le,hs.2⟩
  have hz : HasDerivAt (fun y => backwardZ β μ (s,y))
      (backwardQ β μ (parisiCDF μ s) (s,x) + parisiCDF μ s * backwardC β μ (s,x)) x := by
    convert hasDerivAt_backwardZ β hβ μ s x ⟨hs.1.le,hs.2⟩ using 1
    dsimp [backwardQ,backwardQJet,backwardZx,backwardC]
    ring
  have hg := crossingThirdFlux_hasDerivAt (parisiCDF μ s) x
    (fun y => backwardC β μ (s,y)) (fun y => backwardZ β μ (s,y))
    (fun y => backwardQ β μ (parisiCDF μ s) (s,y)) (bridgeCrossingN β μ s hs)
    (bridgeCrossingVxx β μ s hs) hC hz (hasDerivAt_bridgeCrossingN β hβ μ s hs x)
  have hd := hg.mul (hasDerivAt_bridgeCrossingWeight β hβ μ s hs x)
  convert hd using 1
  · funext y; rfl
  · dsimp [bridgeCrossingThirdSource,bridgeCrossingThirdFlux,actualCrossingPhi,
      bridgeCrossingK,bridgeCrossingPsi,backwardH,backwardHJet,crossingH,crossingK,
      crossingPhi,crossingPsi,crossingThirdSource,crossingThirdFlux,backwardZ,
      backwardQ,backwardQJet,backwardZx,backwardZxJet,backwardZJet]
    ring
end FRSB
