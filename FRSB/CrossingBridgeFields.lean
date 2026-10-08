module

public import FRSB.CrossingBridgeWeight

@[expose] public section

/-! Spatial transport fields of the concrete Gaussian-bridge density.
All derivatives below are of the actual selected Parisi potential and the
actual bridge candidate. The diffusion-law identification is separate. -/
noncomputable section
open Set Paper
namespace FRSB

def bridgeCrossingVx (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  x / (β ^ 2 * s) + deriv (forwardBridgeCorrection β μ s hs) x

def bridgeCrossingN (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  bridgeCrossingVx β μ s hs x + backwardZ β μ (s, x) -
    parisiCDF μ s * backwardB β μ (s, x)

def bridgeCrossingPsi (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  backwardZ β μ (s, x) * (bridgeCrossingN β μ s hs x + backwardZ β μ (s, x)) -
    backwardQ β μ (parisiCDF μ s) (s, x)

theorem forwardBridgeDensity_eq_exponential (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeDensity β μ s hs x =
      (Real.sqrt (2 * Real.pi * (β ^ 2 * s)))⁻¹ *
        Real.exp (-x ^ 2 / (2 * (β ^ 2 * s)) +
          parisiCDF μ s * parisiPotential β μ (s, x) - forwardBridgeCorrection β μ s hs x) := by
  unfold forwardBridgeDensity heatDensity forwardBridgeCorrection
  rw [sub_neg_eq_add, Real.exp_add, Real.exp_add,
    Real.exp_log (forwardBridgeFactor_pos β μ s hs x)]
  ring

theorem hasDerivAt_forwardBridgeDensity_score (β : ℝ) (_hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (forwardBridgeDensity β μ s hs)
      ((parisiCDF μ s * backwardB β μ (s, x) - bridgeCrossingVx β μ s hs x) *
        forwardBridgeDensity β μ s hs x) x := by
  have hU := (hasDerivAt_parisiPotential_spatial_all β μ s x ⟨hs.1.le, hs.2⟩).const_mul
    (parisiCDF μ s)
  have hW := ((contDiff_forwardBridgeCorrection β μ s hs).differentiable (by simp) x).hasDerivAt
  have he := (((((hasDerivAt_id x).pow 2).neg.div_const (2 * (β ^ 2 * s))).add hU).sub hW).exp.const_mul
    (Real.sqrt (2 * Real.pi * (β ^ 2 * s)))⁻¹
  have hB := backwardB_eq_gradient β μ s x ⟨hs.1.le, hs.2⟩
  convert he using 1
  · funext y
    exact forwardBridgeDensity_eq_exponential β μ s hs y
  · rw [forwardBridgeDensity_eq_exponential, hB]
    unfold bridgeCrossingVx
    dsimp only [Pi.sub_apply, Pi.add_apply, Pi.neg_apply, Pi.pow_apply, id_eq]
    ring

/-- The weighted density's score is -(N+3z). -/
theorem hasDerivAt_bridgeCrossingWeight (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (bridgeCrossingWeight β μ s hs)
      (-(bridgeCrossingN β μ s hs x + 3 * backwardZ β μ (s, x)) *
        bridgeCrossingWeight β μ s hs x) x := by
  have hd := (((hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le, hs.2⟩).pow 2).const_mul 2).mul
    (hasDerivAt_forwardBridgeDensity_score β hβ μ s hs x)
  convert hd using 1
  · funext y; rfl
  · dsimp only [Pi.pow_apply]
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceSub, pow_one]
    rw [backwardD_three_eq_neg_two_C_z β hβ μ s x ⟨hs.1.le, hs.2⟩]
    unfold bridgeCrossingWeight bridgeCrossingN backwardC
    ring

/-- The exact spatial flux used in the centering integration by parts. -/
theorem hasDerivAt_bridgeCrossingWeight_mul_z (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (fun y => bridgeCrossingWeight β μ s hs y * backwardZ β μ (s, y))
      (-(actualCrossingPhi β μ (parisiCDF μ s) (s, x) + bridgeCrossingPsi β μ s hs x) *
        bridgeCrossingWeight β μ s hs x) x := by
  have hd := (hasDerivAt_bridgeCrossingWeight β hβ μ s hs x).mul
    (hasDerivAt_backwardZ β hβ μ s x ⟨hs.1.le, hs.2⟩)
  convert hd using 1
  unfold bridgeCrossingPsi actualCrossingPhi crossingPhi backwardQ backwardQJet backwardZx
  ring

end FRSB
