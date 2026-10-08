module

public import FRSB.CrossingBridgeFields
public import FRSB.CrossingActualMonotonicity
public import FRSB.ForwardBridgeParity

@[expose] public section

/-! Exact spatial derivatives of the actual crossing fields. Forward
shape comparisons are not presumed: their sign consequences will be
specialized separately after the actual forward construction. -/
noncomputable section
open Set Paper
open scoped ContDiff
namespace FRSB

def bridgeCrossingVxx (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  (β ^ 2 * s)⁻¹ + iteratedDeriv 2 (forwardBridgeCorrection β μ s hs) x

def bridgeCrossingVxxx (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ℝ → ℝ :=
  iteratedDeriv 3 (forwardBridgeCorrection β μ s hs)

def bridgeCrossingK (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) : ℝ :=
  crossingK (parisiCDF μ s) (backwardC β μ (s,x)) (backwardZ β μ (s,x))
    (bridgeCrossingN β μ s hs x) (bridgeCrossingVxx β μ s hs x)

theorem hasDerivAt_forwardBridgeCorrection_jet (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    HasDerivAt (iteratedDeriv j (forwardBridgeCorrection β μ s hs))
      (iteratedDeriv (j+1) (forwardBridgeCorrection β μ s hs) x) x := by
  have hd := ((contDiff_forwardBridgeCorrection β μ s hs).differentiable_iteratedDeriv j
    (by exact WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top j)) x).hasDerivAt
  simpa only [iteratedDeriv_succ] using hd

theorem forwardBridgeCorrection_deriv_origin (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    deriv (forwardBridgeCorrection β μ s hs) 0 = 0 := by
  have hd := ((contDiff_forwardBridgeCorrection β μ s hs).differentiable (by simp) 0).hasDerivAt
  have hdn : HasDerivAt (forwardBridgeCorrection β μ s hs)
      (deriv (forwardBridgeCorrection β μ s hs) 0) (-(0 : ℝ)) := by simpa using hd
  have hn := hdn.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg)
  have he : (forwardBridgeCorrection β μ s hs ∘ fun y : ℝ => -y) =
      forwardBridgeCorrection β μ s hs := funext (forwardBridgeCorrection_even β μ s hs)
  rw [he] at hn
  have hh := hn.unique hd
  linarith

theorem hasDerivAt_bridgeCrossingVx (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (bridgeCrossingVx β μ s hs) (bridgeCrossingVxx β μ s hs x) x := by
  have hd := ((hasDerivAt_id x).div_const (β ^ 2 * s)).add
    (by simpa only [iteratedDeriv_one] using hasDerivAt_forwardBridgeCorrection_jet β μ s hs 1 x)
  convert hd using 1
  · funext y; rfl
  · simp only [bridgeCrossingVxx, one_div, Nat.reduceAdd]

theorem hasDerivAt_bridgeCrossingVxx (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (bridgeCrossingVxx β μ s hs) (bridgeCrossingVxxx β μ s hs x) x :=
  (hasDerivAt_forwardBridgeCorrection_jet β μ s hs 2 x).const_add _

theorem bridgeCrossingN_origin (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) : bridgeCrossingN β μ s hs 0 = 0 := by
  simp only [bridgeCrossingN, bridgeCrossingVx, zero_div,
    forwardBridgeCorrection_deriv_origin, add_zero,
    backwardZ_at_zero β μ s ⟨hs.1.le,hs.2⟩,
    backwardB_at_zero β hβ μ s ⟨hs.1.le,hs.2⟩, mul_zero, sub_zero]

theorem hasDerivAt_bridgeCrossingN (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (bridgeCrossingN β μ s hs)
      (bridgeCrossingVxx β μ s hs x + backwardQ β μ (parisiCDF μ s) (s,x)) x := by
  apply crossingN_hasDerivAt (parisiCDF μ s) x (fun y => backwardB β μ (s,y))
    (fun y => backwardC β μ (s,y)) (fun y => backwardZ β μ (s,y))
    (fun y => backwardQ β μ (parisiCDF μ s) (s,y))
    (bridgeCrossingVx β μ s hs) (bridgeCrossingVxx β μ s hs)
  · exact hasDerivAt_backwardD β μ 1 s x ⟨hs.1.le,hs.2⟩
  · convert hasDerivAt_backwardZ β hβ μ s x ⟨hs.1.le,hs.2⟩ using 1
    dsimp [backwardQ,backwardQJet,backwardZx,backwardC]
    ring
  · exact hasDerivAt_bridgeCrossingVx β μ s hs x

theorem hasDerivAt_bridgeCrossingK (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (bridgeCrossingK β μ s hs)
      (2 * bridgeCrossingN β μ s hs x *
        (bridgeCrossingVxx β μ s hs x + backwardQ β μ (parisiCDF μ s) (s,x)) -
        bridgeCrossingVxxx β μ s hs x +
        2 * backwardZ β μ (s,x) * backwardQ β μ (parisiCDF μ s) (s,x)) x := by
  apply crossingK_hasDerivAt (parisiCDF μ s) x (fun y => backwardC β μ (s,y))
    (fun y => backwardZ β μ (s,y)) (fun y => backwardQ β μ (parisiCDF μ s) (s,y))
    (bridgeCrossingN β μ s hs) (bridgeCrossingVxx β μ s hs) (bridgeCrossingVxxx β μ s hs)
  · rw [← backwardD_three_eq_neg_two_C_z β hβ μ s x ⟨hs.1.le,hs.2⟩]
    exact hasDerivAt_backwardD β μ 2 s x ⟨hs.1.le,hs.2⟩
  · convert hasDerivAt_backwardZ β hβ μ s x ⟨hs.1.le,hs.2⟩ using 1
    dsimp [backwardQ,backwardQJet,backwardZx,backwardC]
    ring
  · exact hasDerivAt_bridgeCrossingN β hβ μ s hs x
  · exact hasDerivAt_bridgeCrossingVxx β μ s hs x

theorem hasDerivAt_bridgeCrossingPsi (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    HasDerivAt (bridgeCrossingPsi β μ s hs)
      ((backwardQ β μ (parisiCDF μ s) (s,x) + parisiCDF μ s * backwardC β μ (s,x)) *
        bridgeCrossingN β μ s hs x + backwardZ β μ (s,x) *
          (bridgeCrossingVxx β μ s hs x + 2 * backwardQ β μ (parisiCDF μ s) (s,x) +
            2 * parisiCDF μ s * backwardC β μ (s,x)) +
          backwardHx β μ (parisiCDF μ s) (s,x) / 2) x := by
  apply crossingPsi_hasDerivAt (parisiCDF μ s) x (fun y => backwardC β μ (s,y))
    (fun y => backwardZ β μ (s,y)) (fun y => backwardQ β μ (parisiCDF μ s) (s,y))
    (bridgeCrossingN β μ s hs) (bridgeCrossingVxx β μ s hs)
    (fun y => backwardHx β μ (parisiCDF μ s) (s,y))
  · convert hasDerivAt_backwardZ β hβ μ s x ⟨hs.1.le,hs.2⟩ using 1
    dsimp [backwardQ,backwardQJet,backwardZx,backwardC]
    ring
  · exact hasDerivAt_bridgeCrossingN β hβ μ s hs x
  · exact hasDerivAt_backwardQ_crossing_form β hβ μ (parisiCDF μ s) s x ⟨hs.1.le,hs.2⟩

end FRSB
