module

public import FRSB.CrossingBridgeDifferentiation
public import FRSB.CrossingActualMonotonicity
public import FRSB.ForwardPropositionShape

@[expose] public section

/-! Actual strict spatial order for the forward fields used in crossing.
All backward and forward shape inequalities refer to the constructed solution. -/
noncomputable section
open Set Paper
namespace FRSB

theorem bridgeCrossingVxx_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    0 < bridgeCrossingVxx β μ s hs x :=
  add_pos_of_pos_of_nonneg (inv_pos.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1))
    (forwardBridgeCorrection_curvature_nonneg β hβ μ s hs x)

theorem bridgeCrossingN_pos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : 0 < x) :
    0 < bridgeCrossingN β μ s hs x := by
  apply crossing_N_pos (bridgeCrossingN β μ s hs) (bridgeCrossingVxx β μ s hs)
    (fun y => backwardQ β μ (parisiCDF μ s) (s,y))
    (bridgeCrossingN_origin β hβ μ s hs)
    (fun y _ => hasDerivAt_bridgeCrossingN β hβ μ s hs y)
    (fun y _ => bridgeCrossingVxx_pos β hβ μ s hs y)
    (fun y _ => backwardQ_nonneg β hβ μ s y ⟨hs.1.le,hs.2⟩) x hx

theorem bridgeCrossingK_strictMonoOn (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    StrictMonoOn (bridgeCrossingK β μ s hs) (Ici 0) := by
  apply strictMonoOn_halfLine_of_hasDerivAt_pos _
    (fun x => 2 * bridgeCrossingN β μ s hs x *
      (bridgeCrossingVxx β μ s hs x + backwardQ β μ (parisiCDF μ s) (s,x)) -
      bridgeCrossingVxxx β μ s hs x + 2 * backwardZ β μ (s,x) *
        backwardQ β μ (parisiCDF μ s) (s,x))
  · exact fun x _ => hasDerivAt_bridgeCrossingK β hβ μ s hs x
  · intro x hx
    exact crossingK_slope_pos _ _ _ _ _ (bridgeCrossingN_pos β hβ μ s hs x hx)
      (bridgeCrossingVxx_pos β hβ μ s hs x)
      (backwardQ_nonneg β hβ μ s x ⟨hs.1.le,hs.2⟩)
      (forwardBridgeCorrection_third_nonpos β hβ μ s hs x hx.le)
      ((mul_nonneg (parisiCDF_nonneg μ s)
        (backwardB_nonneg β hβ μ s x ⟨hs.1.le,hs.2⟩ hx.le)).trans
          (backwardZ_ge_massB β hβ μ s x ⟨hs.1.le,hs.2⟩ hx.le))

theorem bridgeCrossingPsi_strictMonoOn (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (hm : 0 < parisiCDF μ s) :
    StrictMonoOn (bridgeCrossingPsi β μ s hs) (Ici 0) := by
  apply strictMonoOn_halfLine_of_hasDerivAt_pos _
    (fun x => (backwardQ β μ (parisiCDF μ s) (s,x) + parisiCDF μ s * backwardC β μ (s,x)) *
      bridgeCrossingN β μ s hs x + backwardZ β μ (s,x) *
        (bridgeCrossingVxx β μ s hs x + 2 * backwardQ β μ (parisiCDF μ s) (s,x) +
          2 * parisiCDF μ s * backwardC β μ (s,x)) +
            backwardHx β μ (parisiCDF μ s) (s,x) / 2)
  · exact fun x _ => hasDerivAt_bridgeCrossingPsi β hβ μ s hs x
  · intro x hx
    exact crossingPsi_slope_pos _ _ _ _ _ _ _ hm
      (backwardC_pos β hβ μ s x ⟨hs.1.le,hs.2⟩)
      (backwardQ_nonneg β hβ μ s x ⟨hs.1.le,hs.2⟩)
      (bridgeCrossingN_pos β hβ μ s hs x hx)
      (actualCrossing_z_pos β hβ μ s x ⟨hs.1.le,hs.2⟩ hm hx).le
      (bridgeCrossingVxx_pos β hβ μ s hs x)
      (backwardHx_bounds β hβ μ s x ⟨hs.1.le,hs.2⟩ hx.le).1

end FRSB
