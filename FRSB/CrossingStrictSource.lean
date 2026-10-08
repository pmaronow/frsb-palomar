module

public import FRSB.CrossingThirdIBP
public import FRSB.CrossingActualForwardMonotonicity

@[expose] public section

/-! Strict positivity of the actual third-source mean at a crossing zero.
The centering, spatial integration by parts, probability law, integrability,
and strict covariance are all proved for the constructed objects. -/
noncomputable section
open Set Filter MeasureTheory Paper
namespace FRSB

theorem bridge_crossing_positive_covariances (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hm : 0 < parisiCDF μ s) :
    0 < crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s hs))
        (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x)) (bridgeCrossingK β μ s hs) / 2 +
      crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s hs))
        (fun x => backwardH β μ (parisiCDF μ s) (s,x)) (bridgeCrossingPsi β μ s hs) := by
  apply crossing_positive_representation_strict
    (bridgeCrossingWeight β μ s hs)
    (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s,x))
    (bridgeCrossingK β μ s hs)
    (fun x => backwardH β μ (parisiCDF μ s) (s,x))
    (bridgeCrossingPsi β μ s hs)
    (bridgeCrossingWeight_integrable β hβ μ s hs)
    (fun x _ => bridgeCrossingWeight_pos β hβ μ s hs x)
    (integrable_bridgeCrossingPhi β hβ μ s hs)
    (integrable_bridgeCrossingK β hβ μ s hs)
    (integrable_bridgeCrossingH β hβ μ s hs)
    (integrable_bridgeCrossingPsi β hβ μ s hs)
    (integrable_bridgeCrossingPhi_mul_K β hβ μ s hs)
    (integrable_bridgeCrossingH_mul_Psi β hβ μ s hs)
    (actualCrossingPhi_strictMonoOn β hβ μ s ⟨hs.1.le,hs.2⟩ hm)
    (bridgeCrossingK_strictMonoOn β hβ μ s hs)
    (actualCrossingH_monotoneOn β hβ μ s ⟨hs.1.le,hs.2⟩)
    (bridgeCrossingPsi_strictMonoOn β hβ μ s hs hm).monotoneOn

theorem bridge_crossing_source_pos_at_zero (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hm : 0 < parisiCDF μ s)
    (hzero : (∫ x, actualCrossingPhi β μ (parisiCDF μ s) (s,x)
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs)) = 0) :
    0 < ∫ x, bridgeCrossingThirdSource β μ s x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ s hs) := by
  have hpsi := bridge_crossing_centering β hβ μ s hs
  rw [hzero, neg_zero] at hpsi
  have hsrc := bridge_crossing_third_source_expectation β hβ μ s hs
  have hadd := integral_add ((integrable_bridgeCrossingPhi_mul_K β hβ μ s hs).div_const 2)
    (integrable_bridgeCrossingH_mul_Psi β hβ μ s hs)
  rw [hadd, integral_div] at hsrc
  have hpos := bridge_crossing_positive_covariances β hβ μ s hs hm
  unfold crossingCovariance at hpos
  rw [hzero, hpsi, zero_mul, mul_zero, sub_zero, sub_zero] at hpos
  rw [hsrc]
  exact hpos

end FRSB
