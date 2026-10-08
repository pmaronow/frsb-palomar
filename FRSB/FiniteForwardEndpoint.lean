module

public import FRSB.FiniteForwardAction

@[expose] public section

/-! The actual optimal diffusion endpoint law for a finite overlap law is
exactly the Brownian path-action tilt. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper SpinGlass.Targets
open scoped NNReal ENNReal Topology
namespace FRSB

theorem measurable_forwardBrownianWeight_scheme {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) :
    Measurable (forwardBrownianWeight β (parisiSchemeMeasure s) t) := by
  have hh : Measurable (fun sample : BrownianSample =>
      finiteHistoryDensity (forwardSchemeWeight s β t) (k+2)
        (historySample (fun r sample => β*canonicalBrownian r sample)
          (forwardSchemeTime s t) (k+2) sample)) :=
    (measurable_finiteHistoryDensity _ (measurable_forwardSchemeWeight s β t) _).comp
      (measurable_historySample _ (fun r => (measurable_canonicalBrownian r).const_mul β) _ _)
  convert! hh using 1
  funext sample
  exact (finiteHistoryDensity_eq_forwardBrownianWeight s β t ht sample).symm

/-- Exact endpoint measure equality for every actual finite scheme. -/
theorem selectedState_endpoint_eq_BrownianTilt_scheme {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t) =
      (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β (parisiSchemeMeasure s) t)).map
        (fun sample => β*canonicalBrownian t sample) := by
  let D := finiteHistoryDensity (forwardSchemeWeight s β t) (k+2)
  let Y := historySample (fun r sample => β*canonicalBrownian r sample)
    (forwardSchemeTime s t) (k+2)
  let L : FiniteHistory (k+2) → ℝ := fun p => p (Fin.last (k+2))
  have hY : Measurable Y := measurable_historySample _
    (fun r => (measurable_canonicalBrownian r).const_mul β) _ _
  have hD : Measurable D := measurable_finiteHistoryDensity _ (measurable_forwardSchemeWeight s β t) _
  have hL : Measurable L := measurable_pi_apply _
  have hh := congrArg (fun Q : Measure (FiniteHistory (k+2)) => Q.map L)
    (selectedState_history_eq_tiltedBrownian s β hβ t ht (k+2))
  have hm := map_withDensity_pullback canonicalBrownianMeasure Y hY D hD
  change (_ : Measure ℝ) = ((canonicalBrownianMeasure.map Y).withDensity D).map L at hh
  rw [←hm,Measure.map_map hL hY,
    Measure.map_map hL (measurable_historySample _
      (measurable_selectedParisiState_time β 0 hβ _) _ _)] at hh
  have hd : (fun sample => D (Y sample)) = forwardBrownianWeight β (parisiSchemeMeasure s) t := by
    funext sample
    exact finiteHistoryDensity_eq_forwardBrownianWeight s β t ht sample
  rw [hd] at hh
  simpa only [L,Y,Function.comp_def,historySample,Fin.val_last,forwardSchemeTime_top s t ht le_rfl] using hh

/-- Every actual finite-support overlap law has the literal Brownian action
endpoint law; no scheme-representation premise is supplied. -/
theorem selectedState_endpoint_eq_BrownianTilt_finite (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ t) =
      (canonicalBrownianMeasure.withDensity (forwardBrownianWeight β μ t)).map
        (fun sample => β*canonicalBrownian t sample) := by
  simpa only [parisiSchemeMeasure_finiteLawRSBScheme] using
    selectedState_endpoint_eq_BrownianTilt_scheme (finiteLawRSBScheme μ hμ) β hβ t ht

end FRSB
