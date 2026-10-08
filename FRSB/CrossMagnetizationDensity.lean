module

public import FRSB.CrossMomentTransfer
public import FRSB.BackwardsMagnetizationRemark
public import FRSB.CrossingActualWeightTime
public import Mathlib.MeasureTheory.Function.JacobianOneDim

@[expose] public section

/-! Literal change to the magnetization coordinate. The actual diffusion
has density p/C in this coordinate, and the curvature-square crossing tilt
has normalized density proportional to r=p*C on [0,1). -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff ENNReal
namespace FRSB

/-- One-dimensional Jacobian substitution, including restricted domains.
The actual strict positive curvature discharges every premise below. -/
 theorem map_positiveJacobian_density (B c p g : ℝ → ℝ) (S : Set ℝ)
    (hS : MeasurableSet S) (hB : Measurable B) (hi : Function.Injective B)
    (hd : ∀ x,HasDerivAt B (c x) x) (hc : ∀ x,0 < c x)
    (hg : ∀ x,g (B x) = x) :
    ((volume.restrict S).withDensity (fun x => ENNReal.ofReal (p x))).map B =
      (volume.restrict (B '' S)).withDensity
        (fun b => ENNReal.ofReal (p (g b) / c (g b))) := by
  ext E hE
  rw [Measure.map_apply hB hE,withDensity_apply _ (hE.preimage hB),
    withDensity_apply _ hE,Measure.restrict_restrict (hE.preimage hB),
    Measure.restrict_restrict hE]
  have himage : B '' (B ⁻¹' E ∩ S) = E ∩ B '' S := by
    ext b
    constructor
    · rintro ⟨x,⟨hxE,hxS⟩,rfl⟩
      exact ⟨hxE,⟨x,hxS,rfl⟩⟩
    · rintro ⟨hbE,x,hxS,rfl⟩
      exact ⟨x,⟨hbE,hxS⟩,rfl⟩
  rw [← himage,lintegral_image_eq_lintegral_abs_deriv_mul
    ((hE.preimage hB).inter hS) (fun x _ => (hd x).hasDerivWithinAt) hi.injOn]
  apply lintegral_congr_ae
  exact .of_forall fun x => by
    dsimp only
    rw [abs_of_pos (hc x),hg x,← ENNReal.ofReal_mul (hc x).le]
    congr 1
    field_simp [(hc x).ne']

 def magnetizationDensity (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (b : ℝ) : ℝ :=
  forwardBridgeDensity β μ s hs (magnetizationInverse β μ s b) /
    backwardC β μ (s,magnetizationInverse β μ s b)

 def magnetizationWeightedDensity (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (b : ℝ) : ℝ :=
  forwardBridgeDensity β μ s hs (magnetizationInverse β μ s b) *
    backwardC β μ (s,magnetizationInverse β μ s b)

 theorem magnetizationWeightedDensity_eq_chi_sq_density (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (b : ℝ) :
    magnetizationWeightedDensity β μ s hs b =
      backwardC β μ (s,magnetizationInverse β μ s b)^2 * magnetizationDensity β μ s hs b := by
  have hp := (backwardC_pos β hβ μ s (magnetizationInverse β μ s b) ⟨hs.1.le,hs.2⟩).ne'
  unfold magnetizationWeightedDensity magnetizationDensity
  field_simp

 theorem gradient_image_positiveHalfLine (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    (fun x => parisiGradient β μ (s,x)) '' Ioi (0 : ℝ) = Ioo (0 : ℝ) 1 := by
  ext b
  constructor
  · rintro ⟨x,hx,rfl⟩
    have hp := parisiGradient_strictMono β hβ μ s hs hx
    dsimp only at hp
    rw [parisiGradient_at_zero β hβ μ s hs] at hp
    exact ⟨hp,(parisiGradient_mem_Ioo β hβ μ s x hs).2⟩
  · intro hb
    let x := magnetizationInverse β μ s b
    have hxB : parisiGradient β μ (s,x) = b :=
      parisiGradient_magnetizationInverse β hβ μ s b hs ⟨by linarith [hb.1],hb.2⟩
    refine ⟨x,?_,hxB⟩
    by_contra hx
    have h := (parisiGradient_strictMono β hβ μ s hs).monotone (le_of_not_gt hx)
    rw [hxB,parisiGradient_at_zero β hβ μ s hs] at h
    exact (not_le_of_gt hb.1) h

/-- The genuine law of the magnetization martingale has density p/C on
(-1,1), with no assumed density or change-of-variables premise. -/
 theorem magnetizationState_density_law (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    canonicalBrownianMeasure.map (M β μ s) =
      (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
        (fun b => ENNReal.ofReal (magnetizationDensity β μ s hs b)) := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  have hcomp : M β μ s =
      (fun x => parisiGradient β μ (s,x)) ∘ selectedParisiItoState β 0 hβ μ s.toNNReal := by
    funext sample
    dsimp only [Function.comp_def,M,jetProcess]
    rw [parisiSpatialJet_one,selectedItoState_eq_optimalStateReal β hβ μ s ht sample]
  have hBm : Measurable (fun x => parisiGradient β μ (s,x)) :=
    (continuous_parisiGradient β μ |>.comp (continuous_const.prodMk continuous_id)).measurable
  rw [hcomp,← Measure.map_map hBm
    (measurable_selectedParisiState_time β 0 hβ μ s.toNNReal),
    selectedState_endpoint_eq_bridgeDensity β hβ μ s hs]
  have h := map_positiveJacobian_density (fun x => parisiGradient β μ (s,x))
    (fun x => backwardC β μ (s,x)) (forwardBridgeDensity β μ s hs)
    (magnetizationInverse β μ s) univ MeasurableSet.univ
    (continuous_parisiGradient β μ |>.comp (continuous_const.prodMk continuous_id) |>.measurable)
    (parisiGradient_strictMono β hβ μ s ht).injective
    (fun x => by
      rw [backwardC_eq_hessian β μ s x ht]
      exact hasDerivAt_parisiGradient_spatial_all β μ s x)
    (fun x => backwardC_pos β hβ μ s x ht)
    (fun x => magnetizationInverse_parisiGradient β hβ μ s x ht)
  simpa only [Measure.restrict_univ,image_univ,parisiGradient_range β hβ μ s ht,
    magnetizationDensity] using h

/-- The actual half-line crossing probability pushes forward to the
normalized density 2r/Z on [0,1), where r=p*C and Z=E[C_s²]. -/
 theorem crossingWeightLaw_magnetization_density (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (crossingWeightLaw (bridgeCrossingWeight β μ s hs)).map
      (fun x => parisiGradient β μ (s,x)) =
      (volume.restrict (Ico (0 : ℝ) 1)).withDensity
        (fun b => ENNReal.ofReal (2*magnetizationWeightedDensity β μ s hs b /
          curvatureMoment2 β μ s)) := by
  have ht : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le,hs.2⟩
  unfold crossingWeightLaw
  have h := map_positiveJacobian_density (fun x => parisiGradient β μ (s,x))
    (fun x => backwardC β μ (s,x))
    (fun x => bridgeCrossingWeight β μ s hs x /
      crossingWeightMass (bridgeCrossingWeight β μ s hs))
    (magnetizationInverse β μ s) (Ioi (0 : ℝ)) measurableSet_Ioi
    (continuous_parisiGradient β μ |>.comp (continuous_const.prodMk continuous_id) |>.measurable)
    (parisiGradient_strictMono β hβ μ s ht).injective
    (fun x => by
      rw [backwardC_eq_hessian β μ s x ht]
      exact hasDerivAt_parisiGradient_spatial_all β μ s x)
    (fun x => backwardC_pos β hβ μ s x ht)
    (fun x => magnetizationInverse_parisiGradient β hβ μ s x ht)
  rw [h,gradient_image_positiveHalfLine β hβ μ s ht,
    Measure.restrict_congr_set (Ioo_ae_eq_Ico' (by simp : volume {(0 : ℝ)} = 0))]
  apply withDensity_congr_ae
  exact .of_forall fun b => by
    have hC := (backwardC_pos β hβ μ s (magnetizationInverse β μ s b) ht).ne'
    rw [crossingWeightMass_bridge_eq_curvatureMoment2 β hβ μ s hs]
    unfold bridgeCrossingWeight magnetizationWeightedDensity
    field_simp

end FRSB
