module

public import FRSB.BrownianBridgeLaw
public import FRSB.FiniteJointLaw
public import FRSB.ForwardBridgeLawLimit

@[expose] public section

/-! Genuine Gaussian endpoint disintegration of a weighted Wiener path law. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped NNReal ENNReal Topology
namespace FRSB

theorem weighted_product_snd {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) (Q : Measure B) [SFinite P] [SFinite Q]
    (D : A × B → ℝ≥0∞) (hD : Measurable D) :
    ((P.prod Q).withDensity D).map Prod.snd =
      Q.withDensity (fun y => ∫⁻ x, D (x,y) ∂P) := by
  ext s hs
  rw [Measure.map_apply measurable_snd hs,withDensity_apply _ (measurable_snd hs),
    withDensity_apply _ hs]
  have hset : Prod.snd ⁻¹' s = (univ : Set A) ×ˢ s := by ext p; simp
  rw [hset,← Measure.prod_restrict,Measure.restrict_univ]
  exact lintegral_prod_symm D hD.aemeasurable

theorem bridge_path_weight_marginal (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1) (x : ℝ) :
    (∫⁻ path, ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x) -
        forwardBridgeAction β μ s hs path x)) ∂canonicalWienerMeasure) =
      ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x)) *
        forwardBridgeFactor β μ s hs x) := by
  have he : (fun path => ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x) -
      forwardBridgeAction β μ s hs path x))) =
      fun path => ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x))) *
        ENNReal.ofReal (forwardBridgePathFactor β μ s hs path x) := by
    funext path
    rw [sub_eq_add_neg,Real.exp_add,ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl
  have hfac : Measurable (fun path => forwardBridgePathFactor β μ s hs path x) := by
    simpa only [iteratedDeriv_zero,Function.comp_def] using
      ((continuous_iteratedDeriv_forwardBridgePathFactor β μ s hs 0).comp
        (show Continuous (fun path : ForwardBridgePath => (path,x)) by fun_prop)).measurable
  rw [he,lintegral_const_mul _ hfac.ennreal_ofReal]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_forwardBridgePathFactor β μ s hs x)
    (.of_forall fun path => (forwardBridgePathFactor_pos β μ s hs path x).le)]
  exact (ENNReal.ofReal_mul (Real.exp_pos _).le).symm

/-- An actual weighted scaled-Wiener path law has the literal bridge density
at its endpoint. The weight's pullback is the explicit Feynman--Kac action. -/
theorem bridge_endpoint_density_of_pullback (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0:ℝ) 1)
    (D : ForwardBridgePath → ℝ≥0∞) (hD : Measurable D)
    (hbridge : ∀ path x, D (forwardBridgeAsPath β s hs path x) =
      ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x) -
        forwardBridgeAction β μ s hs path x))) :
    ((canonicalWienerMeasure.map (scaledBrownianPath β)).withDensity D).map
      (fun path => path ⟨s,hs.1.le,hs.2⟩) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) := by
  let G := gaussianReal 0 (β^2*s).toNNReal
  let R : ForwardBridgePath × ℝ → ForwardBridgePath :=
    fun p => forwardBridgeAsPath β s hs p.1 p.2
  let E : ForwardBridgePath → ℝ := fun path => path ⟨s,hs.1.le,hs.2⟩
  have hR : Measurable R := measurable_forwardBridgeAsPath β s hs
  have hE : Measurable E := (ProbabilityTheory.ContinuousMap.measurable_iff_eval
    (fun path : ForwardBridgePath => path)).mp measurable_id _
  have hRE : E ∘ R = Prod.snd := by
    funext p
    exact forwardBridgePoint_at_endpoint β s hs p.1 p.2
  rw [← forwardBridge_scaled_wiener_law β s hs,
    ← map_withDensity_pullback _ R hR D hD,Measure.map_map hE hR]
  rw [hRE]
  have hDR : Measurable (fun p => D (R p)) := hD.comp hR
  rw [weighted_product_snd canonicalWienerMeasure
    (gaussianReal 0 (β^2*s).toNNReal) (fun p => D (R p)) hDR]
  have hinner : (fun x => ∫⁻ path, D (R (path,x)) ∂canonicalWienerMeasure) =
      fun x => ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x)) *
        forwardBridgeFactor β μ s hs x) := by
    funext x
    simp_rw [R,hbridge]
    exact bridge_path_weight_marginal β μ s hs x
  rw [hinner,gaussianReal_of_var_ne_zero _
    (ne_of_gt (Real.toNNReal_pos.mpr (mul_pos (sq_pos_of_ne_zero hβ) hs.1))),
    ← withDensity_mul _ (measurable_gaussianPDF _ _) ((by
      have hu : Continuous (fun x : ℝ => parisiPotential β μ (s,x)) :=
        (continuous_parisiPotential β μ).comp (continuous_const.prodMk continuous_id)
      have hf : Continuous (forwardBridgeFactor β μ s hs) := (contDiff_forwardBridgeFactor β μ s hs).continuous
      exact ((Real.continuous_exp.comp (continuous_const.mul hu)).mul hf).measurable.ennreal_ofReal) :
      Measurable (fun x => ENNReal.ofReal (Real.exp (parisiCDF μ s * parisiPotential β μ (s,x)) *
        forwardBridgeFactor β μ s hs x)))]
  congr 1
  funext x
  dsimp only [Pi.mul_apply]
  rw [gaussianPDF,← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
  unfold forwardBridgeDensity
  rw [heatDensity_eq_gaussianPDFReal (mul_pos (sq_pos_of_ne_zero hβ) hs.1).le]
  congr 1
  ring

end FRSB
