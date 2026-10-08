module

public import FRSB.PolynomialStochasticEndpoints

@[expose] public section

/-! Actual adaptedness and square integrability of the polynomial stochastic
coefficients and represented endpoint remainders. Uniform derivative bounds
are discharged by the constructed PDE, for arbitrary Parisi measures. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace FRSB
set_option maxHeartbeats 400000

 theorem stronglyAdapted_selectedPolynomialProcess (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) :
    StronglyAdapted canonicalBrownianFiltration (selectedPolynomialProcess β hβ μ F) := by
  intro t
  unfold selectedPolynomialProcess
  have hf : Continuous (fun x : ℝ => polynomialJetField β μ F (t:ℝ) x) := by
    convert (continuous_polynomialJetField β μ F).comp
      (continuous_const.prodMk continuous_id) using 1
    rfl
  convert hf.comp_stronglyMeasurable
    ((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t) using 1

 theorem norm_selectedPolynomialProcess_le (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (t : ℝ≥0) (ω : BrownianSample) :
    ‖selectedPolynomialProcess β hβ μ F t ω‖ ≤ uniformPolynomialMomentBound β F :=
  norm_polynomialJetField_le_uniform β μ F _ _

 theorem memLp_selectedPolynomialProcess (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (t : ℝ≥0) :
    MemLp (selectedPolynomialProcess β hβ μ F t) 2 canonicalBrownianMeasure :=
  MemLp.of_bound (((stronglyAdapted_selectedPolynomialProcess β hβ μ F t).mono
    (canonicalBrownianFiltration.le t)).aestronglyMeasurable)
    (uniformPolynomialMomentBound β F) (.of_forall (norm_selectedPolynomialProcess_le β hβ μ F t))

 theorem measurable_selectedPolynomialField (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) :
    Measurable (fun p : ℝ×BrownianSample => polynomialJetField β μ F p.1
      (selectedParisiItoState β 0 hβ μ p.1.toNNReal p.2)) := by
  have hNN : Measurable (Function.uncurry (selectedParisiItoState β 0 hβ μ)) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).continuous_state
    intro t
    exact (((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t).measurable).mono
      (canonicalBrownianFiltration.le t) le_rfl
  have hX : Measurable (fun p : ℝ×BrownianSample => selectedParisiItoState β 0 hβ μ p.1.toNNReal p.2) := by
    convert hNN.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd) using 1
    rfl
  convert (continuous_polynomialJetField β μ F).measurable.comp (measurable_fst.prodMk hX) using 1
  rfl

 theorem memLp_selectedPolynomialBrownianCoefficient (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (T : ℝ≥0) :
    MemLp (fun p : ℝ×BrownianSample => polynomialJetField β μ (polynomialSpatialDerivative F) p.1
      (selectedParisiItoState β 0 hβ μ p.1.toNNReal p.2)) 2
      ((volume.restrict (Icc (0:ℝ) (T:ℝ))).prod canonicalBrownianMeasure) := by
  haveI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) (T:ℝ))) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using
      ((isCompact_Icc (a := (0:ℝ)) (b := (T:ℝ))).measure_lt_top (μ := (volume : Measure ℝ)))⟩
  exact MemLp.of_bound (measurable_selectedPolynomialField β hβ μ _).aestronglyMeasurable
    (uniformPolynomialMomentBound β (polynomialSpatialDerivative F))
    (.of_forall fun p => norm_polynomialJetField_le_uniform β μ _ _ _)

 def polynomialItoRemainder (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (F : MomentPolynomial) (a b : ℝ≥0) (ω : BrownianSample) : ℝ :=
  selectedPolynomialProcess β hβ μ F b ω-selectedPolynomialProcess β hβ μ F a ω-
    ∫t in (a:ℝ)..(b:ℝ),selectedPolynomialDrift β hβ μ F t ω

 theorem memLp_polynomialItoRemainder (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (F : MomentPolynomial) (a b : ℝ≥0) :
    MemLp (polynomialItoRemainder β hβ μ F a b) 2 canonicalBrownianMeasure := by
  have hm (t : ℝ≥0) := (stronglyAdapted_selectedPolynomialProcess β hβ μ F t).mono
    (canonicalBrownianFiltration.le t)
  have hi := stronglyMeasurable_selectedPolynomialDrift_integral β hβ μ F (a:ℝ) (b:ℝ)
  let D := β^2*(uniformPolynomialMomentBound β (momentDrift0 F)+uniformPolynomialMomentBound β (momentDrift1 F))
  apply MemLp.of_bound ((hm b).sub (hm a) |>.sub hi).aestronglyMeasurable
    (2*uniformPolynomialMomentBound β F+D*|(b:ℝ)-a|)
  exact .of_forall fun ω => by
    dsimp only [Pi.sub_apply]
    have hg := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (a:ℝ)) (b := (b:ℝ)) (C := D)
      (fun t _ => norm_selectedPolynomialDrift_le β hβ μ F t ω)
    have h1 := norm_selectedPolynomialProcess_le β hβ μ F b ω
    have h0 := norm_selectedPolynomialProcess_le β hβ μ F a ω
    have hn := (norm_sub_le
      (selectedPolynomialProcess β hβ μ F b ω-selectedPolynomialProcess β hβ μ F a ω)
      (∫t in (a:ℝ)..(b:ℝ),selectedPolynomialDrift β hβ μ F t ω)).trans
      (add_le_add (norm_sub_le (selectedPolynomialProcess β hβ μ F b ω)
        (selectedPolynomialProcess β hβ μ F a ω)) le_rfl)
    exact hn.trans (by linarith)

end FRSB
