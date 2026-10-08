module

public import FRSB.PolynomialStochasticCells
public import FRSB.StochasticCrops

@[expose] public section

/-! Actual closed-cell stochastic polynomial identities. The Brownian
Riemann sums come from strictly interior crops and refining actual partitions;
continuity closes the endpoints, including CDF atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace FRSB
open SpinGlass.Targets
set_option maxHeartbeats 500000

 def selectedPolynomialProcess (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (F : MomentPolynomial) (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  polynomialJetField β μ F t (selectedParisiItoState β 0 hβ μ t ω)

 def selectedPolynomialDrift (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (F : MomentPolynomial) (t : ℝ) (ω : BrownianSample) : ℝ := β^2*(
      polynomialJetField β μ (momentDrift0 F) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)+
      parisiCDF μ t*polynomialJetField β μ (momentDrift1 F) t
        (selectedParisiItoState β 0 hβ μ t.toNNReal ω))

 theorem continuous_selectedPolynomialProcess (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (ω : BrownianSample) :
    Continuous (fun t => selectedPolynomialProcess β hβ μ F t ω) := by
  unfold selectedPolynomialProcess
  have hm : Continuous (fun t : ℝ≥0 => ((t:ℝ),selectedParisiItoState β 0 hβ μ t ω)) :=
    NNReal.continuous_coe.prodMk ((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).continuous_state ω)
  convert (continuous_polynomialJetField β μ F).comp hm using 1
  rfl

 theorem measurable_selectedPolynomialDrift (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) :
    Measurable (Function.uncurry (selectedPolynomialDrift β hβ μ F)) := by
  have hNN : Measurable (Function.uncurry (selectedParisiItoState β 0 hβ μ)) := by
    apply measurable_uncurry_of_continuous_of_measurable
      (boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).continuous_state
    intro t
    exact (((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ μ).adapted_state t).measurable).mono
      (canonicalBrownianFiltration.le t) le_rfl
  have hX : Measurable (fun p : ℝ×BrownianSample => selectedParisiItoState β 0 hβ μ p.1.toNNReal p.2) := by
    convert hNN.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
      using 1
    rfl
  have hm (G : MomentPolynomial) : Measurable (fun p : ℝ×BrownianSample =>
      polynomialJetField β μ G p.1 (selectedParisiItoState β 0 hβ μ p.1.toNNReal p.2)) := by
    convert (continuous_polynomialJetField β μ G).measurable.comp (measurable_fst.prodMk hX) using 1
    rfl
  unfold selectedPolynomialDrift Function.uncurry
  exact measurable_const.mul ((hm _).add
    (((parisiCDF_monotone μ).measurable.comp measurable_fst).mul (hm _)))

 theorem norm_selectedPolynomialDrift_le (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (t : ℝ) (ω : BrownianSample) :
    ‖selectedPolynomialDrift β hβ μ F t ω‖ ≤ β^2*(
      uniformPolynomialMomentBound β (momentDrift0 F)+uniformPolynomialMomentBound β (momentDrift1 F)) := by
  unfold selectedPolynomialDrift
  rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
  apply (norm_add_le _ _).trans
  apply add_le_add (norm_polynomialJetField_le_uniform β μ _ _ _)
  rw [norm_mul,Real.norm_of_nonneg (parisiCDF_nonneg μ t)]
  exact (mul_le_mul (parisiCDF_le_one μ t) (norm_polynomialJetField_le_uniform β μ _ _ _)
    (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

 theorem selectedPolynomialDrift_intervalIntegrable (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (ω : BrownianSample) (a b : ℝ) :
    IntervalIntegrable (fun t => selectedPolynomialDrift β hβ μ F t ω) volume a b := by
  apply IntegrableOn.intervalIntegrable
  apply (integrableOn_const isCompact_uIcc.measure_ne_top
    (C := β^2*(uniformPolynomialMomentBound β (momentDrift0 F)+uniformPolynomialMomentBound β (momentDrift1 F)))).mono'
  · exact ((measurable_selectedPolynomialDrift β hβ μ F).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  · exact .of_forall fun t => norm_selectedPolynomialDrift_le β hβ μ F t ω

 theorem stronglyMeasurable_selectedPolynomialDrift_integral (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (F : MomentPolynomial) (a b : ℝ) :
    StronglyMeasurable (fun ω => ∫t in a..b,selectedPolynomialDrift β hβ μ F t ω) := by
  unfold intervalIntegral
  exact ((measurable_selectedPolynomialDrift β hβ μ F).stronglyMeasurable.integral_prod_left).sub
    ((measurable_selectedPolynomialDrift β hβ μ F).stronglyMeasurable.integral_prod_left)

 theorem polynomialStochasticLeftSums_closed_cell (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p≤k+1) (hq : s.q p<s.q (p+1))
    (F : MomentPolynomial) :
    ∃ refinement : ℕ → ℕ, (∀ n, n ≤ refinement n) ∧ TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess
        (canonicalDiracShiftMartingale β (leftCellCrop (s.q p) (s.q (p+1)) n))
        (fun t ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s)
          (polynomialSpatialDerivative F) (leftCellCrop (s.q p) (s.q (p+1)) n+t) ω)
        (rightCellCrop (s.q p) (s.q (p+1)) n-leftCellCrop (s.q p) (s.q (p+1)) n)
        (refinement n+1)
        (rightCellCrop (s.q p) (s.q (p+1)) n-leftCellCrop (s.q p) (s.q (p+1)) n)) atTop
      (fun ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F (s.q (p+1)).toNNReal ω-
        selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F (s.q p).toNNReal ω-
        ∫t in s.q p..s.q (p+1), selectedPolynomialDrift β hβ (parisiSchemeMeasure s) F t ω) := by
  let ν := parisiSchemeMeasure s
  let a := s.q p
  let b := s.q (p+1)
  let L := leftCellCrop a b
  let R := rightCellCrop a b
  let B : ℕ → BrownianSample → ℝ := fun n ω => selectedPolynomialProcess β hβ ν F (R n) ω-
    selectedPolynomialProcess β hβ ν F (L n) ω-
    ∫t in (L n:ℝ)..(R n:ℝ), selectedPolynomialDrift β hβ ν F t ω
  let A : ℕ → ℕ → BrownianSample → ℝ := fun n m ω =>
    uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β (L n))
      (fun t ω => selectedPolynomialProcess β hβ ν (polynomialSpatialDerivative F) (L n+t) ω)
      (R n-L n) (m+1) (R n-L n) ω
  have ha : 0≤a := s.q_nonneg (by omega)
  have hcrop (n : ℕ) := cellCrop_bounds ha hq n
  have hL := tendsto_leftCellCrop ha hq
  have hR := tendsto_rightCellCrop ha hq
  have hB : TendstoInMeasure canonicalBrownianMeasure B atTop
      (fun ω => selectedPolynomialProcess β hβ ν F b.toNNReal ω-
        selectedPolynomialProcess β hβ ν F a.toNNReal ω-
        ∫t in a..b,selectedPolynomialDrift β hβ ν F t ω) := by
    apply tendstoInMeasure_of_tendsto_ae
    · intro n
      have hpmeas (t : ℝ≥0) : StronglyMeasurable (selectedPolynomialProcess β hβ ν F t) := by
        unfold selectedPolynomialProcess
        have hf : Continuous (fun x : ℝ => polynomialJetField β ν F (t:ℝ) x) := by
          convert (continuous_polynomialJetField β ν F).comp
            (continuous_const.prodMk continuous_id) using 1
          rfl
        convert hf.comp_stronglyMeasurable
          (((boundedDriftItoCharacteristics_selectedParisiState β 0 hβ ν).adapted_state t).mono
            (canonicalBrownianFiltration.le t)) using 1
      exact ((hpmeas _).sub (hpmeas _)).sub
        (stronglyMeasurable_selectedPolynomialDrift_integral β hβ ν F _ _) |>.aestronglyMeasurable
    · exact .of_forall fun ω => by
        have hpcont := continuous_selectedPolynomialProcess β hβ ν F ω
        have hprim := intervalIntegral.continuous_primitive
          (selectedPolynomialDrift_intervalIntegrable β hβ ν F ω) (0:ℝ)
        have hLc : Tendsto (fun n => (L n:ℝ)) atTop (nhds a) := by
          simpa only [L,Function.comp_def,Real.coe_toNNReal _ ha] using NNReal.continuous_coe.tendsto a.toNNReal |>.comp hL
        have hRc : Tendsto (fun n => (R n:ℝ)) atTop (nhds b) := by
          simpa only [R,b,Function.comp_def,Real.coe_toNNReal _ (ha.trans hq.le)] using NNReal.continuous_coe.tendsto b.toNNReal |>.comp hR
        have hint := (hprim.tendsto b |>.comp hRc).sub (hprim.tendsto a |>.comp hLc)
        dsimp only [Function.comp_def] at hint
        simp only [intervalIntegral.integral_interval_sub_left
          (selectedPolynomialDrift_intervalIntegrable β hβ ν F ω 0 _)
          (selectedPolynomialDrift_intervalIntegrable β hβ ν F ω 0 _)] at hint
        convert ((hpcont.tendsto _ |>.comp hR).sub (hpcont.tendsto _ |>.comp hL)).sub hint using 1
        rfl
  have hA (n : ℕ) : TendstoInMeasure canonicalBrownianMeasure (A n) atTop (B n) := by
    have hh := polynomialStochasticLeftSums_finite_cell β hβ s hp hq F (L n) (R n)
      (hcrop n).1 (hcrop n).2.1 (hcrop n).2.2
    convert hh using 1
    · funext m ω
      simp only [A,selectedPolynomialProcess,NNReal.coe_add,ν]
    · rfl
  have hh := exists_diagonal_tendstoInMeasure hA hB
  convert hh using 1

end FRSB
