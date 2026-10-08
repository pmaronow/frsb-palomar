module

public import FRSB.PolynomialStochasticEndpoints

@[expose] public section

/-! Closed stochastic polynomial identities on arbitrary nonempty subintervals
of a finite Parisi cell, including either atomic boundary. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal ENNReal
namespace FRSB
open SpinGlass.Targets
set_option maxHeartbeats 500000

 theorem polynomialStochasticLeftSums_closed_interval (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p≤k+1) (hq : s.q p<s.q (p+1))
    (F : MomentPolynomial) (a0 b0 : ℝ≥0)
    (hal : s.q p ≤ (a0:ℝ)) (hab0 : a0 < b0) (hbr : (b0:ℝ) ≤ s.q (p+1)) :
    ∃ refinement : ℕ → ℕ, (∀ n, n ≤ refinement n) ∧ TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess
        (canonicalDiracShiftMartingale β (leftCellCrop (a0:ℝ) (b0:ℝ) n))
        (fun t ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s)
          (polynomialSpatialDerivative F) (leftCellCrop (a0:ℝ) (b0:ℝ) n+t) ω)
        (rightCellCrop (a0:ℝ) (b0:ℝ) n-leftCellCrop (a0:ℝ) (b0:ℝ) n)
        (refinement n+1)
        (rightCellCrop (a0:ℝ) (b0:ℝ) n-leftCellCrop (a0:ℝ) (b0:ℝ) n)) atTop
      (fun ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F b0 ω-
        selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F a0 ω-
        ∫t in (a0:ℝ)..(b0:ℝ), selectedPolynomialDrift β hβ (parisiSchemeMeasure s) F t ω) := by
  let ν := parisiSchemeMeasure s
  let a : ℝ := a0
  let b : ℝ := b0
  let L := leftCellCrop a b
  let R := rightCellCrop a b
  let B : ℕ → BrownianSample → ℝ := fun n ω => selectedPolynomialProcess β hβ ν F (R n) ω-
    selectedPolynomialProcess β hβ ν F (L n) ω-
    ∫t in (L n:ℝ)..(R n:ℝ), selectedPolynomialDrift β hβ ν F t ω
  let A : ℕ → ℕ → BrownianSample → ℝ := fun n m ω =>
    uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β (L n))
      (fun t ω => selectedPolynomialProcess β hβ ν (polynomialSpatialDerivative F) (L n+t) ω)
      (R n-L n) (m+1) (R n-L n) ω
  have ha : 0≤a := a0.coe_nonneg
  have hab : a<b := by exact_mod_cast hab0
  have hcrop (n : ℕ) := cellCrop_bounds ha hab n
  have hL := tendsto_leftCellCrop ha hab
  have hR := tendsto_rightCellCrop ha hab
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
          simpa only [R,b,Function.comp_def,Real.coe_toNNReal _ (ha.trans hab.le)] using NNReal.continuous_coe.tendsto b.toNNReal |>.comp hR
        have hint := (hprim.tendsto b |>.comp hRc).sub (hprim.tendsto a |>.comp hLc)
        dsimp only [Function.comp_def] at hint
        simp only [intervalIntegral.integral_interval_sub_left
          (selectedPolynomialDrift_intervalIntegrable β hβ ν F ω 0 _)
          (selectedPolynomialDrift_intervalIntegrable β hβ ν F ω 0 _)] at hint
        convert ((hpcont.tendsto _ |>.comp hR).sub (hpcont.tendsto _ |>.comp hL)).sub hint using 1
        rfl
  have hA (n : ℕ) : TendstoInMeasure canonicalBrownianMeasure (A n) atTop (B n) := by
    have hh := polynomialStochasticLeftSums_finite_cell β hβ s hp hq F (L n) (R n)
      (hal.trans_lt (hcrop n).1) (hcrop n).2.1 ((hcrop n).2.2.trans_le hbr)
    convert hh using 1
    · funext m ω
      simp only [A,selectedPolynomialProcess,NNReal.coe_add,ν]
    · rfl
  have hh := exists_diagonal_tendstoInMeasure hA hB
  convert hh using 1
  all_goals simp only [A,B,L,R,a,b,ν,Real.toNNReal_coe]

end FRSB
