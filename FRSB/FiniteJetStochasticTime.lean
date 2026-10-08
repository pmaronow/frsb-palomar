module

public import FRSB.FiniteJetStochasticPasting
public import FRSB.PolynomialStochasticTime
public import FRSB.PolynomialStochasticIntegrability

@[expose] public section

/-! Equation (2.17) at every physical time, with actual uncapped jet
coefficients and drift, Brownian sums pasted across atoms, and square
integrability of both the coefficient and represented stochastic remainder. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper MvPolynomial
open scoped Topology NNReal ENNReal BigOperators
namespace FRSB
open SpinGlass.Targets

 theorem finiteTimeCellPolynomialBrownianSum_X (β : ℝ) (hβ : β ≠ 0) {k : ℕ}
    (s : RSBScheme k) (j : ℕ) (T : ℝ≥0) (p : ℕ) (refinement : ℕ → ℕ)
    (n : ℕ) (ω : BrownianSample) :
    finiteTimeCellPolynomialBrownianSum β hβ s (MvPolynomial.X j) T p refinement n ω =
      let a := min (s.q p) (T:ℝ)
      let b := min (s.q (p+1)) (T:ℝ)
      if a < b then uniformAdaptedMartingaleLeftSumProcess
        (canonicalDiracShiftMartingale β (leftCellCrop a b n))
        (fun t ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+2) (leftCellCrop a b n+t) ω)
        (rightCellCrop a b n-leftCellCrop a b n) (refinement n+1)
        (rightCellCrop a b n-leftCellCrop a b n) ω else 0 := by
  simp only [finiteTimeCellPolynomialBrownianSum,polynomialSpatialDerivative_X,selectedPolynomialProcess_X]

 theorem finiteJetStochasticLeftSums_at_time (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) (j : ℕ) (T : ℝ≥0) (hT : T ≤ 1) :
    ∃ refinement : Fin (k+2) → ℕ → ℕ, (∀ p n, n ≤ refinement p n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (fun n ω => ∑ p : Fin (k+2),finiteTimeCellPolynomialBrownianSum β hβ s (MvPolynomial.X j)
          T p (refinement p) n ω) atTop
        (fun ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+1) T ω-
          selectedJetProcess β hβ (parisiSchemeMeasure s) (j+1) 0 ω-
          ∫t in (0:ℝ)..(T:ℝ),-(β^2*parisiCDF (parisiSchemeMeasure s) t/2)*
            ∑ i ∈ Finset.Icc 1 j,((j+1).choose i : ℝ)*
              parisiSpatialJet β (parisiSchemeMeasure s) (i+1) t
                (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)*
              parisiSpatialJet β (parisiSchemeMeasure s) (j+1-i+1) t
                (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)) := by
  simpa only [selectedPolynomialProcess_X,selectedPolynomialDrift_X] using
    polynomialStochasticLeftSums_at_time β hβ s (MvPolynomial.X j) T hT

 theorem memLp_finiteJetBrownianCoefficient (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (j : ℕ) (T : ℝ≥0) :
    MemLp (fun p : ℝ×BrownianSample => parisiSpatialJet β μ (j+2) p.1
      (selectedParisiItoState β 0 hβ μ p.1.toNNReal p.2)) 2
      ((volume.restrict (Icc (0:ℝ) (T:ℝ))).prod canonicalBrownianMeasure) := by
  simpa only [polynomialSpatialDerivative_X,polynomialJetField,eval_X,
    show j+1+1=j+2 by omega] using
      memLp_selectedPolynomialBrownianCoefficient β hβ μ (MvPolynomial.X j) T

 theorem memLp_finiteJetStochasticRemainder (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (j : ℕ) (T : ℝ≥0) :
    MemLp (fun ω => selectedJetProcess β hβ μ (j+1) T ω-selectedJetProcess β hβ μ (j+1) 0 ω-
      ∫t in (0:ℝ)..(T:ℝ),-(β^2*parisiCDF μ t/2)*
        ∑ i ∈ Finset.Icc 1 j,((j+1).choose i : ℝ)*
          parisiSpatialJet β μ (i+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)*
          parisiSpatialJet β μ (j+1-i+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω))
      2 canonicalBrownianMeasure := by
  convert memLp_polynomialItoRemainder β hβ μ (MvPolynomial.X j) 0 T using 1
  funext ω
  simp only [polynomialItoRemainder,selectedPolynomialProcess_X,selectedPolynomialDrift_X,NNReal.coe_zero]

end FRSB
