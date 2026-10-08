module

public import FRSB.PolynomialStochasticPasting
public import FRSB.FiniteJetStochastic

@[expose] public section

/-! Literal finite-jet stochastic equations with genuine Brownian partitions
pasted across every atom, as well as each open cell. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper MvPolynomial
open scoped Topology NNReal ENNReal BigOperators
namespace FRSB
open SpinGlass.Targets

@[simp] theorem selectedPolynomialProcess_X (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ≥0) (ω : BrownianSample) :
    selectedPolynomialProcess β hβ μ (MvPolynomial.X j) t ω=selectedJetProcess β hβ μ (j+1) t ω := by
  simp only [selectedPolynomialProcess,selectedJetProcess,polynomialJetField,eval_X]

 theorem selectedPolynomialDrift_X (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ) (ω : BrownianSample) :
    selectedPolynomialDrift β hβ μ (MvPolynomial.X j) t ω =
      -(β^2*parisiCDF μ t/2)*∑ i ∈ Finset.Icc 1 j,((j+1).choose i : ℝ)*
        parisiSpatialJet β μ (i+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω)*
        parisiSpatialJet β μ (j+1-i+1) t (selectedParisiItoState β 0 hβ μ t.toNNReal ω) := by
  simp only [selectedPolynomialDrift,momentDrift0_X,momentDrift1_X,polynomialJetField,
    map_zero,map_mul,eval_C,zero_add,nonlinearJetPolynomial,map_sum,map_mul,eval_C,eval_X]
  ring

 theorem finiteCellPolynomialBrownianSum_X (β : ℝ) (hβ : β ≠ 0) {k : ℕ}
    (s : RSBScheme k) (j p : ℕ) (refinement : ℕ → ℕ) (n : ℕ) (ω : BrownianSample) :
    finiteCellPolynomialBrownianSum β hβ s (MvPolynomial.X j) p refinement n ω =
      if s.q p<s.q (p+1) then uniformAdaptedMartingaleLeftSumProcess
        (canonicalDiracShiftMartingale β (leftCellCrop (s.q p) (s.q (p+1)) n))
        (fun t ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+2)
          (leftCellCrop (s.q p) (s.q (p+1)) n+t) ω)
        (rightCellCrop (s.q p) (s.q (p+1)) n-leftCellCrop (s.q p) (s.q (p+1)) n)
        (refinement n+1)
        (rightCellCrop (s.q p) (s.q (p+1)) n-leftCellCrop (s.q p) (s.q (p+1)) n) ω else 0 := by
  simp only [finiteCellPolynomialBrownianSum,polynomialSpatialDerivative_X,selectedPolynomialProcess_X]

 theorem finiteJetStochasticLeftSums_across_atoms (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) (j : ℕ) :
    ∃ refinement : Fin (k+2) → ℕ → ℕ, (∀ p n,n≤refinement p n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (fun n ω => ∑ p : Fin (k+2),finiteCellPolynomialBrownianSum β hβ s (MvPolynomial.X j)
          p (refinement p) n ω) atTop
        (fun ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+1) 1 ω-
          selectedJetProcess β hβ (parisiSchemeMeasure s) (j+1) 0 ω-
          ∫t in (0:ℝ)..1,-(β^2*parisiCDF (parisiSchemeMeasure s) t/2)*
            ∑ i ∈ Finset.Icc 1 j,((j+1).choose i : ℝ)*
              parisiSpatialJet β (parisiSchemeMeasure s) (i+1) t
                (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)*
              parisiSpatialJet β (parisiSchemeMeasure s) (j+1-i+1) t
                (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)) := by
  simpa only [selectedPolynomialProcess_X,selectedPolynomialDrift_X] using
    polynomialStochasticLeftSums_across_atoms β hβ s (MvPolynomial.X j)

end FRSB
