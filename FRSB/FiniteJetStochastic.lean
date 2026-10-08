module

public import FRSB.PolynomialStochasticCells

@[expose] public section

/-! Literal positive-order jet stochastic identities for actual finite Parisi
measures between atoms. Variable index `j` is the spatial derivative `j+1`. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper MvPolynomial
open scoped Topology NNReal BigOperators
namespace FRSB
open SpinGlass.Targets

@[simp] theorem polynomialSpatialDerivative_X (j : ℕ) :
    polynomialSpatialDerivative (MvPolynomial.X j)=MvPolynomial.X (j+1) := by
  simp [polynomialSpatialDerivative,polynomialDirection]

@[simp] theorem momentDrift0_X (j : ℕ) : momentDrift0 (MvPolynomial.X j)=0 := by
  classical
  simp [momentDrift0]

@[simp] theorem momentDrift1_X (j : ℕ) : momentDrift1 (MvPolynomial.X j)=
    MvPolynomial.C (-1/2 : ℝ)*nonlinearJetPolynomial j := by
  classical
  simp [momentDrift1,nonlinearJetPolynomial]

 def selectedJetProcess (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure) (j : ℕ)
    (t : ℝ≥0) (ω : BrownianSample) : ℝ :=
  parisiSpatialJet β μ j t (selectedParisiItoState β 0 hβ μ t ω)

 theorem selectedJetProcess_eq_physical (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (j : ℕ) (t : ℝ≥0) (ht : t ≤ 1) (ω : BrownianSample) :
    selectedJetProcess β hβ μ j t ω=jetProcess β μ j t ω := by
  unfold selectedJetProcess jetProcess
  rw [selectedParisiItoState_eq β 0 hβ μ ht]
  rfl

 theorem finiteJetStochasticLeftSums (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) (j : ℕ) (l r : ℝ≥0)
    (hl : s.q p < (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) < s.q (p+1)) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+2) (l+t) ω)
        (r-l) (n+1) (r-l)) atTop
      (fun ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+1) r ω-
        selectedJetProcess β hβ (parisiSchemeMeasure s) (j+1) l ω-
        ∫t in (l : ℝ)..(r : ℝ),-(β^2*parisiCDF (parisiSchemeMeasure s) t/2)*
          ∑ i ∈ Finset.Icc 1 j,((j+1).choose i : ℝ)*
            parisiSpatialJet β (parisiSchemeMeasure s) (i+1) t
              (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)*
            parisiSpatialJet β (parisiSchemeMeasure s) (j+1-i+1) t
              (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) t.toNNReal ω)) := by
  have hh := polynomialStochasticLeftSums_finite_cell β hβ s hp hq (MvPolynomial.X j) l r hl hlr hr
  simp only [polynomialSpatialDerivative_X,momentDrift0_X,momentDrift1_X,
    polynomialJetField,eval_X,map_zero,zero_add,map_mul,eval_C] at hh
  have hleft (n : ℕ) : (fun ω => uniformAdaptedMartingaleLeftSumProcess
      (canonicalDiracShiftMartingale β l)
      (fun t ω => parisiSpatialJet β (parisiSchemeMeasure s) (j+1+1) ((l : ℝ)+t)
        (selectedParisiItoState β 0 hβ (parisiSchemeMeasure s) (l+t) ω))
      (r-l) (n+1) (r-l) ω) =
      (fun ω => uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t ω => selectedJetProcess β hβ (parisiSchemeMeasure s) (j+2) (l+t) ω)
        (r-l) (n+1) (r-l) ω) := by
    simp only [selectedJetProcess,NNReal.coe_add,show j+1+1=j+2 by omega]
  have hh' := hh.congr_left (fun n => .of_forall (congrFun (hleft n)))
  apply TendstoInMeasure.congr_right _ hh'
  exact .of_forall fun ω => by
    dsimp only [selectedJetProcess]
    congr 1
    apply intervalIntegral.integral_congr
    intro t _
    simp only [nonlinearJetPolynomial,map_sum,map_mul,eval_C,eval_X]
    ring

/-- On a finite cell the actual gradient has zero drift and Brownian
coefficient equal to the actual Hessian. -/
 theorem finiteGradientStochasticLeftSums (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) {p : ℕ} (hp : p ≤ k+1)
    (hq : s.q p < s.q (p+1)) (l r : ℝ≥0)
    (hl : s.q p < (l : ℝ)) (hlr : l ≤ r) (hr : (r : ℝ) < s.q (p+1)) :
    TendstoInMeasure canonicalBrownianMeasure
      (fun n => uniformAdaptedMartingaleLeftSumProcess (canonicalDiracShiftMartingale β l)
        (fun t ω => selectedJetProcess β hβ (parisiSchemeMeasure s) 2 (l+t) ω)
        (r-l) (n+1) (r-l)) atTop
      (fun ω => selectedJetProcess β hβ (parisiSchemeMeasure s) 1 r ω-
        selectedJetProcess β hβ (parisiSchemeMeasure s) 1 l ω) := by
  simpa only [zero_add,Finset.Icc_eq_empty_of_lt (by norm_num : (0 : ℕ)<1),
    Finset.sum_empty,mul_zero,intervalIntegral.integral_zero,sub_zero] using
      finiteJetStochasticLeftSums β hβ s hp hq 0 l r hl hlr hr

end FRSB
