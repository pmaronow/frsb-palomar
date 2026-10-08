module

public import FRSB.PolynomialStochasticEndpoints
public import FRSB.StochasticFinitePasting

@[expose] public section

/-! Genuine finite-pasting of Brownian stochastic polynomial identities across
all CDF atoms. Degenerate scheme cells contribute zero. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal ENNReal BigOperators
namespace FRSB
open SpinGlass.Targets
set_option maxHeartbeats 600000

 def finiteCellPolynomialBrownianSum (β : ℝ) (hβ : β ≠ 0) {k : ℕ}
    (s : RSBScheme k) (F : MomentPolynomial) (p : ℕ) (refinement : ℕ → ℕ)
    (n : ℕ) (ω : BrownianSample) : ℝ :=
  if s.q p<s.q (p+1) then
    uniformAdaptedMartingaleLeftSumProcess
      (canonicalDiracShiftMartingale β (leftCellCrop (s.q p) (s.q (p+1)) n))
      (fun t ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s)
        (polynomialSpatialDerivative F) (leftCellCrop (s.q p) (s.q (p+1)) n+t) ω)
      (rightCellCrop (s.q p) (s.q (p+1)) n-leftCellCrop (s.q p) (s.q (p+1)) n)
      (refinement n+1)
      (rightCellCrop (s.q p) (s.q (p+1)) n-leftCellCrop (s.q p) (s.q (p+1)) n) ω
  else 0

 theorem polynomialStochasticLeftSums_across_atoms (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) (F : MomentPolynomial) :
    ∃ refinement : Fin (k+2) → ℕ → ℕ, (∀ p n, n≤refinement p n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (fun n ω => ∑ p : Fin (k+2),finiteCellPolynomialBrownianSum β hβ s F p (refinement p) n ω)
        atTop (fun ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F 1 ω-
          selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F 0 ω-
          ∫t in (0:ℝ)..1,selectedPolynomialDrift β hβ (parisiSchemeMeasure s) F t ω) := by
  classical
  let ν := parisiSchemeMeasure s
  let L := fun p ω => selectedPolynomialProcess β hβ ν F (s.q (p+1)).toNNReal ω-
    selectedPolynomialProcess β hβ ν F (s.q p).toNNReal ω-
    ∫t in s.q p..s.q (p+1),selectedPolynomialDrift β hβ ν F t ω
  have hex (p : Fin (k+2)) : ∃ refinement : ℕ → ℕ, (∀ n,n≤refinement n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (finiteCellPolynomialBrownianSum β hβ s F p refinement) atTop (L p) := by
    have hp : (p:ℕ)≤k+1 := by omega
    by_cases hq : s.q p<s.q (p+1)
    · obtain ⟨refinement,href,hconv⟩ := polynomialStochasticLeftSums_closed_cell β hβ s hp hq F
      refine ⟨refinement,href,?_⟩
      convert hconv using 1
      funext n ω
      simp only [finiteCellPolynomialBrownianSum,if_pos hq]
    · have he : s.q (p+1)=s.q p := le_antisymm (le_of_not_gt hq) (s.q_mono p hp)
      refine ⟨id,fun _ => le_rfl,?_⟩
      have hz : (L p)=fun _ => (0:ℝ) := by
        funext ω
        simp only [L,he,sub_self,intervalIntegral.integral_same,sub_zero]
      rw [hz]
      intro ε hε
      simp only [finiteCellPolynomialBrownianSum,if_neg hq,edist_self]
      have he0 : {ω : BrownianSample | ε≤(0:ℝ≥0∞)}=∅ := by
        ext ω
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        exact not_le_of_gt hε
      simp only [he0,measure_empty]
      exact tendsto_const_nhds
  choose refinement href hconv using hex
  refine ⟨refinement,href,?_⟩
  have hh := tendstoInMeasure_finset_sum canonicalBrownianMeasure Finset.univ
    (fun p : Fin (k+2) => finiteCellPolynomialBrownianSum β hβ s F p (refinement p))
    (fun p : Fin (k+2) => L p) atTop (fun p _ => hconv p)
  have heq : (fun ω => ∑ p : Fin (k+2),L p ω) =ᵐ[canonicalBrownianMeasure]
      (fun ω => selectedPolynomialProcess β hβ ν F 1 ω-selectedPolynomialProcess β hβ ν F 0 ω-
        ∫t in (0:ℝ)..1,selectedPolynomialDrift β hβ ν F t ω) := .of_forall fun ω => by
    dsimp only
    rw [Fin.sum_univ_eq_sum_range (fun p => L p ω) (k+2)]
    have htel := finite_interval_remainder_telescope
      (fun t => selectedPolynomialProcess β hβ ν F t.toNNReal ω) s.q
      (fun t => selectedPolynomialDrift β hβ ν F t ω) (k+2)
      (fun p _ => selectedPolynomialDrift_intervalIntegrable β hβ ν F ω _ _)
    simpa only [L,s.q_top,s.q_zero,Real.toNNReal_one,Real.toNNReal_zero] using htel
  exact TendstoInMeasure.congr_right heq hh

end FRSB
