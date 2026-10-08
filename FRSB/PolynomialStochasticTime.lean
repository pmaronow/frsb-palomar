module

public import FRSB.PolynomialStochasticInterval
public import FRSB.StochasticFinitePasting

@[expose] public section

/-! Actual stochastic polynomial equations at every physical time. Finite
Brownian sums on closed, clipped CDF cells are pasted through all atoms. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus Paper
open scoped Topology NNReal ENNReal BigOperators
namespace FRSB
open SpinGlass.Targets
set_option maxHeartbeats 600000

 def finiteTimeCellPolynomialBrownianSum (β : ℝ) (hβ : β ≠ 0) {k : ℕ}
    (s : RSBScheme k) (F : MomentPolynomial) (T : ℝ≥0) (p : ℕ)
    (refinement : ℕ → ℕ) (n : ℕ) (ω : BrownianSample) : ℝ :=
  let a := min (s.q p) (T:ℝ)
  let b := min (s.q (p+1)) (T:ℝ)
  if a < b then
    uniformAdaptedMartingaleLeftSumProcess
      (canonicalDiracShiftMartingale β (leftCellCrop a b n))
      (fun t ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s)
        (polynomialSpatialDerivative F) (leftCellCrop a b n+t) ω)
      (rightCellCrop a b n-leftCellCrop a b n) (refinement n+1)
      (rightCellCrop a b n-leftCellCrop a b n) ω
  else 0

 theorem polynomialStochasticLeftSums_at_time (β : ℝ) (hβ : β ≠ 0)
    {k : ℕ} (s : RSBScheme k) (F : MomentPolynomial) (T : ℝ≥0) (hT : T ≤ 1) :
    ∃ refinement : Fin (k+2) → ℕ → ℕ, (∀ p n, n ≤ refinement p n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (fun n ω => ∑ p : Fin (k+2),finiteTimeCellPolynomialBrownianSum β hβ s F T p (refinement p) n ω)
        atTop (fun ω => selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F T ω-
          selectedPolynomialProcess β hβ (parisiSchemeMeasure s) F 0 ω-
          ∫t in (0:ℝ)..(T:ℝ),selectedPolynomialDrift β hβ (parisiSchemeMeasure s) F t ω) := by
  classical
  let ν := parisiSchemeMeasure s
  let times : ℕ → ℝ := fun p => min (s.q p) (T:ℝ)
  let L : ℕ → BrownianSample → ℝ := fun p ω =>
    selectedPolynomialProcess β hβ ν F (times (p+1)).toNNReal ω-
    selectedPolynomialProcess β hβ ν F (times p).toNNReal ω-
    ∫t in times p..times (p+1),selectedPolynomialDrift β hβ ν F t ω
  have hex (p : Fin (k+2)) : ∃ refinement : ℕ → ℕ, (∀ n, n ≤ refinement n) ∧
      TendstoInMeasure canonicalBrownianMeasure
        (finiteTimeCellPolynomialBrownianSum β hβ s F T p refinement) atTop (L p) := by
    have hp : (p:ℕ) ≤ k+1 := by omega
    have hnonneg (i : ℕ) (hi : i ≤ k+2) : 0 ≤ times i :=
      le_min (s.q_nonneg hi) T.coe_nonneg
    have hmono : times p ≤ times (p+1) := by dsimp [times];gcongr;exact s.q_mono p hp
    by_cases hpos : times p < times (p+1)
    · have hqT : s.q p < (T:ℝ) := by
        by_contra hh
        have he : times p=(T:ℝ) := min_eq_right (le_of_not_gt hh)
        rw [he] at hpos
        exact not_lt_of_ge (min_le_right _ _) hpos
      have he : times p=s.q p := min_eq_left hqT.le
      have hq : s.q p < s.q (p+1) := by rw [he] at hpos;exact hpos.trans_le (min_le_left _ _)
      have ha : ((times p).toNNReal:ℝ)=times p := Real.coe_toNNReal _ (hnonneg p (by omega))
      have hb : ((times (p+1)).toNNReal:ℝ)=times (p+1) := Real.coe_toNNReal _ (hnonneg (p+1) (by omega))
      have hab : (times p).toNNReal < (times (p+1)).toNNReal := by
        apply NNReal.coe_lt_coe.mp
        rwa [ha,hb]
      obtain ⟨refinement,href,hconv⟩ := polynomialStochasticLeftSums_closed_interval β hβ s hp hq F
        (times p).toNNReal (times (p+1)).toNNReal (by rw [ha,he]) hab
        (by rw [hb];exact min_le_left _ _)
      refine ⟨refinement,href,?_⟩
      convert hconv using 1
      · funext n ω
        simp only [finiteTimeCellPolynomialBrownianSum,ha,hb,if_pos hpos,times]
      · funext ω
        simp only [L,ν,ha,hb]
    · have he : times (p+1)=times p := le_antisymm (le_of_not_gt hpos) hmono
      refine ⟨id,fun _ => le_rfl,?_⟩
      have hz : L p=fun _ => (0:ℝ) := by
        funext ω
        simp only [L,he,sub_self,intervalIntegral.integral_same,sub_zero]
      rw [hz]
      have hf : finiteTimeCellPolynomialBrownianSum β hβ s F T p id=fun _ _ => (0:ℝ) := by
        funext n ω
        dsimp only [finiteTimeCellPolynomialBrownianSum]
        rw [if_neg hpos]
      rw [hf]
      intro ε hε
      simp only [edist_self]
      have he0 : {ω : BrownianSample | ε ≤ (0:ℝ≥0∞)}=∅ := by
        ext ω
        simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
        exact not_le_of_gt hε
      simp only [he0,measure_empty]
      exact tendsto_const_nhds
  choose refinement href hconv using hex
  refine ⟨refinement,href,?_⟩
  have hh := tendstoInMeasure_finset_sum canonicalBrownianMeasure Finset.univ
    (fun p : Fin (k+2) => finiteTimeCellPolynomialBrownianSum β hβ s F T p (refinement p))
    (fun p : Fin (k+2) => L p) atTop (fun p _ => hconv p)
  have heq : (fun ω => ∑ p : Fin (k+2),L p ω) =ᵐ[canonicalBrownianMeasure]
      (fun ω => selectedPolynomialProcess β hβ ν F T ω-selectedPolynomialProcess β hβ ν F 0 ω-
        ∫t in (0:ℝ)..(T:ℝ),selectedPolynomialDrift β hβ ν F t ω) := .of_forall fun ω => by
    dsimp only
    rw [Fin.sum_univ_eq_sum_range (fun p => L p ω) (k+2)]
    have htel := finite_interval_remainder_telescope
      (fun t => selectedPolynomialProcess β hβ ν F t.toNNReal ω) times
      (fun t => selectedPolynomialDrift β hβ ν F t ω) (k+2)
      (fun p _ => selectedPolynomialDrift_intervalIntegrable β hβ ν F ω _ _)
    have h0 : times 0=0 := by simp only [times,s.q_zero,min_eq_left T.coe_nonneg]
    have h1 : times (k+2)=(T:ℝ) := by simp only [times,s.q_top,min_eq_right (show (T:ℝ)≤1 by exact_mod_cast hT)]
    simpa only [L,h0,h1,Real.toNNReal_zero,Real.toNNReal_coe] using htel
  exact TendstoInMeasure.congr_right heq hh

end FRSB
