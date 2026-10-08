module

public import FRSB.FiniteForwardLaw

@[expose] public section

/-! Telescoping the literal finite transition-density product into overlap
atom weights. In particular, atoms at zero are retained. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper SpinGlass.Targets
open scoped NNReal ENNReal Topology
namespace FRSB

theorem historySplit_sample {Ω : Type*} (X : ℝ≥0 → Ω → ℝ) (T : ℕ → ℝ≥0)
    (n : ℕ) (sample : Ω) :
    historySplit n (historySample X T (n+1) sample) =
      (historySample X T n sample,X (T (n+1)) sample) := rfl

theorem finite_weighted_difference_telescope (m F : ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range (n+1),m i*(F (i+1)-F i)) =
      m n*F (n+1)-m 0*F 0-
        ∑ i ∈ Finset.range n,(m (i+1)-m i)*F (i+1) := by
  induction n with
  | zero => simp;ring
  | succ n ih =>
    rw [Finset.sum_range_succ,ih,Finset.sum_range_succ]
    ring

theorem finiteHistoryDensity_forwardScheme_sample {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (t : ℝ≥0) (X : ℝ≥0 → ℝ) (n : ℕ) :
    finiteHistoryDensity (forwardSchemeWeight s β t) n
      (fun i => X (forwardSchemeTime s t i)) = ENNReal.ofReal (Real.exp
        (∑ j ∈ Finset.range n, forwardSchemeMass s j *
          (parisiPotential β (parisiSchemeMeasure s)
            (forwardSchemeTime s t (j+1),X (forwardSchemeTime s t (j+1))) -
           parisiPotential β (parisiSchemeMeasure s)
            (forwardSchemeTime s t j,X (forwardSchemeTime s t j))))) := by
  induction n with
  | zero => simp [finiteHistoryDensity]
  | succ n ih =>
    change finiteHistoryDensity (forwardSchemeWeight s β t) n
      (fun i => X (forwardSchemeTime s t i)) *
      forwardSchemeWeight s β t n (X (forwardSchemeTime s t n))
        (X (forwardSchemeTime s t (n+1))) = _
    rw [ih,Finset.sum_range_succ,Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
    rfl

theorem forwardScheme_exponent_telescope {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (X : ℝ≥0 → ℝ) :
    (∑ j ∈ Finset.range (k+2), forwardSchemeMass s j *
      (parisiPotential β (parisiSchemeMeasure s)
        (forwardSchemeTime s t (j+1),X (forwardSchemeTime s t (j+1))) -
       parisiPotential β (parisiSchemeMeasure s)
        (forwardSchemeTime s t j,X (forwardSchemeTime s t j)))) =
    parisiPotential β (parisiSchemeMeasure s) (t,X t) -
      ∑ i ∈ Finset.range (k+1), (s.m (i+1)-s.m i)*
        parisiPotential β (parisiSchemeMeasure s)
          (forwardSchemeTime s t (i+1),X (forwardSchemeTime s t (i+1))) := by
  have he := finite_weighted_difference_telescope (forwardSchemeMass s)
    (fun j => parisiPotential β (parisiSchemeMeasure s)
      (forwardSchemeTime s t j,X (forwardSchemeTime s t j))) (k+1)
  rw [show k+1+1 = k+2 by omega] at he
  rw [show forwardSchemeMass s (k+1) = 1 by simp [forwardSchemeMass,s.m_top],
    show forwardSchemeMass s 0 = 0 by simp [forwardSchemeMass,s.m_zero],
    forwardSchemeTime_top s t ht le_rfl] at he
  simp only [one_mul,zero_mul,sub_zero] at he
  rw [he]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i+1 ≤ k+1 := by have := Finset.mem_range.mp hi;omega
  simp only [forwardSchemeMass,min_eq_left hi',min_eq_left (by omega : i ≤ k+1)]


/-- The complete stopped-path density is a terminal potential minus every
scheme atom contribution, including an atom at the initial time. -/
theorem finiteHistoryDensity_forwardScheme_terminal {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (X : ℝ≥0 → ℝ) :
    finiteHistoryDensity (forwardSchemeWeight s β t) (k+2)
      (fun i => X (forwardSchemeTime s t i)) =
    ENNReal.ofReal (Real.exp (parisiPotential β (parisiSchemeMeasure s) (t,X t) -
      ∑ i ∈ Finset.range (k+1),(s.m (i+1)-s.m i)*
        parisiPotential β (parisiSchemeMeasure s)
          (forwardSchemeTime s t (i+1),X (forwardSchemeTime s t (i+1))))) := by
  rw [finiteHistoryDensity_forwardScheme_sample,forwardScheme_exponent_telescope s β t ht X]

end FRSB
