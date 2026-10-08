module

public import FRSB.FiniteForwardWeight
public import Paper.ParisiCDFIntegral

@[expose] public section

/-! Literal finite overlap integrals and the stopped Brownian path action.
The initial atom is part of the actual measure integral. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper SpinGlass.Targets
open scoped NNReal ENNReal Topology
namespace FRSB

def stoppedOverlapTime (t : ℝ≥0) (q : Overlap) : ℝ≥0 :=
  ⟨min (q:ℝ) t,le_min q.property.1 t.coe_nonneg⟩

theorem forwardSchemeTime_atom {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (i : Fin (k+1)) :
    forwardSchemeTime s t (i+1) = stoppedOverlapTime t (parisiSchemeAtom s i) := by
  apply NNReal.eq
  change min (s.q (min (i+1) (k+2))) t = min (s.q (i+1)) t
  rw [min_eq_left (by have := i.isLt;omega : (i:ℕ)+1 ≤ k+2)]

theorem integrable_parisiSchemeMeasure {k : ℕ} (s : RSBScheme k) (f : Overlap → ℝ) :
    Integrable f (parisiSchemeMeasure s : Measure Overlap) := by
  change Integrable f (∑ i : Fin (k+1),ENNReal.ofReal (s.m (i+1)-s.m i) •
    Measure.dirac (parisiSchemeAtom s i))
  exact integrable_finsetSum_measure.mpr fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top

theorem integral_parisiSchemeMeasure {k : ℕ} (s : RSBScheme k) (f : Overlap → ℝ) :
    (∫q,f q ∂(parisiSchemeMeasure s : Measure Overlap)) =
      ∑ i : Fin (k+1),(s.m (i+1)-s.m i)*f (parisiSchemeAtom s i) := by
  change (∫q,f q ∂(∑ i : Fin (k+1),ENNReal.ofReal (s.m (i+1)-s.m i) •
    Measure.dirac (parisiSchemeAtom s i))) = _
  rw [integral_finsetSum_measure (fun i _ =>
    (integrable_dirac (by finiteness)).smul_measure ENNReal.ofReal_ne_top)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_smul_measure,integral_dirac,ENNReal.toReal_ofReal
    (sub_nonneg.mpr (s.m_mono i (by have := i.isLt;omega)))]
  rfl

def forwardBrownianAction (β : ℝ) (μ : ParisiMeasure) (t : ℝ≥0)
    (sample : BrownianSample) : ℝ :=
  ∫q : Overlap,if (q:ℝ) ≤ t then parisiPotential β μ
    (q,β*canonicalBrownian (q:ℝ).toNNReal sample) else 0 ∂(μ : Measure Overlap)

def forwardBrownianWeight (β : ℝ) (μ : ParisiMeasure) (t : ℝ≥0)
    (sample : BrownianSample) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (parisiCDF μ t * parisiPotential β μ
    (t,β*canonicalBrownian t sample)-forwardBrownianAction β μ t sample))

theorem finiteScheme_stopped_action_split {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (t : ℝ≥0) (X : ℝ≥0 → ℝ) :
    (∫q : Overlap,parisiPotential β (parisiSchemeMeasure s)
      (stoppedOverlapTime t q,X (stoppedOverlapTime t q)) ∂(parisiSchemeMeasure s : Measure Overlap)) =
    (∫q : Overlap,if (q:ℝ) ≤ t then parisiPotential β (parisiSchemeMeasure s)
      (q,X (q:ℝ).toNNReal) else 0 ∂(parisiSchemeMeasure s : Measure Overlap)) +
    (1-parisiCDF (parisiSchemeMeasure s) t)*parisiPotential β (parisiSchemeMeasure s) (t,X t) := by
  let μ := parisiSchemeMeasure s
  let U := parisiPotential β μ (t,X t)
  have he : (fun q : Overlap => parisiPotential β μ
      (stoppedOverlapTime t q,X (stoppedOverlapTime t q))) =
      (fun q : Overlap => (if (q:ℝ) ≤ t then parisiPotential β μ
        (q,X (q:ℝ).toNNReal) else 0) +
        (1-(if (q:ℝ) ≤ t then (1:ℝ) else 0))*U) := by
    funext q
    by_cases hqt : (q:ℝ) ≤ t
    · have htq : stoppedOverlapTime t q = (q:ℝ).toNNReal := by
        apply NNReal.eq
        change min (q:ℝ) t = _
        rw [min_eq_left hqt,Real.coe_toNNReal _ q.property.1]
      rw [htq]
      simp only [hqt,ite_true,sub_self,zero_mul,add_zero,Real.coe_toNNReal _ q.property.1]
    · have htq : stoppedOverlapTime t q = t := by
        apply NNReal.eq
        exact min_eq_right (not_le.mp hqt).le
      rw [htq]
      simp only [hqt,ite_false,sub_zero,one_mul,zero_add]
      rfl
  change (∫q : Overlap,parisiPotential β μ
      (stoppedOverlapTime t q,X (stoppedOverlapTime t q)) ∂(μ : Measure Overlap)) = _
  rw [he,integral_add (integrable_parisiSchemeMeasure s _) (integrable_parisiSchemeMeasure s _),
    integral_mul_const,integral_sub (integrable_parisiSchemeMeasure s _) (integrable_parisiSchemeMeasure s _)]
  rw [integral_const]
  have hc := parisiCDF_eq_integral_upperIndicator μ t
  rw [← hc]
  simp
  rfl

/-- Exact conversion of the finite transition product to the actual overlap
measure action, with right-continuous CDF and the initial atom intact. -/
theorem finiteHistoryDensity_eq_forwardBrownianWeight {k : ℕ} (s : RSBScheme k)
    (β : ℝ) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (sample : BrownianSample) :
    finiteHistoryDensity (forwardSchemeWeight s β t) (k+2)
      (historySample (fun r sample => β*canonicalBrownian r sample) (forwardSchemeTime s t)
        (k+2) sample) = forwardBrownianWeight β (parisiSchemeMeasure s) t sample := by
  change finiteHistoryDensity (forwardSchemeWeight s β t) (k+2)
    (fun i => β*canonicalBrownian (forwardSchemeTime s t i) sample) = _
  rw [finiteHistoryDensity_forwardScheme_terminal s β t ht (fun r => β*canonicalBrownian r sample)]
  unfold forwardBrownianWeight forwardBrownianAction
  congr 2
  have hs := integral_parisiSchemeMeasure s (fun q => parisiPotential β (parisiSchemeMeasure s)
    (stoppedOverlapTime t q,β*canonicalBrownian (stoppedOverlapTime t q) sample))
  simp only [←forwardSchemeTime_atom] at hs
  rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (s.m (i+1)-s.m i)*
    parisiPotential β (parisiSchemeMeasure s) (forwardSchemeTime s t (i+1),
      β*canonicalBrownian (forwardSchemeTime s t (i+1)) sample))] at hs
  rw [←hs,finiteScheme_stopped_action_split s β t (fun r => β*canonicalBrownian r sample)]
  ring

end FRSB
