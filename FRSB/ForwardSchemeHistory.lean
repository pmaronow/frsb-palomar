module

public import FRSB.FiniteHistoryDensity
public import FRSB.ConstantMassLaw
public import FRSB.FiniteSchemeRepresentation

@[expose] public section

/-! Actual chronological records of a finite overlap scheme, stopped at a
physical time. Repeated nodes and endpoint atoms remain in the record. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper SpinGlass.Targets
open scoped NNReal ENNReal Topology
namespace FRSB

def forwardSchemeTime {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (j : ℕ) : ℝ≥0 :=
  ⟨min (s.q (min j (k+2))) t, le_min (s.q_nonneg (min_le_right _ _)) t.coe_nonneg⟩

def forwardSchemeMass {k : ℕ} (s : RSBScheme k) (j : ℕ) : ℝ :=
  s.m (min j (k+1))

theorem forwardSchemeTime_monotone {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) :
    Monotone (forwardSchemeTime s t) := by
  intro i j hij
  exact min_le_min_right _ (s.q_mono' (min j (k+2)) (min_le_right _ _)
    (min i (k+2)) (min_le_min_right _ hij))

@[simp] theorem forwardSchemeTime_zero {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) :
    forwardSchemeTime s t 0 = 0 := by
  apply NNReal.eq
  simp only [forwardSchemeTime, Nat.zero_min, s.q_zero, NNReal.coe_zero]
  exact min_eq_left t.coe_nonneg

@[simp] theorem forwardSchemeTime_top {k : ℕ} (s : RSBScheme k) (t : ℝ≥0)
    (ht : (t:ℝ) ≤ 1) {j : ℕ} (hj : k+2 ≤ j) : forwardSchemeTime s t j = t := by
  apply NNReal.eq
  simp only [forwardSchemeTime, min_eq_right hj, s.q_top, min_eq_right ht]
  rfl

theorem forwardSchemeTime_le {k : ℕ} (s : RSBScheme k) (t : ℝ≥0) (j : ℕ) :
    forwardSchemeTime s t j ≤ t := by
  change min (s.q (min j (k+2))) (t:ℝ) ≤ t
  exact min_le_right _ _

theorem parisiCDF_forwardScheme_cell {k : ℕ} (s : RSBScheme k) (t : ℝ≥0)
    (ht : (t:ℝ) ≤ 1) (j : ℕ) {r : ℝ}
    (hr : r ∈ Ico (forwardSchemeTime s t j : ℝ) (forwardSchemeTime s t (j+1) : ℝ)) :
    parisiCDF (parisiSchemeMeasure s) r = forwardSchemeMass s j := by
  by_cases hj : k+2 ≤ j
  · rw [forwardSchemeTime_top s t ht hj,
      forwardSchemeTime_top s t ht (by omega)] at hr
    exact (not_lt_of_ge hr.1 hr.2).elim
  · have hj' : j ≤ k+1 := by omega
    have hq : s.q j < (t:ℝ) := by
      by_contra hn
      have hh : (t:ℝ) ≤ r := by
        have hr1 := hr.1
        change min (s.q (min j (k+2))) (t:ℝ) ≤ r at hr1
        simpa only [forwardSchemeTime, min_eq_left (by omega : j ≤ k+2),
          min_eq_right (not_lt.mp hn)] using hr1
      have hh' : r < (t:ℝ) := hr.2.trans_le (forwardSchemeTime_le s t (j+1))
      linarith
    have hlo : s.q j ≤ r := by
      have hr1 := hr.1
      change min (s.q (min j (k+2))) (t:ℝ) ≤ r at hr1
      simpa only [forwardSchemeTime, min_eq_left (by omega : j ≤ k+2),
        min_eq_left hq.le] using hr1
    have hhi : r < s.q (j+1) := by
      exact hr.2.trans_le (show (forwardSchemeTime s t (j+1):ℝ) ≤ s.q (j+1) by
        simp only [forwardSchemeTime, min_eq_left (by omega : j+1 ≤ k+2)]
        exact min_le_left _ _)
    simpa only [forwardSchemeMass, min_eq_left hj'] using
      parisiCDF_scheme_cell s hj' ⟨hlo,hhi⟩

def forwardSchemeKernel {k : ℕ} (s : RSBScheme k) (β : ℝ) (t : ℝ≥0) (j : ℕ) :
    Kernel ℝ ℝ := parisiConstantMassKernel β (parisiSchemeMeasure s)
      (forwardSchemeTime s t j) (forwardSchemeTime s t (j+1)-forwardSchemeTime s t j)
      (forwardSchemeMass s j)

theorem isMarkovKernel_forwardSchemeKernel {k : ℕ} (s : RSBScheme k) (β : ℝ)
    (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (j : ℕ) : IsMarkovKernel (forwardSchemeKernel s β t j) := by
  apply isMarkovKernel_parisiConstantMassKernel
  rw [← NNReal.coe_add, add_tsub_cancel_of_le (forwardSchemeTime_monotone s t (Nat.le_succ j))]
  exact (show (forwardSchemeTime s t (j+1):ℝ) ≤ t from forwardSchemeTime_le s t (j+1)).trans ht

theorem selectedState_forwardScheme_restricted_transition {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hβ : β ≠ 0) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (j : ℕ)
    (E : Set BrownianSample)
    (hE : MeasurableSet[canonicalBrownianFiltration (forwardSchemeTime s t j)] E) :
    (canonicalBrownianMeasure.restrict E).map
      (selectedParisiItoState β h hβ (parisiSchemeMeasure s) (forwardSchemeTime s t (j+1))) =
      forwardSchemeKernel s β t j ∘ₘ (canonicalBrownianMeasure.restrict E).map
        (selectedParisiItoState β h hβ (parisiSchemeMeasure s) (forwardSchemeTime s t j)) := by
  let a := forwardSchemeTime s t j
  let b := forwardSchemeTime s t (j+1)
  have hab : a ≤ b := forwardSchemeTime_monotone s t (Nat.le_succ j)
  have hab1 : (a:ℝ)+(b-a:ℝ≥0) ≤ 1 := by
    rw [← NNReal.coe_add, add_tsub_cancel_of_le hab]
    exact (show (forwardSchemeTime s t (j+1):ℝ) ≤ t from forwardSchemeTime_le s t (j+1)).trans ht
  by_cases he : a = b
  · change (canonicalBrownianMeasure.restrict E).map
      (selectedParisiItoState β h hβ (parisiSchemeMeasure s) b) =
      parisiConstantMassKernel β (parisiSchemeMeasure s) a (b-a) (forwardSchemeMass s j) ∘ₘ _
    rw [← he, tsub_self]
    have hker : parisiConstantMassKernel β (parisiSchemeMeasure s) a 0 (forwardSchemeMass s j) =
        Kernel.id := by
      unfold parisiConstantMassKernel
      simp only [NNReal.coe_zero, mul_zero, Real.toNNReal_zero]
      exact constantMassKernel_zero_variance _ _
        ((continuous_parisiPotential β _).comp (continuous_const.prodMk continuous_id))
        (parisiPotential_hasLinearGrowth β _ _
          ⟨by simpa only [add_zero] using a.coe_nonneg, by simpa only [he, tsub_self, NNReal.coe_zero] using hab1⟩)
    rw [hker, Measure.id_comp]
  · have hpos : 0 < b-a := tsub_pos_iff_lt.mpr (lt_of_le_of_ne hab he)
    have hc : ∀ r ∈ Ico (a:ℝ) ((a:ℝ)+(b-a:ℝ≥0)),
        parisiCDF (parisiSchemeMeasure s) r = forwardSchemeMass s j := by
      rw [← NNReal.coe_add, add_tsub_cancel_of_le hab]
      exact fun r hr => parisiCDF_forwardScheme_cell s t ht j hr
    have hh := selectedParisiState_constantMass_restricted_transitionLaw β h hβ
      (parisiSchemeMeasure s) a (b-a) hpos hab1 (forwardSchemeMass s j) hc E hE
    rw [add_tsub_cancel_of_le hab] at hh
    exact hh

theorem selectedState_forwardScheme_historyLaw {k : ℕ} (s : RSBScheme k)
    (β h : ℝ) (hβ : β ≠ 0) (t : ℝ≥0) (ht : (t:ℝ) ≤ 1) (n : ℕ) :
    canonicalBrownianMeasure.map
      (historySample (selectedParisiItoState β h hβ (parisiSchemeMeasure s))
        (forwardSchemeTime s t) n) =
      finiteHistoryLaw
        (canonicalBrownianMeasure.map (selectedParisiItoState β h hβ (parisiSchemeMeasure s) 0))
        (forwardSchemeKernel s β t) n := by
  simpa only [forwardSchemeTime_zero] using
    historySample_law_of_restricted canonicalBrownianMeasure canonicalBrownianFiltration
      (selectedParisiItoState β h hβ (parisiSchemeMeasure s))
      (stronglyAdapted_selectedParisiState β h hβ _) (forwardSchemeTime s t)
      (forwardSchemeTime_monotone s t) (forwardSchemeKernel s β t)
      (isMarkovKernel_forwardSchemeKernel s β t ht)
      (selectedState_forwardScheme_restricted_transition s β h hβ t ht) n

end FRSB
