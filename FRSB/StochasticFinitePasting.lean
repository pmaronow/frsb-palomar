module

public import StochasticCalculus.TendstoInMeasureAlgebra
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

/-! Finite pasting of genuine stochastic sums and their endpoint remainders.
No smoothness across atomic time points is required. -/
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace FRSB

theorem tendstoInMeasure_finset_sum {Ω I ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (S : Finset I) (A : I → ι → Ω → ℝ) (L : I → Ω → ℝ)
    (l : Filter ι) (hA : ∀ i ∈ S, TendstoInMeasure P (A i) l (L i)) :
    TendstoInMeasure P (fun n sample => ∑ i ∈ S, A i n sample) l
      (fun sample => ∑ i ∈ S, L i sample) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro ε hε
    simp only [Finset.sum_empty,edist_self]
    have he : {sample : Ω | ε ≤ (0 : ℝ≥0∞)} = ∅ := by
      ext sample
      simp only [mem_setOf_eq,mem_empty_iff_false,iff_false]
      exact not_le_of_gt hε
    simp only [he,measure_empty]
    exact tendsto_const_nhds
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (hA i (Finset.mem_insert_self i S)).add_real_noMeas
      (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj)))

theorem finite_interval_remainder_telescope (F : ℝ → ℝ) (a : ℕ → ℝ)
    (g : ℝ → ℝ) (n : ℕ)
    (hg : ∀ k < n, IntervalIntegrable g volume (a k) (a (k+1))) :
    (∑ k ∈ Finset.range n, (F (a (k+1))-F (a k)-∫s in a k..a (k+1),g s)) =
      F (a n)-F (a 0)-∫s in a 0..a n,g s := by
  rw [Finset.sum_sub_distrib,Finset.sum_range_sub (fun k => F (a k)),
    intervalIntegral.sum_integral_adjacent_intervals hg]

end FRSB
