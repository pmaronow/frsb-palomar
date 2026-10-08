module

public import FRSB.ForwardPropositionShape
public import FRSB.ForwardLeftJets
public import FRSB.ConstantMassGrowthRefined
public import FRSB.CrossingBridgeFields
public import Mathlib.Analysis.Convex.Deriv

@[expose] public section

/-! The origin-relative Gaussian tail and genuine all-orders local uniform
convergence of the pre-atom correction complete the forward conclusions. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology
namespace FRSB

/-- The exact paper heat-step formula, with right input and pre-atom
output, follows from a literal zero-mass open cell. -/
theorem forwardBridgeLeftCorrection_heat_of_zero_mass (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hrt : r < t)
    (hzero : (μ : Measure Overlap) {q : Overlap | r < (q : ℝ) ∧ (q : ℝ) < t} = 0) :
    forwardBridgeLeftCorrection β μ t ht =
      forwardHeatCorrection (β ^ 2 * r) (β ^ 2 * t) (forwardBridgeCorrection β μ r hr) :=
  forwardBridgeLeftCorrection_heat_step β hβ μ r t hr ht hrt (parisiCDF μ r)
    (forwardCDF_constant_of_open_mass_zero μ r t hzero)

/-- A single positive constant controls both one-sided actual gauges,
every measure and positive time, and every derivative through order k. -/
theorem forward_derivative_bounds (β : ℝ) (k : ℕ) (_hk : 1 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∀ (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
      (j : ℕ), j ∈ Icc 1 k → ∀ x : ℝ,
      ‖iteratedDeriv j (forwardBridgeCorrection β μ s hs) x‖ ≤ c ∧
      ‖iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs) x‖ ≤ c := by
  let c : ℝ := 1 + ∑ i ∈ Finset.range (k+1),
    (forwardCorrectionDerivativeConstant β i + forwardBridgeLeftDerivativeConstant β i)
  have hn (i : ℕ) : 0 ≤ forwardCorrectionDerivativeConstant β i + forwardBridgeLeftDerivativeConstant β i :=
    add_nonneg (forwardCorrectionDerivativeConstant_nonneg β i)
      (forwardBridgeLeftDerivativeConstant_nonneg β i)
  refine ⟨c,?_,?_⟩
  · dsimp [c]
    have hh : 0 ≤ ∑ i ∈ Finset.range (k+1),
        (forwardCorrectionDerivativeConstant β i + forwardBridgeLeftDerivativeConstant β i) :=
      Finset.sum_nonneg (fun i _ => hn i)
    linarith
  · intro μ s hs j hj x
    have hjk := hj.2
    have hb : forwardCorrectionDerivativeConstant β j + forwardBridgeLeftDerivativeConstant β j ≤ c := by
      have hh := Finset.single_le_sum (fun i _ => hn i)
        (Finset.mem_range.mpr (by omega : j < k+1))
      dsimp [c]
      linarith
    constructor
    · exact (forwardBridgeCorrection_uniform_derivative_bound β μ s hs j hj.1 x).trans
        (by change forwardCorrectionDerivativeConstant β j ≤ c
            linarith [forwardBridgeLeftDerivativeConstant_nonneg β j])
    · exact (forwardBridgeLeftCorrection_uniform_derivative_bound β μ s hs j hj.1 x).trans
        (by linarith [forwardCorrectionDerivativeConstant_nonneg β j])

lemma convex_even_origin_le (W : ℝ → ℝ) (hc : ConvexOn ℝ univ W)
    (he : ∀ x, W (-x) = W x) (x : ℝ) : W 0 ≤ W x := by
  have hh := hc.2 (mem_univ x) (mem_univ (-x))
    (show (0 : ℝ) ≤ 1/2 by norm_num) (show (0 : ℝ) ≤ 1/2 by norm_num)
    (show (1/2 : ℝ)+1/2=1 by norm_num)
  have hz : (1/2 : ℝ) • x + (1/2 : ℝ) • (-x) = 0 := by
    simp only [smul_eq_mul]
    ring
  rw [hz,he x] at hh
  simp only [smul_eq_mul] at hh
  linarith

theorem forwardBridgeCorrection_origin_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeCorrection β μ s hs 0 ≤ forwardBridgeCorrection β μ s hs x := by
  have hW := contDiff_forwardBridgeCorrection β μ s hs
  have hd : Differentiable ℝ (deriv (forwardBridgeCorrection β μ s hs)) := by
    simpa only [iteratedDeriv_one] using hW.differentiable_iteratedDeriv 1 (by simp)
  have hc := convexOn_univ_of_deriv2_nonneg (hW.differentiable (by simp)) hd
    (fun x => by simpa only [← iteratedDeriv_eq_iterate] using
      forwardBridgeCorrection_curvature_nonneg β hβ μ s hs x)
  exact convex_even_origin_le _ hc (forwardBridgeCorrection_even β μ s hs) x

theorem forwardBridgeLeftCorrection_origin_le (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeLeftCorrection β μ s hs 0 ≤ forwardBridgeLeftCorrection β μ s hs x := by
  have hW := contDiff_forwardBridgeLeftCorrection β μ s hs
  have hd : Differentiable ℝ (deriv (forwardBridgeLeftCorrection β μ s hs)) := by
    simpa only [iteratedDeriv_one] using hW.differentiable_iteratedDeriv 1 (by simp)
  have hc := convexOn_univ_of_deriv2_nonneg (hW.differentiable (by simp)) hd
    (fun x => by simpa only [← iteratedDeriv_eq_iterate] using
      forwardBridgeLeftCorrection_curvature_nonneg β hβ μ s hs x)
  exact convex_even_origin_le _ hc (forwardBridgeLeftCorrection_even β μ s hs) x

theorem forwardBridgeDensity_origin_relative_tail (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    forwardBridgeDensity β μ s hs x ≤ forwardBridgeDensity β μ s hs 0 *
      Real.exp (parisiCDF μ s * |x| - x ^ 2 / (2 * (β ^ 2 * s))) := by
  have hu := (parisiPotential_origin_growth β μ s x ⟨hs.1.le,hs.2⟩).2
  have hw := forwardBridgeCorrection_origin_le β hβ μ s hs x
  have he : forwardBridgeDensity β μ s hs x = forwardBridgeDensity β μ s hs 0 *
      Real.exp (parisiCDF μ s * (parisiPotential β μ (s,x) - parisiPotential β μ (s,0)) -
        (forwardBridgeCorrection β μ s hs x - forwardBridgeCorrection β μ s hs 0) -
          x ^ 2 / (2 * (β ^ 2 * s))) := by
    rw [forwardBridgeDensity_eq_exponential, forwardBridgeDensity_eq_exponential]
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div, neg_zero, zero_add]
    have hee : -x ^ 2 / (2 * (β ^ 2 * s)) + parisiCDF μ s * parisiPotential β μ (s,x) -
        forwardBridgeCorrection β μ s hs x =
        (parisiCDF μ s * parisiPotential β μ (s,0) - forwardBridgeCorrection β μ s hs 0) +
        (parisiCDF μ s * (parisiPotential β μ (s,x) - parisiPotential β μ (s,0)) -
          (forwardBridgeCorrection β μ s hs x - forwardBridgeCorrection β μ s hs 0) -
            x ^ 2 / (2 * (β ^ 2 * s))) := by ring
    rw [hee,Real.exp_add]
    ring
  rw [he]
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (forwardBridgeDensity_pos β hβ μ s hs 0).le
  nlinarith [mul_nonneg (parisiCDF_nonneg μ s) (sub_nonneg.mpr hu)]

theorem tendstoUniformlyOn_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses
    {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s)))
    (hδ : Tendsto (fun a => parisiAtomMass (ν a) s hs) l (𝓝 (parisiAtomMass μ s hs)))
    (j : ℕ) (S : Set ℝ) (hS : IsCompact S) :
    TendstoUniformlyOn (fun a => iteratedDeriv j (forwardBridgeLeftCorrection β (ν a) s hs))
      (iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs)) l S := by
  apply tendstoUniformlyOn_of_common_derivative_bound _ _ S hS
    (Real.nnabs (forwardBridgeLeftDerivativeConstant β (j+1)))
  · intro a
    exact (contDiff_forwardBridgeLeftCorrection β (ν a) s hs).differentiable_iteratedDeriv j
      (by exact_mod_cast ENat.natCast_lt_top j)
  · intro a x
    rw [← iteratedDeriv_succ]
    simpa only [Real.coe_nnabs] using
      (forwardBridgeLeftCorrection_uniform_derivative_bound β (ν a) s hs (j+1) (by omega) x).trans
        (le_abs_self _)
  · exact fun x _ => tendsto_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses
      β μ ν hν s hs hα hδ j x

theorem forward_correction_preserving_cloc (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (S : Set ℝ) (hS : IsCompact S) :
    let q : Overlap := ⟨s,hs.1.le,hs.2⟩
    let ν := preservingMeasure μ {q}
    TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeCorrection β (ν n) s hs))
      (iteratedDeriv j (forwardBridgeCorrection β μ s hs)) atTop S ∧
    TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeLeftCorrection β (ν n) s hs))
      (iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs)) atTop S := by
  intro q ν
  have hν := tendsto_preservingMeasure μ {q}
  have hm (n : ℕ) : parisiCDF (ν n) s = parisiCDF μ s :=
    preservingMeasure_cdf_mass μ {q} n q (Finset.mem_singleton_self q)
  have ha (n : ℕ) : parisiAtomMass (ν n) s hs = parisiAtomMass μ s hs := by
    unfold parisiAtomMass
    exact congrArg ENNReal.toReal (preservingMeasure_atom_mass μ {q} n q (Finset.mem_singleton_self q))
  have hα : Tendsto (fun n => parisiCDF (ν n) s) atTop (𝓝 (parisiCDF μ s)) := by
    simp only [hm]; exact tendsto_const_nhds
  have hδ : Tendsto (fun n => parisiAtomMass (ν n) s hs) atTop (𝓝 (parisiAtomMass μ s hs)) := by
    simp only [ha]; exact tendsto_const_nhds
  exact ⟨tendstoUniformlyOn_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf β μ ν hν s hs hα j S hS,
    tendstoUniformlyOn_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses β μ ν hν s hs hα hδ j S hS⟩

end FRSB
