module

public import FRSB.UniformSpatialRegularity
public import FRSB.PotentialMeasureContinuity
public import FRSB.ConstantMassParity
public import Paper.ParisiCurvature

@[expose] public section

/-! Proposition 2.1, including the uniformity over all measures and order-zero convergence. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology
namespace FRSB

def potentialSpatialDerivative (β : ℝ) (μ : ParisiMeasure) (j : ℕ) (p : ℝ × ℝ) : ℝ :=
  iteratedDeriv j (fun x => parisiPotential β μ (p.1, x)) p.2

theorem continuousOn_potentialSpatialDerivative (β : ℝ) (μ : ParisiMeasure) (j : ℕ) :
    ContinuousOn (potentialSpatialDerivative β μ j) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  apply (continuous_parisiSpatialField β μ j).continuousOn.congr
  intro p hp
  exact (parisiSpatialField_eq_iteratedDeriv β μ j p.1 p.2 hp.1).symm

theorem tendstoUniformlyOn_spatialDerivative_of_weak {A : Type*} {l : Filter A}
    [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) (j : ℕ) :
    TendstoUniformlyOn (fun i => potentialSpatialDerivative β (ν i) j)
      (potentialSpatialDerivative β μ j) l (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)) := by
  cases j with
  | zero => exact tendstoUniformlyOn_parisiPotential_of_weak β μ ν hν
  | succ j =>
    have hnorm : Tendsto (fun i =>
        ‖bcfSpatialDerivative (parisiGradientBCF β (ν i)) j -
          bcfSpatialDerivative (parisiGradientBCF β μ) j‖) l (𝓝 0) := by
      simpa using ((tendsto_spatialDerivativeBCF_of_weak β j μ ν hν).sub_const
        (bcfSpatialDerivative (parisiGradientBCF β μ) j)).norm
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hnorm.eventually (eventually_lt_nhds hε)] with i hi
    intro p hp
    rw [Real.dist_eq, abs_sub_comm, ← Real.norm_eq_abs]
    change ‖iteratedDeriv (j+1) (fun x => parisiPotential β (ν i) (p.1,x)) p.2 -
      iteratedDeriv (j+1) (fun x => parisiPotential β μ (p.1,x)) p.2‖ < ε
    rw [← parisiSpatialField_eq_iteratedDeriv β (ν i) (j+1) p.1 p.2 hp.1,
      ← parisiSpatialField_eq_iteratedDeriv β μ (j+1) p.1 p.2 hp.1]
    exact (norm_parisiSlabExtend_sub_le (by norm_num : (0 : ℝ) ≤ 1)
      (bcfSpatialDerivative (parisiGradientBCF β (ν i)) j)
      (bcfSpatialDerivative (parisiGradientBCF β μ) j) p).trans_lt hi

def PDERegularityTarget (β : ℝ) : Prop :=
  (∀ (μ : ParisiMeasure) (t x : ℝ), t ∈ Icc (0 : ℝ) 1 →
    parisiPotential β μ (t,-x) = parisiPotential β μ (t,x)) ∧
  (∀ (μ : ParisiMeasure) (j : ℕ),
    ContinuousOn (potentialSpatialDerivative β μ j) (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ))) ∧
  (∀ n : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ (μ : ParisiMeasure) (t : Icc (0 : ℝ) 1) (x : ℝ),
    |potentialSpatialDerivative β μ (n+1) (t,x)| ≤ K) ∧
  (∀ (μ : ParisiMeasure) (t x : ℝ), t ∈ Icc (0 : ℝ) 1 →
    |parisiGradient β μ (t,x)| ≤ 1 ∧
      0 < parisiHessian β μ (t,x) ∧ parisiHessian β μ (t,x) ≤ 1) ∧
  (∀ (μ : ParisiMeasure) (ν : ℕ → ParisiMeasure), Tendsto ν atTop (𝓝 μ) →
    ∀ j : ℕ, TendstoUniformlyOn (fun i => potentialSpatialDerivative β (ν i) j)
      (potentialSpatialDerivative β μ j) atTop (Icc (0 : ℝ) 1 ×ˢ (univ : Set ℝ)))

theorem pde_regularity (β : ℝ) : PDERegularityTarget β := by
  refine ⟨fun μ t x ht => parisiPotential_even β μ t x ht,
    continuousOn_potentialSpatialDerivative β, ?_, ?_, ?_⟩
  · intro n
    simpa only [potentialSpatialDerivative, Real.norm_eq_abs] using
      positive_order_spatial_derivatives_uniform β n
  · intro μ t x ht
    exact ⟨by simpa only [Real.norm_eq_abs] using norm_parisiGradient_le_one β μ (t,x),
      parisiHessian_pos_all β μ t x ht, parisiHessian_le_one_all β μ (t,x)⟩
  · intro μ ν hν j
    exact tendstoUniformlyOn_spatialDerivative_of_weak β μ ν hν j

end FRSB
