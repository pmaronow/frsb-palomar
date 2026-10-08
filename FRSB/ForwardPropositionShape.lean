module

public import FRSB.ForwardSupportInduction
public import FRSB.ForwardActualHeatStep
public import FRSB.ForwardLeftPotential

@[expose] public section

/-! The actual forward shape inequalities, for every Parisi measure and
every positive observation time, including its singleton atom. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology
namespace FRSB

theorem forwardShape_finite (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (hμ : (μ : Measure Overlap).support.Finite) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0) ∧
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0) := by
  apply forwardShape_of_finite_support_heat_steps β hβ μ hμ
  intro r t hr ht hrt hz
  exact forwardBridgeLeftCorrection_heat_step β hβ μ r t hr ht hrt (parisiCDF μ r)
    (forwardCDF_constant_of_open_mass_zero μ r t hz)

/-- The atom-preserving quantizers pass both the right and pre-atom
third-derivative signs to every actual probability measure. -/
theorem forwardShape (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0) ∧
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0) := by
  let q : Overlap := ⟨s,hs.1.le,hs.2⟩
  let S : Finset Overlap := {q}
  let ν := preservingMeasure μ S
  have hm (n : ℕ) : parisiCDF (ν n) s = parisiCDF μ s :=
    preservingMeasure_cdf_mass μ S n q (by simp [S])
  have ha (n : ℕ) : parisiAtomMass (ν n) s hs = parisiAtomMass μ s hs := by
    unfold parisiAtomMass
    exact congrArg ENNReal.toReal (preservingMeasure_atom_mass μ S n q (by simp [S]))
  have hν := tendsto_preservingMeasure μ S
  have hα : Tendsto (fun n => parisiCDF (ν n) s) atTop (𝓝 (parisiCDF μ s)) := by
    simp only [hm]
    exact tendsto_const_nhds
  have hδ : Tendsto (fun n => parisiAtomMass (ν n) s hs) atTop (𝓝 (parisiAtomMass μ s hs)) := by
    simp only [ha]
    exact tendsto_const_nhds
  constructor
  · intro x hx
    apply le_of_tendsto (tendsto_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses
      β μ ν hν s hs hα hδ 3 x)
    exact Eventually.of_forall fun n =>
      (forwardShape_finite β hβ (ν n) (finite_support_preservingMeasure μ S n) s hs).1 x hx
  · intro x hx
    apply le_of_tendsto (tendsto_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf
      β μ ν hν s hs hα 3 x)
    exact Eventually.of_forall fun n =>
      (forwardShape_finite β hβ (ν n) (finite_support_preservingMeasure μ S n) s hs).2 x hx

theorem forwardBridgeCorrection_third_nonpos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0 :=
  (forwardShape β hβ μ s hs).2 x hx

theorem forwardBridgeLeftCorrection_third_nonpos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0 :=
  (forwardShape β hβ μ s hs).1 x hx

theorem forwardBridgeCorrection_curvature_nonneg (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ iteratedDeriv 2 (forwardBridgeCorrection β μ s hs) x :=
  forwardBridgeCorrection_curvature_nonneg_of_third β μ s hs (forwardShape β hβ μ s hs).2 x

theorem forwardBridgeLeftCorrection_curvature_nonneg (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    0 ≤ iteratedDeriv 2 (forwardBridgeLeftCorrection β μ s hs) x :=
  forwardBridgeLeftCorrection_curvature_nonneg_of_third β μ s hs (forwardShape β hβ μ s hs).1 x

theorem forwardLeftPotential_curvature_lower (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardLeftPotential β μ s hs) x :=
  forwardLeftPotential_curvature_lower_of_third β hβ μ s hs (forwardShape β hβ μ s hs).1 x

theorem forwardLeftPotential_third_nonpos (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) (hx : 0 ≤ x) :
    iteratedDeriv 3 (forwardLeftPotential β μ s hs) x ≤ 0 :=
  forwardLeftPotential_third_nonpos_of_third β hβ μ s hs (forwardShape β hβ μ s hs).1 x hx

end FRSB
