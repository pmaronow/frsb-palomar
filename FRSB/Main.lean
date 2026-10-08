module

public import FRSB.FullSupport
public import FRSB.SupportDensityMass
public import FRSB.ForwardPropositionShape
public import FRSB.ParisiStrictConvexity

@[expose] public section

/-! The two main theorems for the actual, unique zero-field Parisi measure.
The smooth density uses one-sided derivatives at zero and at the terminal
overlap. The terminal atom is kept separate in the measure identity. -/
noncomputable section
open Set MeasureTheory Paper
open scoped ContDiff
namespace FRSB

/-- Literal smooth-density and terminal-atom conclusion of Theorem 1.1. -/
def FullRSBMeasure (β : ℝ) (μ : ParisiMeasure) : Prop :=
  ∃ (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (c : ℝ) (ρ : ℝ → ℝ),
    c ∈ Ioo (0 : ℝ) 1 ∧
    c = parisiAtomMass μ q ⟨hq.1, hq.2.le⟩ ∧
    ContDiffOn ℝ ∞ ρ (Icc (0 : ℝ) q) ∧
    (∀ s ∈ Icc (0 : ℝ) q, 0 ≤ ρ s) ∧
    parisiSupport μ = Icc (0 : ℝ) q ∧
    (μ : Measure Overlap).map (fun x : Overlap => (x : ℝ)) =
      (volume.restrict (Ico (0 : ℝ) q)).withDensity
        (fun s => ENNReal.ofReal (ρ s)) + ENNReal.ofReal c • Measure.dirac q ∧
    (∫ s in 0..q, ρ s) + c = 1

def FullRSBTarget : Prop :=
  ∀ β : ℝ, 1 < β → FullRSBMeasure β (parisiMinimizer β 0)

/-- Theorem 1.2 uses the actual atom at the terminal point of the measure
from Theorem 1.1. Quantification over all minimizers also records uniqueness
independently of the particular compactness choice. -/
def QuantitativeAtomTarget : Prop :=
  ∀ (β : ℝ), 1 < β → ∀ (μ : ParisiMeasure), IsParisiMinimizer β 0 μ →
    ∀ (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1),
      parisiSupport μ = Icc (0 : ℝ) q →
      let c := parisiAtomMass μ q ⟨hq.1, hq.2.le⟩
      (1-c) * (4-(1-c)+1/(β^2*q)) ≤ 2 ∧
        max (Real.sqrt 2-1) (1-2*β^2*q) < c

theorem atom_bounds_of_minimizer_support_interval
    (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0 : ℝ) q) :
    (1-parisiAtomMass μ q ⟨hq.1,hq.2.le⟩) *
      (4-(1-parisiAtomMass μ q ⟨hq.1,hq.2.le⟩)+1/(β^2*q)) ≤ 2 ∧
    parisiAtomMass μ q ⟨hq.1,hq.2.le⟩ ∈ Ioo (0 : ℝ) 1 ∧
    max (Real.sqrt 2-1) (1-2*β^2*q) < parisiAtomMass μ q ⟨hq.1,hq.2.le⟩ := by
  have hn : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  have hb := terminal_atom_bounds_of_support_interval_and_shape β hn μ hmin q
    ⟨hq.1,hq.2.le⟩ hsupp
    (forwardBridgeLeftCorrection_third_nonpos β hn μ q ⟨hq.1,hq.2.le⟩)
  have hm : 1-parisiAtomMass μ q ⟨hq.1,hq.2.le⟩ = parisiLeftMass μ q := by
    erw [parisiAtomMass_eq_cdf_sub_left μ q ⟨hq.1,hq.2.le⟩, parisiCDF_eq_one_above_support μ
      (fun x hx => (hsupp ▸ hx).2) le_rfl]
    ring
  simpa only [hm] using hb

theorem fullRSB_of_minimizer (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) : FullRSBMeasure β μ := by
  have hn : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  obtain ⟨q,hq,hsupp⟩ := minimizer_full_support β hβ μ hmin
  let c := parisiAtomMass μ q ⟨hq.1,hq.2.le⟩
  let ρ := parisiSmoothDensity β μ q
  have hc : c = 1-momentQuotient β μ q := by
    erw [show c = parisiAtomMass μ q ⟨hq.1,hq.2.le⟩ from rfl,
      parisiAtomMass_eq_cdf_sub_left μ q ⟨hq.1,hq.2.le⟩,parisiCDF_eq_one_above_support μ
        (fun x hx => (hsupp ▸ hx).2) le_rfl]
    congr 1
    exact momentQuotient_terminal_mass_of_support_interval β hn μ hmin q hq.1 hq.2.le hsupp
  have hr := parisiSmoothDensity_regular_of_support_interval β hn μ hmin q hq.1 hq.2.le hsupp
  have ha := atom_bounds_of_minimizer_support_interval β hβ μ hmin q hq hsupp
  refine ⟨q,hq,c,ρ,ha.2.1,rfl,hr.1,hr.2,hsupp,?_,?_⟩
  · rw [hc]
    exact parisiMeasure_eq_density_add_atom_of_support_interval β hn μ hmin q hq.1 hq.2.le hsupp
  · exact parisiSmoothDensity_atom_normalization_of_support_interval β hn μ hmin q
      ⟨hq.1,hq.2.le⟩ hsupp

/-- The complete main theorem, with all PDE, diffusion, shape, support,
smoothness and strict atom estimates discharged. -/
theorem fullRSB : FullRSBTarget := fun β hβ =>
  fullRSB_of_minimizer β hβ _ (isParisiMinimizer_selected β 0)

theorem quantitative_atom : QuantitativeAtomTarget := by
  intro β hβ μ hmin q hq hsupp
  have h := atom_bounds_of_minimizer_support_interval β hβ μ hmin q hq hsupp
  exact ⟨h.1,h.2.2⟩

theorem fullRSB_unique (β : ℝ) (hβ : 1 < β) :
    ∃! μ : ParisiMeasure, IsParisiMinimizer β 0 μ ∧ FullRSBMeasure β μ := by
  refine ⟨parisiMinimizer β 0, ⟨isParisiMinimizer_selected β 0,fullRSB β hβ⟩,?_⟩
  exact fun μ hμ => parisiMinimizer_unique β (zero_lt_one.trans hβ).ne' μ hμ.1

end FRSB
