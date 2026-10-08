module

public import FRSB.ForwardConclusions
public import FRSB.ForwardRightPotential
public import FRSB.ForwardLeftCurvature
public import FRSB.ForwardDensityLaw

@[expose] public section

/-! Complete actual forward-density conclusion of Proposition 4.1,
including pre-atom endpoint conventions and all-orders approximation. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology
namespace FRSB

theorem forwardLeftPotential_curvature_bounds (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardLeftPotential β μ s hs) x ∧
    iteratedDeriv 2 (forwardLeftPotential β μ s hs) x ≤ 1 / (β ^ 2 * s) + parisiLeftMass μ s := by
  rw [iteratedDeriv_forwardLeftPotential_two β hβ μ s hs x]
  exact ⟨le_add_of_nonneg_right (forwardBridgeLeftCorrection_curvature_nonneg β hβ μ s hs x),
    add_le_add le_rfl (forwardBridgeLeftCorrection_curvature_le_leftMass β μ s hs x)⟩

theorem forward_proposition (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ s.toNNReal) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) ∧
    ContDiff ℝ ∞ (forwardBridgeDensity β μ s hs) ∧
    (∀ x, 0 < forwardBridgeDensity β μ s hs x ∧
      forwardBridgeDensity β μ s hs (-x) = forwardBridgeDensity β μ s hs x) ∧
    ContDiff ℝ ∞ (forwardRightPotential β μ s hs) ∧
    ContDiff ℝ ∞ (forwardLeftPotential β μ s hs) ∧
    (∀ x, forwardRightPotential β μ s hs (-x) = forwardRightPotential β μ s hs x ∧
      forwardLeftPotential β μ s hs (-x) = forwardLeftPotential β μ s hs x) ∧
    ContDiff ℝ ∞ (forwardBridgeCorrection β μ s hs) ∧
    ContDiff ℝ ∞ (forwardBridgeLeftCorrection β μ s hs) ∧
    (∀ x, forwardBridgeCorrection β μ s hs (-x) = forwardBridgeCorrection β μ s hs x ∧
      forwardBridgeLeftCorrection β μ s hs (-x) = forwardBridgeLeftCorrection β μ s hs x) ∧
    (∀ x, ‖deriv (forwardBridgeCorrection β μ s hs) x‖ ≤ 1 ∧
      ‖deriv (forwardBridgeLeftCorrection β μ s hs) x‖ ≤ 1) ∧
    (∀ x, (1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardRightPotential β μ s hs) x ∧
        iteratedDeriv 2 (forwardRightPotential β μ s hs) x ≤ 1 / (β ^ 2 * s) + parisiCDF μ s) ∧
      (1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardLeftPotential β μ s hs) x ∧
        iteratedDeriv 2 (forwardLeftPotential β μ s hs) x ≤ 1 / (β ^ 2 * s) + parisiLeftMass μ s)) ∧
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardRightPotential β μ s hs) x ≤ 0 ∧
      iteratedDeriv 3 (forwardLeftPotential β μ s hs) x ≤ 0) ∧
    (∀ x, forwardBridgeDensity β μ s hs x ≤ Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x ∧
      forwardBridgeDensity β μ s hs x ≤ forwardBridgeDensity β μ s hs 0 *
        Real.exp (parisiCDF μ s * |x| - x ^ 2 / (2 * (β ^ 2 * s)))) ∧
    (∀ j S, IsCompact S →
      let q : Overlap := ⟨s,hs.1.le,hs.2⟩
      let ν := preservingMeasure μ {q}
      TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeCorrection β (ν n) s hs))
        (iteratedDeriv j (forwardBridgeCorrection β μ s hs)) atTop S ∧
      TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeLeftCorrection β (ν n) s hs))
        (iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs)) atTop S) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ (ν : ParisiMeasure) (t : ℝ)
      (ht : t ∈ Ioc (0 : ℝ) 1) (j : ℕ), j ∈ Icc 1 k → ∀ x : ℝ,
      ‖iteratedDeriv j (forwardBridgeCorrection β ν t ht) x‖ ≤ c ∧
      ‖iteratedDeriv j (forwardBridgeLeftCorrection β ν t ht) x‖ ≤ c) := by
  exact ⟨selectedState_endpoint_eq_bridgeDensity β hβ μ s hs,
    contDiff_forwardBridgeDensity β μ s hs,
    fun x => ⟨forwardBridgeDensity_pos β hβ μ s hs x,forwardBridgeDensity_even β μ s hs x⟩,
    contDiff_forwardRightPotential β hβ μ s hs,contDiff_forwardLeftPotential β hβ μ s hs,
    fun x => ⟨forwardRightPotential_even β μ s hs x,forwardLeftPotential_even β μ s hs x⟩,
    contDiff_forwardBridgeCorrection β μ s hs,contDiff_forwardBridgeLeftCorrection β μ s hs,
    fun x => ⟨forwardBridgeCorrection_even β μ s hs x,forwardBridgeLeftCorrection_even β μ s hs x⟩,
    fun x => ⟨forwardBridgeCorrection_slope_bound β μ s hs x,forwardBridgeLeftCorrection_slope_bound β μ s hs x⟩,
    fun x => ⟨forwardRightPotential_curvature_bounds β hβ μ s hs x,forwardLeftPotential_curvature_bounds β hβ μ s hs x⟩,
    fun x hx => ⟨forwardRightPotential_third_nonpos β hβ μ s hs x hx,forwardLeftPotential_third_nonpos β hβ μ s hs x hx⟩,
    fun x => ⟨forwardBridgeDensity_gaussian_envelope β μ s hs x,forwardBridgeDensity_origin_relative_tail β hβ μ s hs x⟩,
    fun j S hS => forward_correction_preserving_cloc β μ s hs j S hS,
    fun k hk => forward_derivative_bounds β k hk⟩

end FRSB
