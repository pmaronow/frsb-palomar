module

public import FRSB.TerminalAtomEstimate
public import FRSB.ForwardDensityLaw

@[expose] public section

/-! Terminal atom conclusions for the actual minimizer once its support
interval and the forward shape theorem are supplied. -/
noncomputable section
open Set Filter MeasureTheory Paper
namespace FRSB

theorem parisiLeftMass_pos_of_zero_support (μ : ParisiMeasure)
    (hzero : 0 ∈ parisiSupport μ) {q : ℝ} (hq : 0 < q) : 0 < parisiLeftMass μ q := by
  obtain ⟨z,hz,hz0⟩ := hzero
  let U : Set Overlap := {t | (t:ℝ) < q}
  have hU : IsOpen U := isOpen_lt continuous_subtype_val continuous_const
  have hzU : z ∈ U := by change (z:ℝ) < q;rw [hz0];exact hq
  have hp := ((μ : Measure Overlap).mem_support_iff_forall z).mp hz U (hU.mem_nhds hzU)
  exact ENNReal.toReal_pos hp.ne' (measure_ne_top _ _)

theorem parisiLeftMass_mem_unit (μ : ParisiMeasure) (q : ℝ) :
    parisiLeftMass μ q ∈ Icc (0:ℝ) 1 := by
  refine ⟨ENNReal.toReal_nonneg,?_⟩
  have h := ENNReal.toReal_mono (measure_ne_top (μ : Measure Overlap) univ)
    (measure_mono (subset_univ {t : Overlap | (t:ℝ) < q}))
  convert! h using 1
  simp only [measure_univ,ENNReal.toReal_one]

theorem terminal_crossing_phi_zero_of_support_interval (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1)
    (hsupp : parisiSupport μ = Icc (0:ℝ) q) :
    (∫ x, terminalCrossingPhi (parisiLeftMass μ q) x
      ∂crossingWeightLaw (bridgeCrossingWeight β μ q hq)) = 0 := by
  have hmax : ∀ x ∈ parisiSupport μ, x ≤ q := fun x hx => (hsupp ▸ hx).2
  apply terminal_crossing_phi_zero_of_full_moment β hβ μ hq hmax (parisiLeftMass μ q)
  let ψ : ℝ → ℝ := fun x => sech x^4 * terminalCrossingPhi (parisiLeftMass μ q) x
  have hψ : Measurable ψ := by
    exact ((gaussian_continuous_sech.pow 4).mul
      ((continuous_const.mul (gaussian_continuous_tanh.pow 2)).sub
        (continuous_const.mul (gaussian_continuous_sech.pow 2)))).measurable
  have hi := integral_selectedState_bridgeDensity β hβ μ q hq ψ hψ
  have he : ∀ sample, selectedParisiItoState β 0 hβ μ q.toNNReal sample =
      optimalStateReal β μ sample q := by
    intro sample
    rw [← optimalState_eq_selected β hβ μ,optimalState_eq_real β μ
      (by simpa only [Real.coe_toNNReal q hq.1.le] using hq.2) sample]
    rw [Real.coe_toNNReal q hq.1.le]
  have hphysical := terminal_physical_phi_moment_zero β hβ μ hmin q hq.1 hq.2 hsupp
  change (∫ sample, ψ (optimalStateReal β μ sample q) ∂canonicalBrownianMeasure) = 0 at hphysical
  calc
    _ = ∫ x, forwardBridgeDensity β μ q hq x*ψ x := by
      congr 1
      funext x
      dsimp [ψ]
      ring
    _ = ∫ sample, ψ (selectedParisiItoState β 0 hβ μ q.toNNReal sample) ∂canonicalBrownianMeasure := hi.symm
    _ = ∫ sample, ψ (optimalStateReal β μ sample q) ∂canonicalBrownianMeasure :=
      integral_congr_ae (.of_forall fun sample => congrArg ψ (he sample))
    _ = 0 := hphysical

theorem terminal_atom_bounds_of_support_interval_and_shape (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hmin : ∀ ν : ParisiMeasure,
      parisiPDEFunctional β 0 μ ≤ parisiPDEFunctional β 0 ν)
    (q : ℝ) (hq : q ∈ Ioc (0:ℝ) 1) (hsupp : parisiSupport μ = Icc (0:ℝ) q)
    (hshape : ∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ q hq) x ≤ 0) :
    parisiLeftMass μ q * (4-parisiLeftMass μ q+1/(β^2*q)) ≤ 2 ∧
      parisiAtomMass μ q hq ∈ Ioo (0:ℝ) 1 ∧
      max (Real.sqrt 2-1) (1-2*β^2*q) < parisiAtomMass μ q hq := by
  have hmax : ∀ x ∈ parisiSupport μ, x ≤ q := fun x hx => (hsupp ▸ hx).2
  have hquad := terminal_atom_quadratic_of_shape_and_centering β hβ μ q hq hmax hshape
    (terminal_crossing_phi_zero_of_support_interval β hβ μ hmin q hq hsupp)
  have hm := parisiLeftMass_mem_unit μ q
  have hc : parisiAtomMass μ q hq = 1-parisiLeftMass μ q := by
    rw [parisiAtomMass_eq_cdf_sub_left,parisiCDF_eq_one_above_support μ hmax le_rfl]
  have hmpos := parisiLeftMass_pos_of_zero_support μ
    (hsupp ▸ (show (0:ℝ) ∈ Icc (0:ℝ) q from ⟨le_rfl,hq.1.le⟩)) hq.1
  refine ⟨hquad,?_,?_⟩
  · rw [hc]
    exact ⟨atom_mass_positive hm.1 hm.2 (by have hv := mul_pos (sq_pos_of_ne_zero hβ) hq.1; positivity) hquad,
      by linarith⟩
  · rw [hc]
    exact atom_mass_strict_lower_bounds hβ hq.1 hm.1 hm.2 hquad

end FRSB
