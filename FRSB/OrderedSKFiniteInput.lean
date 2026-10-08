module

public import FRSB.OrderedSK

@[expose] public section

/-! The literal finite product-Gaussian integral in the paper, transported to
the actual countable realization through its already proved finite joint law. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace FRSB
open Paper

abbrev OrderedSKCouplings (n : ℕ) := OrderedSKEdge n → ℝ

def orderedFiniteCouplingLaw (n : ℕ) : Measure (OrderedSKCouplings n) :=
  Measure.pi (fun _ => gaussianReal 0 1)

def orderedFiniteHamiltonian (n : ℕ) (β : ℝ) (g : OrderedSKCouplings n)
    (σ : SKConfiguration n) : ℝ :=
  β / Real.sqrt (2 * (n : ℝ)) *
    ∑ e : OrderedSKEdge n, g e * spinSign (σ e.1) * spinSign (σ e.2)

def orderedFiniteLogPartition (n : ℕ) (β : ℝ) (g : OrderedSKCouplings n) : ℝ :=
  Real.log (∑ σ : SKConfiguration n, Real.exp (orderedFiniteHamiltonian n β g σ))

/-- Exactly the paper's finite independent-Gaussian expected free energy. -/
def orderedFiniteFreeEnergy (β : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∫ g, orderedFiniteLogPartition n β g ∂orderedFiniteCouplingLaw n

theorem measurable_orderedFiniteLogPartition (n : ℕ) (β : ℝ) :
    Measurable (orderedFiniteLogPartition n β) := by
  unfold orderedFiniteLogPartition orderedFiniteHamiltonian
  fun_prop

/-- The independent finite-coupling logarithmic partition is genuinely integrable. -/
theorem integrable_orderedFiniteLogPartition (n : ℕ) (β : ℝ) :
    Integrable (orderedFiniteLogPartition n β) (orderedFiniteCouplingLaw n) := by
  have hm : Measurable (fun ω e => orderedSKCoupling n e ω) :=
    measurable_pi_iff.mpr (measurable_orderedSKCoupling n)
  have hj := orderedSKCoupling_joint_law n
  rw [orderedFiniteCouplingLaw, ← hj]
  apply (integrable_map_measure
    (measurable_orderedFiniteLogPartition n β).aestronglyMeasurable hm.aemeasurable).mpr
  exact integrable_orderedSK_logPartition n β

/-- The countable realization and the literal finite product integral agree. -/
theorem orderedFiniteFreeEnergy_eq_orderedSK (β : ℝ) (n : ℕ) :
    orderedFiniteFreeEnergy β n = orderedSKFreeEnergy β n := by
  have hm : Measurable (fun ω e => orderedSKCoupling n e ω) :=
    measurable_pi_iff.mpr (measurable_orderedSKCoupling n)
  unfold orderedFiniteFreeEnergy orderedFiniteCouplingLaw
  rw [← orderedSKCoupling_joint_law n,
    integral_map hm.aemeasurable (measurable_orderedFiniteLogPartition n β).aestronglyMeasurable]
  rfl

/-- Exact finite-volume equality with the prior increasing-pair normalization. -/
theorem orderedFiniteFreeEnergy_eq_physical (β : ℝ) (n : ℕ) :
    orderedFiniteFreeEnergy β n = finiteSKFreeEnergy β 0 n := by
  rw [orderedFiniteFreeEnergy_eq_orderedSK, orderedSKFreeEnergy_eq_physical]

/-- The Parisi formula for the literal finite product-Gaussian Hamiltonian. -/
theorem orderedFinite_parisiFormula (β : ℝ) (hβ : 0 < β) :
    Tendsto (orderedFiniteFreeEnergy β) atTop (𝓝 (parisiPDEValue β 0)) := by
  have he : orderedFiniteFreeEnergy β = orderedSKFreeEnergy β :=
    funext (orderedFiniteFreeEnergy_eq_orderedSK β)
  rw [he]
  exact orderedSK_parisiFormula β hβ

end FRSB
