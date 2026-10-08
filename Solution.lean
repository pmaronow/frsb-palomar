module

public import FRSB.Main
public import Paper.ParisiWeakWellPosed

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Calculus.Deriv.Support
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Measure.Support

@[expose] public section

/-!
# Full replica symmetry breaking in the zero-field SK model

This proved interface states Theorems 1.1 and 1.2 of Patrick Lopatto,
*Full replica symmetry breaking in the Sherrington--Kirkpatrick model*.
Its concrete definitions are repeated from the independent Challenge. The Parisi functional is specified by the actual weak terminal
PDE, not by a supplied potential or an assumed minimizer. The infimum defining
its time-zero value is totalized by Lean outside the theorem's domain. Here,
existence and uniqueness prove that its defining set is a nonempty
singleton for every nonzero inverse temperature.

The density is smooth on the closed support interval in the one-sided sense
of `ContDiffOn`; the terminal atom is separate. These statements concern the
zero-field Parisi minimizing measure for `β > 1`.
-/

noncomputable section
open Set MeasureTheory
open scoped ContDiff

namespace PalomarFRSB

/-- The allowed overlap domain is the closed real interval `[0,1]`. -/
abbrev Overlap := Icc (0 : ℝ) 1

/-- Actual Borel probability measures on the overlap domain. -/
abbrev ParisiMeasure := ProbabilityMeasure Overlap

/-- Cumulative probability, including mass at the observation point. -/
def cdf (μ : ParisiMeasure) (t : ℝ) : ℝ :=
  ((μ : Measure Overlap) {q : Overlap | (q : ℝ) ≤ t}).toReal

/-- Lebesgue measure on the closed time strip times the full spatial line. -/
def spaceTime : Measure (ℝ × ℝ) :=
  (volume.restrict (Icc (0 : ℝ) 1)).prod volume

def testX (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => φ (p.1, x)) p.2

def testXX (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun x => testX φ (p.1, x)) p.2

def testT (φ : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  deriv (fun t => φ (t, p.2)) p.1

/-- The spatial distributional derivative, with integrability explicit. -/
def IsWeakGradient (u v : ℝ × ℝ → ℝ) : Prop :=
  ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1 ∧ p.1 < 1} →
    Integrable (fun p => u p * testX φ p + v p * φ p) spaceTime ∧
      (∫ p, u p * testX φ p + v p * φ p ∂spaceTime) = 0

/-- The weak Parisi terminal PDE `u_t + β²/2 (u_xx + cdf(t) u_x²) = 0`,
with terminal value `log(cosh x)`. Tests may meet time one, retaining the
terminal trace. No differentiability or supplied growth bound is assumed. -/
structure IsWeakSolution (β : ℝ) (μ : ParisiMeasure)
    (u v : ℝ × ℝ → ℝ) : Prop where
  continuous_potential : ContinuousOn u (Icc (0 : ℝ) 1 ×ˢ univ)
  measurable_gradient : AEStronglyMeasurable v spaceTime
  bounded_gradient : ∃ M : ℝ, ∀ᵐ p ∂spaceTime, ‖v p‖ ≤ M
  weak_gradient : IsWeakGradient u v
  terminal : ∀ x : ℝ, u (1, x) = Real.log (Real.cosh x)
  equation : ∀ φ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
    tsupport φ ⊆ {p : ℝ × ℝ | 0 < p.1} →
    Integrable (fun p => -u p * testT φ p + β ^ 2 / 2 *
      (u p * testXX φ p + cdf μ p.1 * v p ^ 2 * φ p)) spaceTime ∧
    Integrable (fun x => φ (1, x) * Real.log (Real.cosh x)) ∧
    (∫ p, -u p * testT φ p + β ^ 2 / 2 *
      (u p * testXX φ p + cdf μ p.1 * v p ^ 2 * φ p) ∂spaceTime) +
      (∫ x, φ (1, x) * Real.log (Real.cosh x)) = 0

/-- Values at `(0,0)` of actual solutions of the specified weak PDE. -/
def potentialValueSet (β : ℝ) (μ : ParisiMeasure) : Set ℝ :=
  {r | ∃ u v : ℝ × ℝ → ℝ, IsWeakSolution β μ u v ∧ r = u (0, 0)}

/-- The paper's Parisi functional at zero external field. The additive
`log 2` and correction coefficient `β²/2` fix the SK normalization. -/
def zeroFieldFunctional (β : ℝ) (μ : ParisiMeasure) : ℝ :=
  Real.log 2 + sInf (potentialValueSet β μ) -
    β ^ 2 / 2 * ∫ t in (0 : ℝ)..1, t * cdf μ t

/-- Global minimization over all overlap probability measures. -/
def IsMinimizer (β : ℝ) (μ : ParisiMeasure) : Prop :=
  ∀ ν : ParisiMeasure, zeroFieldFunctional β μ ≤ zeroFieldFunctional β ν

/-- The real image of the measure's actual topological support. -/
def support (μ : ParisiMeasure) : Set ℝ :=
  Subtype.val '' (μ : Measure Overlap).support

/-- Actual singleton probability at a positive overlap at most one. -/
def atomMass (μ : ParisiMeasure) (q : ℝ) (hq : q ∈ Ioc (0 : ℝ) 1) : ℝ :=
  ((μ : Measure Overlap) {⟨q, hq.1.le, hq.2⟩}).toReal

/-- Smooth nonnegative density on the full support interval, and a separate
positive terminal atom of mass strictly less than one, with exact normalization. -/
def FullRSBMeasure (μ : ParisiMeasure) : Prop :=
  ∃ (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1) (c : ℝ) (ρ : ℝ → ℝ),
    c ∈ Ioo (0 : ℝ) 1 ∧
    c = atomMass μ q ⟨hq.1, hq.2.le⟩ ∧
    ContDiffOn ℝ ∞ ρ (Icc (0 : ℝ) q) ∧
    (∀ t ∈ Icc (0 : ℝ) q, 0 ≤ ρ t) ∧
    support μ = Icc (0 : ℝ) q ∧
    (μ : Measure Overlap).map (fun x : Overlap => (x : ℝ)) =
      (volume.restrict (Ico (0 : ℝ) q)).withDensity
        (fun t => ENNReal.ofReal (ρ t)) + ENNReal.ofReal c • Measure.dirac q ∧
    (∫ t in 0..q, ρ t) + c = 1

/-- The independent weak-PDE class has exactly the original development's fields. -/
private theorem weakSolution_iff (β : ℝ) (μ : ParisiMeasure)
    (u v : ℝ × ℝ → ℝ) :
    IsWeakSolution β μ u v ↔ Paper.IsParisiWeakSolution β μ u v := by
  constructor
  · intro h
    exact ⟨h.continuous_potential, h.measurable_gradient, h.bounded_gradient,
      h.weak_gradient, h.terminal, h.equation⟩
  · intro h
    exact ⟨h.continuous_potential, h.measurable_gradient, h.bounded_gradient,
      h.weak_gradient, h.terminal, h.equation⟩

/-- Existence and unrestricted weak uniqueness discharge the infimum definition. -/
private theorem potentialValueSet_eq_singleton (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) :
    potentialValueSet β μ = {Paper.parisiPotential β μ (0, 0)} := by
  ext r
  constructor
  · rintro ⟨u, v, h, hr⟩
    have he := ((weakSolution_iff β μ u v).mp h).eq_parisiPotential hβ
      (0, 0) (by simp)
    exact mem_singleton_iff.mpr (hr.trans he)
  · intro hr
    exact ⟨Paper.parisiPotential β μ, Paper.parisiGradient β μ,
      (weakSolution_iff β μ _ _).mpr (Paper.parisiPotential_isWeakSolution β hβ μ),
      mem_singleton_iff.mp hr⟩

/-- The independent functional is the constructed PDE functional, including
its time-zero value, additive normalization and correction integral. -/
private theorem zeroFieldFunctional_eq (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) :
    zeroFieldFunctional β μ = Paper.parisiPDEFunctional β 0 μ := by
  unfold zeroFieldFunctional
  rw [potentialValueSet_eq_singleton β hβ μ, csInf_singleton]
  rfl

private theorem isMinimizer_iff (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) :
    IsMinimizer β μ ↔ FRSB.IsParisiMinimizer β 0 μ := by
  unfold IsMinimizer FRSB.IsParisiMinimizer
  simp only [zeroFieldFunctional_eq β hβ]

/-- **Theorem 1.1**, together with the proved uniqueness of the zero-field
Parisi minimizer: for every `β > 1`, a minimizing probability measure has the
stated form, and every minimizing probability measure equals it. -/
theorem fullRSB :
    ∀ β : ℝ, 1 < β → ∃ μ : ParisiMeasure,
      IsMinimizer β μ ∧ FullRSBMeasure μ ∧
        ∀ ν : ParisiMeasure, IsMinimizer β ν → ν = μ := by
  intro β hβ
  have hn : β ≠ 0 := (zero_lt_one.trans hβ).ne'
  refine ⟨FRSB.parisiMinimizer β 0,
    (isMinimizer_iff β hn _).mpr (FRSB.isParisiMinimizer_selected β 0),
    FRSB.fullRSB β hβ, ?_⟩
  intro ν hν
  exact FRSB.parisiMinimizer_unique β hn ν ((isMinimizer_iff β hn ν).mp hν)

/-- **Theorem 1.2**: the actual terminal atom satisfies both the quadratic
bound and the strict lower bound, for every minimizer and terminal support point. -/
theorem quantitativeAtom :
    ∀ β : ℝ, 1 < β → ∀ μ : ParisiMeasure, IsMinimizer β μ →
      ∀ (q : ℝ) (hq : q ∈ Ioo (0 : ℝ) 1), support μ = Icc (0 : ℝ) q →
        let c := atomMass μ q ⟨hq.1, hq.2.le⟩
        (1 - c) * (4 - (1 - c) + 1 / (β ^ 2 * q)) ≤ 2 ∧
          max (Real.sqrt 2 - 1) (1 - 2 * β ^ 2 * q) < c := by
  intro β hβ μ hμ q hq hsupp
  exact FRSB.quantitative_atom β hβ μ
    ((isMinimizer_iff β (zero_lt_one.trans hβ).ne' μ).mp hμ) q hq hsupp

end PalomarFRSB
