module

public import FRSB.ComparisonInterval

@[expose] public section

/-! Scalar relative derivative comparison on a constant-mass cell. The
triangular differentiated PDE allows successive use for u3, u4, and u5. -/

noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

def relativeFactor (L k t : ℝ) : ℝ := L * Real.exp (k * t)

theorem relative_linear_cell_barrier
    (a c r J L σ M : ℝ) (ha : 0 ≤ a) (hac : a ≤ c)
    (hr : 1 ≤ r) (hJ : 0 ≤ J) (hL : 1 ≤ L) (hσ : |σ| ≤ 1) (hM : 0 ≤ M)
    (C Ct f ft b α F : ℝ × ℝ → ℝ)
    (hCcont : ContinuousOn C (Icc a c ×ˢ univ))
    (hfcont : ContinuousOn f (Icc a c ×ˢ univ))
    (hCt : ∀ t ∈ Ioc a c, ∀ x,
      HasDerivWithinAt (fun s => C (s, x)) (Ct (t, x)) (Icc a c) t)
    (hft : ∀ t ∈ Ioc a c, ∀ x,
      HasDerivWithinAt (fun s => f (s, x)) (ft (t, x)) (Icc a c) t)
    (hCx : ∀ t ∈ Ioc a c, ∀ x, DifferentiableAt ℝ (fun y => C (t, y)) x)
    (hfx : ∀ t ∈ Ioc a c, ∀ x, DifferentiableAt ℝ (fun y => f (t, y)) x)
    (hCxx : ∀ t ∈ Ioc a c, ∀ x, DifferentiableAt ℝ (deriv (fun y => C (t, y))) x)
    (hfxx : ∀ t ∈ Ioc a c, ∀ x, DifferentiableAt ℝ (deriv (fun y => f (t, y))) x)
    (hCbounds : ∀ t ∈ Icc a c, ∀ x, 0 ≤ C (t, x) ∧ C (t, x) ≤ 1)
    (hfbound : ∀ t ∈ Icc a c, ∀ x, |f (t, x)| ≤ M)
    (hα : ∀ t ∈ Ioc a c, ∀ x, 0 ≤ α (t, x) ∧ α (t, x) ≤ 1)
    (hb : ∀ t ∈ Ioc a c, ∀ x, b (t, x) * sign x ≤ 1)
    (hCPDE : ∀ t ∈ Ioc a c, ∀ x,
      Ct (t, x) - deriv (deriv (fun y => C (t, y))) x / 2 -
        b (t, x) * deriv (fun y => C (t, y)) x = α (t, x) * C (t, x) ^ 2)
    (hfPDE : ∀ t ∈ Ioc a c, ∀ x,
      ft (t, x) - deriv (deriv (fun y => f (t, y))) x / 2 -
        b (t, x) * deriv (fun y => f (t, y)) x =
          r * α (t, x) * C (t, x) * f (t, x) + F (t, x))
    (hF : ∀ t ∈ Ioc a c, ∀ x, |F (t, x)| ≤ J * C (t, x))
    (hinitial : ∀ x, σ * f (a, x) ≤ relativeFactor L (r + J) a * C (a, x)) :
    ∀ t ∈ Icc a c, ∀ x,
      σ * f (t, x) ≤ relativeFactor L (r + J) t * C (t, x) := by
  let k := r + J
  let φ := relativeFactor L k
  let v : ℝ × ℝ → ℝ := fun p => φ p.1 * C p - σ * f p
  let vt : ℝ × ℝ → ℝ := fun p => k * φ p.1 * C p + φ p.1 * Ct p - σ * ft p
  let κ : ℝ × ℝ → ℝ := fun p => r * α p * C p
  have hk : 0 ≤ k := by dsimp [k]; linarith
  have hL0 : 0 ≤ L := by linarith
  have hφpos (t : ℝ) : 0 ≤ φ t := mul_nonneg hL0 (Real.exp_pos _).le
  have hφone (t : ℝ) (ht0 : 0 ≤ t) : 1 ≤ φ t := by
    have he : 1 ≤ Real.exp (k * t) := Real.one_le_exp_iff.mpr (mul_nonneg hk ht0)
    dsimp [φ, relativeFactor]
    nlinarith
  have hφder (t : ℝ) : HasDerivAt φ (k * φ t) t := by
    convert (((hasDerivAt_id t).const_mul k).exp.const_mul L) using 1
    · funext s
      rfl
    · dsimp [φ, relativeFactor]
      ring
  have hvcont : ContinuousOn v (Icc a c ×ˢ comparisonSpace false) := by
    exact ((by dsimp [φ, relativeFactor]; fun_prop : Continuous (fun p : ℝ × ℝ => φ p.1)).continuousOn.mul hCcont).sub
      (hfcont.const_mul σ)
  have hvtime : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior false,
      HasDerivWithinAt (fun s => v (s, x)) (vt (t, x)) (Icc a c) t := by
    intro t ht0 x _
    exact ((hφder t).hasDerivWithinAt.mul (hCt t ht0 x)).sub ((hft t ht0 x).const_mul σ)
  have hvspace (t : ℝ) (ht0 : t ∈ Ioc a c) (x : ℝ) :
      HasDerivAt (fun y => v (t, y))
        (φ t * deriv (fun y => C (t, y)) x - σ * deriv (fun y => f (t, y)) x) x :=
    ((hCx t ht0 x).hasDerivAt.const_mul (φ t)).sub ((hfx t ht0 x).hasDerivAt.const_mul σ)
  have hvxEq (t : ℝ) (ht0 : t ∈ Ioc a c) :
      deriv (fun y => v (t, y)) =
        (fun y => φ t * deriv (fun q => C (t, q)) y - σ * deriv (fun q => f (t, q)) y) :=
    funext fun x => (hvspace t ht0 x).deriv
  have hvxx (t : ℝ) (ht0 : t ∈ Ioc a c) (x : ℝ) :
      HasDerivAt (deriv (fun y => v (t, y)))
        (φ t * deriv (deriv (fun y => C (t, y))) x - σ * deriv (deriv (fun y => f (t, y))) x) x := by
    rw [hvxEq t ht0]
    exact ((hCxx t ht0 x).hasDerivAt.const_mul (φ t)).sub ((hfxx t ht0 x).hasDerivAt.const_mul σ)
  have hvbound : ∀ t ∈ Icc a c, ∀ x ∈ comparisonSpace false, |v (t, x)| ≤ φ c + M := by
    intro t ht0 x _
    have hφtc : φ t ≤ φ c := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht0.2 hk)) hL0
    have hCc := hCbounds t ht0 x
    have h1 : |φ t * C (t, x)| ≤ φ c := by
      rw [abs_of_nonneg (mul_nonneg (hφpos t) hCc.1)]
      exact (mul_le_of_le_one_right (hφpos t) hCc.2).trans hφtc
    have h2 : |σ * f (t, x)| ≤ M := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hσ (abs_nonneg _)).trans (by simpa using hfbound t ht0 x)
    have hs : |φ t * C (t, x) - σ * f (t, x)| ≤ |φ t * C (t, x)| + |σ * f (t, x)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le (φ t * C (t, x)) (σ * f (t, x))
    exact hs.trans (add_le_add h1 h2)
  have hvκ : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior false, κ (t, x) ≤ r + 1 := by
    intro t ht0 x _
    have hCa := hCbounds t ⟨ht0.1.le, ht0.2⟩ x
    have hαa := hα t ht0 x
    have hh : α (t, x) * C (t, x) ≤ 1 := mul_le_one₀ hαa.2 hCa.1 hCa.2
    have hmul := mul_le_mul_of_nonneg_left hh (by linarith : 0 ≤ r)
    dsimp [κ]
    nlinarith
  have hvPDE : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior false,
      0 ≤ vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x) := by
    intro t ht0 x _
    rw [(hvspace t ht0 x).deriv, (hvxx t ht0 x).deriv]
    have hCa := hCbounds t ⟨ht0.1.le, ht0.2⟩ x
    have hαa := hα t ht0 x
    have hαC : α (t, x) * C (t, x) ≤ 1 := mul_le_one₀ hαa.2 hCa.1 hCa.2
    have hg : 1 + J ≤ k - (r - 1) * α (t, x) * C (t, x) := by
      have hh := mul_le_mul_of_nonneg_left hαC (sub_nonneg.mpr hr)
      dsimp [k]
      nlinarith
    have htpos : 0 ≤ t := ha.trans ht0.1.le
    have hφge := hφone t htpos
    have hgap : J ≤ φ t * (k - (r - 1) * α (t, x) * C (t, x)) := by
      have hh := mul_le_mul_of_nonneg_right hφge (by linarith : 0 ≤ k - (r - 1) * α (t, x) * C (t, x))
      nlinarith
    have hsF : σ * F (t, x) ≤ J * C (t, x) := by
      apply (le_abs_self _).trans
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hσ (abs_nonneg _)).trans (by simpa using hF t ht0 x)
    have hgapC := mul_le_mul_of_nonneg_right hgap hCa.1
    have heq : vt (t, x) - (1 / 2 : ℝ) *
        (φ t * deriv (deriv (fun y => C (t, y))) x - σ * deriv (deriv (fun y => f (t, y))) x) -
        b (t, x) * (φ t * deriv (fun y => C (t, y)) x - σ * deriv (fun y => f (t, y)) x) -
        κ (t, x) * v (t, x) =
      φ t * (Ct (t, x) - deriv (deriv (fun y => C (t, y))) x / 2 -
        b (t, x) * deriv (fun y => C (t, y)) x) -
      σ * (ft (t, x) - deriv (deriv (fun y => f (t, y))) x / 2 -
        b (t, x) * deriv (fun y => f (t, y)) x) + k * φ t * C (t, x) -
        r * α (t, x) * C (t, x) * (φ t * C (t, x) - σ * f (t, x)) := by
      dsimp [vt, κ, v]
      ring
    rw [heq, hCPDE t ht0 x, hfPDE t ht0 x]
    nlinarith [hgapC]
  have hcmp := interval_supersolution_nonneg false a c (r + 1) (φ c + M) hac
    (by linarith) (add_nonneg (hφpos c) hM) v vt b κ hvcont hvtime
    (fun t ht0 x _ => (hvspace t ht0 x).differentiableAt)
    (fun t ht0 x _ => (hvxx t ht0 x).differentiableAt) hvbound
    (fun t ht0 x _ => (hb t ht0 x).trans (by linarith)) hvκ hvPDE
    (fun x _ => sub_nonneg.mpr (hinitial x)) (by simp)
  intro t ht0 x
  exact sub_nonneg.mp (hcmp (t, x) ⟨ht0, mem_univ x⟩)

end FRSB
