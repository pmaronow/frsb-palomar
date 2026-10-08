module

public import FRSB.ComparisonBounded

@[expose] public section

noncomputable section
open Set Filter SignType
open scoped Topology
namespace FRSB

/-- The same bounded comparison principle on an arbitrary closed time cell. -/
theorem interval_supersolution_nonneg (halfLine : Bool)
    (a c K M : ℝ) (hac : a ≤ c) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (v vt b κ : ℝ × ℝ → ℝ)
    (hv : ContinuousOn v (Icc a c ×ˢ comparisonSpace halfLine))
    (ht : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      HasDerivWithinAt (fun s => v (s, x)) (vt (t, x)) (Icc a c) t)
    (hx : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (fun y => v (t, y)) x)
    (hxx : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (deriv (fun y => v (t, y))) x)
    (hbound : ∀ t ∈ Icc a c, ∀ x ∈ comparisonSpace halfLine, |v (t, x)| ≤ M)
    (hb : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      b (t, x) * sign x ≤ K)
    (hκ : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior halfLine, κ (t, x) ≤ K)
    (hPDE : ∀ t ∈ Ioc a c, ∀ x ∈ comparisonSpaceInterior halfLine,
      0 ≤ vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x))
    (hinitial : ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (a, x))
    (hboundary : halfLine = true → ∀ t ∈ Icc a c, 0 ≤ v (t, 0)) :
    ∀ p ∈ Icc a c ×ˢ comparisonSpace halfLine, 0 ≤ v p := by
  let shift : ℝ × ℝ → ℝ × ℝ := fun p => (a + p.1, p.2)
  have hmaps : MapsTo (fun s : ℝ => a + s) (Icc 0 (c - a)) (Icc a c) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hmapso : MapsTo (fun s : ℝ => a + s) (Ioc 0 (c - a)) (Ioc a c) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hmapsp : MapsTo shift (Icc 0 (c - a) ×ˢ comparisonSpace halfLine)
      (Icc a c ×ˢ comparisonSpace halfLine) := by
    intro p hp
    exact ⟨hmaps hp.1, hp.2⟩
  have hcont : ContinuousOn (v ∘ shift) (Icc 0 (c - a) ×ˢ comparisonSpace halfLine) :=
    hv.comp (by fun_prop) hmapsp
  have htime : ∀ t ∈ Ioc (0 : ℝ) (c - a), ∀ x ∈ comparisonSpaceInterior halfLine,
      HasDerivWithinAt (fun s => (v ∘ shift) (s, x)) ((vt ∘ shift) (t, x)) (Icc 0 (c - a)) t := by
    intro t ht0 x hx0
    have hh := (ht (a + t) (hmapso ht0) x hx0).comp t
      (((hasDerivAt_const t a).add (hasDerivAt_id t)).hasDerivWithinAt) hmaps
    simpa only [Function.comp_def, shift, zero_add, mul_one] using hh
  have hh := bounded_supersolution_nonneg halfLine (c - a) K M (sub_nonneg.mpr hac) hK hM
    (v ∘ shift) (vt ∘ shift) (b ∘ shift) (κ ∘ shift) hcont htime
    (fun t ht0 x hx0 => hx (a + t) (hmapso ht0) x hx0)
    (fun t ht0 x hx0 => hxx (a + t) (hmapso ht0) x hx0)
    (fun t ht0 x hx0 => hbound (a + t) (hmaps ht0) x hx0)
    (fun t ht0 x hx0 => hb (a + t) (hmapso ht0) x hx0)
    (fun t ht0 x hx0 => hκ (a + t) (hmapso ht0) x hx0)
    (fun t ht0 x hx0 => hPDE (a + t) (hmapso ht0) x hx0)
    (fun x hx0 => by simpa only [Function.comp_def, shift, add_zero] using hinitial x hx0)
    (fun hhalf t ht0 => hboundary hhalf (a + t) (hmaps ht0))
  intro p hp
  have hh0 := hh (p.1 - a, p.2) ⟨⟨sub_nonneg.mpr hp.1.1, sub_le_sub_right hp.1.2 a⟩, hp.2⟩
  simpa only [Function.comp_def, shift, add_sub_cancel] using hh0

end FRSB
