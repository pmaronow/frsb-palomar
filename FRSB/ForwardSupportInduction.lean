module

public import FRSB.ForwardSupportGeometry
public import FRSB.ForwardActualShapeSteps

@[expose] public section

/-! Chronological forward-shape induction on the genuine finite support.
The only transfer input is the exact heat evolution on zero-mass cells. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped ContDiff Topology
namespace FRSB
set_option maxHeartbeats 200000
attribute [local irreducible] forwardBridgeAction forwardBridgeJet forwardBridgeFactor
  forwardBridgePathFactor forwardBridgeCorrection forwardBridgeLeftCorrection

lemma forward_shape_time_congr (β : ℝ) (μ : ParisiMeasure)
    (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1) (he : r = t) :
    ((∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ r hr) x ≤ 0) ∧
      (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ r hr) x ≤ 0)) ↔
    ((∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ t ht) x ≤ 0) ∧
      (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ t ht) x ≤ 0)) := by
  subst t
  rfl

theorem forwardShape_of_finite_support_heat_steps (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (hμ : (μ : Measure Overlap).support.Finite)
    (hheat : ∀ (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1), r < t →
      (μ : Measure Overlap) {q : Overlap | r < (q : ℝ) ∧ (q : ℝ) < t} = 0 →
      forwardBridgeLeftCorrection β μ t ht =
        forwardHeatCorrection (β ^ 2 * r) (β ^ 2 * t) (forwardBridgeCorrection β μ r hr))
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) :
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ s hs) x ≤ 0) ∧
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ s hs) x ≤ 0) := by
  let N := (forwardSupportNodes μ hμ s hs).card
  let q : Fin N → ℝ := fun i => forwardSupportNode μ hμ s hs i
  have hq0 : q ⟨0,forwardSupportNodes_card_pos μ hμ s hs⟩ = 0 :=
    congrArg Subtype.val (forwardSupportNode_zero μ hμ s hs)
  have hqI (j : ℕ) (hj : j < N) (hp : 0 < j) : q ⟨j,hj⟩ ∈ Ioc (0 : ℝ) 1 :=
    forwardSupportNode_mem_Ioc μ hμ s hs _ hp
  have hind (j : ℕ) : ∀ (hj : j < N) (hp : 0 < j),
      (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeLeftCorrection β μ (q ⟨j,hj⟩) (hqI j hj hp)) x ≤ 0) ∧
      (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardBridgeCorrection β μ (q ⟨j,hj⟩) (hqI j hj hp)) x ≤ 0) := by
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hj hp
      obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hcell := forwardSupportNode_cell_zero_mass μ hμ s hs k hj
      have hleft : ∀ x, 0 ≤ x → iteratedDeriv 3
          (forwardBridgeLeftCorrection β μ (q ⟨k+1,hj⟩) (hqI (k+1) hj hp)) x ≤ 0 := by
        by_cases hk : k = 0
        · subst k
          have hz : (μ : Measure Overlap) {t : Overlap | 0 < (t : ℝ) ∧
              (t : ℝ) < q ⟨0+1,hj⟩} = 0 := by
            have hset : {t : Overlap | 0 < (t : ℝ) ∧ (t : ℝ) < q ⟨1,hj⟩} =
                {t : Overlap | q ⟨0,by omega⟩ < (t : ℝ) ∧ (t : ℝ) < q ⟨1,hj⟩} := by
              ext t
              simp only [mem_ofPred_eq]
              constructor <;> intro hh <;> exact ⟨by linarith [hq0],hh.2⟩
            rw [hset]
            exact hcell
          intro x hx
          exact (forwardBridgeLeft_third_zero_of_no_positive_mass β μ _ _ hz x).le
        · have hk0 : 0 < k := Nat.pos_of_ne_zero hk
          have hkc : k < N := by omega
          have hprev := ih k (Nat.lt_succ_self k) hkc hk0
          have hkt : q ⟨k,hkc⟩ < q ⟨k+1,hj⟩ :=
            (forwardSupportNode μ hμ s hs).strictMono
              (show (⟨k,hkc⟩ : Fin N) < ⟨k+1,hj⟩ from Nat.lt_succ_self k)
          have he := hheat (q ⟨k,hkc⟩) (q ⟨k+1,hj⟩) (hqI k hkc hk0)
            (hqI (k+1) hj hp) hkt hcell
          exact forwardBridgeLeft_heat_shape_transfer β hβ μ _ _ _ _ hkt.le he hprev.2
      exact ⟨hleft,forwardBridgeRight_atom_shape_transfer β hβ μ _ _ hleft⟩
  have hN : 1 < N := forwardSupportNodes_one_lt_card μ hμ s hs
  have hj : N-1 < N := by omega
  have hp : 0 < N-1 := by omega
  have he : q ⟨N-1,hj⟩ = s := congrArg Subtype.val (forwardSupportNode_last μ hμ s hs)
  exact (forward_shape_time_congr β μ _ s (hqI (N-1) hj hp) hs he).mp (hind (N-1) hj hp)

end FRSB
