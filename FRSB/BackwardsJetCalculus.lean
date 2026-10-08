module

public import FRSB.BackwardsEvolutionJets

@[expose] public section

noncomputable section
open Set Filter
open scoped Topology
namespace FRSB

theorem hasDerivWithinAt_backwardZJet {C D : ℝ → ℝ} {Ct Dt x : ℝ} {s : Set ℝ}
    (hC : HasDerivWithinAt C Ct s x) (hD : HasDerivWithinAt D Dt s x) (hC0 : C x ≠ 0) :
    HasDerivWithinAt (fun y => backwardZJet (C y) (D y))
      (backwardZtJet (C x) (D x) Ct Dt) s x := by
  have hh := hD.neg.div (hC.const_mul 2) (mul_ne_zero (by norm_num) hC0)
  convert hh using 1
  · funext y
    dsimp [backwardZJet]
  · dsimp [backwardZtJet]
    field_simp
    ring

theorem hasDerivWithinAt_backwardWeightedQJet {C D E : ℝ → ℝ} {a Ct Dt Et x : ℝ} {s : Set ℝ}
    (hC : HasDerivWithinAt C Ct s x) (hD : HasDerivWithinAt D Dt s x)
    (hE : HasDerivWithinAt E Et s x) (hC0 : C x ≠ 0) :
    HasDerivWithinAt (fun y => C y * backwardQJet a (C y) (D y) (E y))
      (backwardPtJet a (C x) (D x) (E x) Ct Dt Et) s x := by
  have h1 := hE.neg.div (hC.const_mul 2) (mul_ne_zero (by norm_num) hC0)
  have h2 := (hD.pow 2).div ((hC.pow 2).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC0))
  have hh := hC.mul ((h1.add h2).sub (hC.const_mul a))
  convert hh using 1
  · funext y
    dsimp [backwardQJet, backwardZxJet]
  · dsimp [backwardPtJet, backwardQJet, backwardZxJet]
    field_simp
    ring

theorem hasDerivWithinAt_backwardRJet {C D E F : ℝ → ℝ} {a Ct Dt Et Ft x : ℝ} {s : Set ℝ}
    (hC : HasDerivWithinAt C Ct s x) (hD : HasDerivWithinAt D Dt s x)
    (hE : HasDerivWithinAt E Et s x) (hF : HasDerivWithinAt F Ft s x) (hC0 : C x ≠ 0) :
    HasDerivWithinAt (fun y => backwardRJet a (C y) (D y) (E y) (F y))
      (backwardRtJet a (C x) (D x) (E x) (F x) Ct Dt Et Ft) s x := by
  have h1 := ((hD.mul hE).const_mul 5).div (hC.const_mul 2) (mul_ne_zero (by norm_num) hC0)
  have h2 := ((hD.pow 3).const_mul 3).div ((hC.pow 2).const_mul 2)
    (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC0))
  have hh := ((hF.sub h1).add h2).add ((hC.mul hD).const_mul (3 * a))
  convert hh using 1
  · funext y
    dsimp [backwardRJet]
    ring
  · dsimp [backwardRtJet]
    field_simp
    ring

theorem hasDerivAt_backwardPxJet {C D E F : ℝ → ℝ} {a x G : ℝ}
    (hC : HasDerivAt C (D x) x) (hD : HasDerivAt D (E x) x)
    (hE : HasDerivAt E (F x) x) (hF : HasDerivAt F G x) (hC0 : C x ≠ 0) :
    HasDerivAt (fun y => backwardPxJet a (C y) (D y) (E y) (F y))
      (backwardPxxJet a (C x) (D x) (E x) (F x) G) x := by
  have h1 := (hD.mul hE).div hC hC0
  have h2 := (hD.pow 3).div ((hC.pow 2).const_mul 2) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC0))
  have hh := (((hF.const_mul (-(1 / 2 : ℝ))).add h1).sub h2).sub ((hC.mul hD).const_mul (2 * a))
  convert hh using 1
  · funext y
    dsimp [backwardPxJet]
    ring
  · dsimp [backwardPxxJet]
    field_simp
    ring

theorem hasDerivAt_backwardRxJet {C D E F G : ℝ → ℝ} {a x J : ℝ}
    (hC : HasDerivAt C (D x) x) (hD : HasDerivAt D (E x) x)
    (hE : HasDerivAt E (F x) x) (hF : HasDerivAt F (G x) x)
    (hG : HasDerivAt G J x) (hC0 : C x ≠ 0) :
    HasDerivAt (fun y => backwardRxJet a (C y) (D y) (E y) (F y) (G y))
      (backwardRxxJet a (C x) (D x) (E x) (F x) (G x) J) x := by
  have h1 := (((hE.pow 2).add (hD.mul hF)).const_mul 5).div (hC.const_mul 2)
    (mul_ne_zero (by norm_num) hC0)
  have h2 := (((hD.pow 2).mul hE).const_mul 7).div (hC.pow 2) (pow_ne_zero 2 hC0)
  have h3 := ((hD.pow 4).const_mul 3).div (hC.pow 3) (pow_ne_zero 3 hC0)
  have hh := (((hG.sub h1).add h2).sub h3).add (((hD.pow 2).add (hC.mul hE)).const_mul (3 * a))
  convert hh using 1
  · funext y
    dsimp [backwardRxJet]
    ring
  · dsimp [backwardRxxJet]
    field_simp
    ring

end FRSB
