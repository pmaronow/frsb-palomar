module

public import FRSB.GaussianDensityCalculus
public import FRSB.ForwardHeatRegularity

@[expose] public section

/-! Gaussian completion gives a genuine heat solution from a bounded
smooth forward bridge factor, with actual variance differentiation. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped ContDiff Topology
namespace FRSB
set_option maxHeartbeats 1000000

 def forwardHeatDensity (β r:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  heatDensity (β^2*t) x*forwardHeatFactor (β^2*r) F (β^2*t) x

 def forwardHeatDensityX (β r:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  (-x/(β^2*t)*heatDensity (β^2*t) x)*forwardHeatFactor (β^2*r) F (β^2*t) x+
    heatDensity (β^2*t) x*forwardHeatJet (β^2*r) F 1 (β^2*t) x

 def forwardHeatDensityXX (β r:ℝ) (F:ℝ→ℝ) (t x:ℝ) : ℝ :=
  (x^2/(β^2*t)^2-1/(β^2*t))*heatDensity (β^2*t) x*
      forwardHeatFactor (β^2*r) F (β^2*t) x+
    2*(-x/(β^2*t)*heatDensity (β^2*t) x)*forwardHeatJet (β^2*r) F 1 (β^2*t) x+
      heatDensity (β^2*t) x*forwardHeatJet (β^2*r) F 2 (β^2*t) x

 theorem hasDerivAt_forwardHeatFactor_spatial (r:ℝ) (F:ℝ→ℝ)
    (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hb:∀j x,‖iteratedDeriv j F x‖≤K j)
    (t x:ℝ) : HasDerivAt (forwardHeatFactor r F t) (forwardHeatJet r F 1 t x) x := by
  have hd:=hasDerivAt_forwardHeatJet_spatial r F hF K hb 0 t x
  convert hd using 1
  · funext y
    simp only [forwardHeatJet,forwardHeatFactor,iteratedDeriv_zero,pow_zero,one_mul]

 theorem hasDerivAt_forwardHeatDensity_spatial (β r:ℝ) (F:ℝ→ℝ)
    (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hb:∀j x,‖iteratedDeriv j F x‖≤K j)
    (t x:ℝ) : HasDerivAt (forwardHeatDensity β r F t) (forwardHeatDensityX β r F t x) x := by
  exact (hasDerivAt_heatDensity_spatial (β^2*t) x).mul
    (hasDerivAt_forwardHeatFactor_spatial (β^2*r) F hF K hb (β^2*t) x)

 theorem hasDerivAt_forwardHeatDensityX_spatial (β r:ℝ) (F:ℝ→ℝ)
    (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hb:∀j x,‖iteratedDeriv j F x‖≤K j)
    (t x:ℝ) : HasDerivAt (forwardHeatDensityX β r F t) (forwardHeatDensityXX β r F t x) x := by
  have hg:=hasDerivAt_heatDensity_spatial (β^2*t) x
  have hgg:=hasDerivAt_deriv_heatDensity_spatial (β^2*t) x
  have he:deriv (heatDensity (β^2*t))=fun y=>-y/(β^2*t)*heatDensity (β^2*t) y:=
    funext fun y=>(hasDerivAt_heatDensity_spatial (β^2*t) y).deriv
  rw [he] at hgg
  have hH:=hasDerivAt_forwardHeatFactor_spatial (β^2*r) F hF K hb (β^2*t) x
  have hH1:=hasDerivAt_forwardHeatJet_spatial (β^2*r) F hF K hb 1 (β^2*t) x
  convert (hgg.mul hH).add (hg.mul hH1) using 1
  · rfl
  · unfold forwardHeatDensityXX
    ring

 theorem iteratedDeriv_forwardHeatDensity_two (β r:ℝ) (F:ℝ→ℝ)
    (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hb:∀j x,‖iteratedDeriv j F x‖≤K j)
    (t x:ℝ) : iteratedDeriv 2 (forwardHeatDensity β r F t) x=forwardHeatDensityXX β r F t x := by
  have he:deriv (forwardHeatDensity β r F t)=forwardHeatDensityX β r F t:=
    funext fun y=>(hasDerivAt_forwardHeatDensity_spatial β r F hF K hb t y).deriv
  rw [show (2:ℕ)=1+1 by rfl,iteratedDeriv_succ,iteratedDeriv_one,he]
  exact (hasDerivAt_forwardHeatDensityX_spatial β r F hF K hb t x).deriv

 theorem contDiff_forwardHeatDensity_spatial (β r:ℝ) (F:ℝ→ℝ)
    (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ) (hb:∀j x,‖iteratedDeriv j F x‖≤K j)
    (t:ℝ) : ContDiff ℝ ∞ (forwardHeatDensity β r F t) := by
  have hg:ContDiff ℝ ∞ (heatDensity (β^2*t)) := by unfold heatDensity;fun_prop
  exact hg.mul (contDiff_forwardHeatFactor (β^2*r) F hF K hb (β^2*t))

 theorem hasDerivAt_forwardHeatFactor_time_scaled (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hb:∀j x,‖iteratedDeriv j F x‖≤K j) {t:ℝ} (hrt:r<t) (x:ℝ) :
    HasDerivAt (fun v=>forwardHeatFactor (β^2*r) F (β^2*v) x)
      ((β^2/2)*forwardHeatJet (β^2*r) F 2 (β^2*t) x-
        x/t*forwardHeatJet (β^2*r) F 1 (β^2*t) x) t := by
  have hbs:=sq_pos_of_ne_zero hβ
  have hd:=(hasDerivAt_forwardHeatJet_time (β^2*r) (mul_pos hbs hr) F hF K hb 0
    (β^2*t) x (mul_lt_mul_of_pos_left hrt hbs)).comp t ((hasDerivAt_id t).const_mul (β^2))
  convert hd using 1
  · funext v
    simp only [forwardHeatJet,forwardHeatFactor,iteratedDeriv_zero,pow_zero,one_mul,Function.comp_apply]
  · simp only [Nat.cast_zero,zero_div,zero_mul,sub_zero]
    have ht:=hr.trans hrt
    field_simp [hβ,ht.ne']

 theorem hasDerivAt_forwardHeatDensity_time (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hb:∀j x,‖iteratedDeriv j F x‖≤K j) {t:ℝ} (hrt:r<t) (x:ℝ) :
    HasDerivAt (fun v=>forwardHeatDensity β r F v x)
      ((β^2/2)*iteratedDeriv 2 (forwardHeatDensity β r F t) x) t := by
  have ht:=hr.trans hrt
  have hg:=(hasDerivAt_heatDensity_time (β^2*t) x
    (mul_pos (sq_pos_of_ne_zero hβ) ht)).comp t ((hasDerivAt_id t).const_mul (β^2))
  have hH:=hasDerivAt_forwardHeatFactor_time_scaled β r hβ hr F hF K hb hrt x
  convert hg.mul hH using 1
  · rfl
  · rw [iteratedDeriv_forwardHeatDensity_two β r F hF K hb]
    unfold forwardHeatDensityXX
    dsimp only [Function.comp_apply]
    field_simp [hβ,ht.ne']; ring

end FRSB
