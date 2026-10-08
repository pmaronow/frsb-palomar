module

public import FRSB.ForwardHeatDensity

@[expose] public section

/-! Joint positive-time continuity of the genuine Gaussian heat solution
and the first two spatial jets used in its forward PDE. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace FRSB
set_option maxHeartbeats 1000000

 theorem continuousOn_forwardHeatJet_scaled (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) (j:ℕ) :
    ContinuousOn (fun p:ℝ×ℝ=>forwardHeatJet (β^2*r) F j (β^2*p.1) p.2)
      (Ioi r ×ˢ (univ:Set ℝ)) := by
  apply (continuousOn_forwardHeatJet (β^2*r) (mul_pos (sq_pos_of_ne_zero hβ) hr)
    F hF K hK j).comp (continuous_const.mul continuous_fst |>.prodMk continuous_snd |>.continuousOn)
  intro p hp
  exact ⟨mul_le_mul_of_nonneg_left hp.1.le (sq_nonneg β),mem_univ _⟩

 theorem continuousOn_forwardHeatFactor_scaled (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) :
    ContinuousOn (fun p:ℝ×ℝ=>forwardHeatFactor (β^2*r) F (β^2*p.1) p.2)
      (Ioi r ×ˢ (univ:Set ℝ)) := by
  convert continuousOn_forwardHeatJet_scaled β r hβ hr F hF K hK 0 using 1
  funext p
  simp only [forwardHeatFactor,forwardHeatJet,iteratedDeriv_zero,pow_zero,one_mul]

 theorem continuousOn_heatDensity_scaled (β r:ℝ) (hβ:β≠0) (hr:0<r) :
    ContinuousOn (fun p:ℝ×ℝ=>heatDensity (β^2*p.1) p.2) (Ioi r ×ˢ (univ:Set ℝ)) := by
  have hv:∀p∈Ioi r ×ˢ (univ:Set ℝ),0<β^2*p.1:=fun p hp=>
    mul_pos (sq_pos_of_ne_zero hβ) (hr.trans hp.1)
  intro p hp
  have hpos:=hv p hp
  have hs:Real.sqrt (2*Real.pi*(β^2*p.1))≠0:=by positivity
  have hden:2*(β^2*p.1)≠0:=by positivity
  have hc:ContinuousAt (fun z:ℝ×ℝ=>heatDensity (β^2*z.1) z.2) p := by
    unfold heatDensity
    fun_prop (disch:=assumption)
  exact hc.continuousWithinAt

 theorem continuousOn_forwardHeatDensity (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) :
    ContinuousOn (fun p:ℝ×ℝ=>forwardHeatDensity β r F p.1 p.2)
      (Ioi r ×ˢ (univ:Set ℝ)) :=
  (continuousOn_heatDensity_scaled β r hβ hr).mul
    (continuousOn_forwardHeatFactor_scaled β r hβ hr F hF K hK)

 theorem continuousOn_forwardHeatDensityX (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) :
    ContinuousOn (fun p:ℝ×ℝ=>forwardHeatDensityX β r F p.1 p.2)
      (Ioi r ×ˢ (univ:Set ℝ)) := by
  have hn:∀p∈Ioi r ×ˢ (univ:Set ℝ),β^2*p.1≠0:=fun p hp=>
    (mul_pos (sq_pos_of_ne_zero hβ) (hr.trans hp.1)).ne'
  have hfrac:ContinuousOn (fun p:ℝ×ℝ=>-p.2/(β^2*p.1)) (Ioi r ×ˢ (univ:Set ℝ)):=
    continuous_snd.neg.continuousOn.div (continuous_const.mul continuous_fst).continuousOn hn
  exact ((hfrac.mul (continuousOn_heatDensity_scaled β r hβ hr)).mul
    (continuousOn_forwardHeatFactor_scaled β r hβ hr F hF K hK)).add
      ((continuousOn_heatDensity_scaled β r hβ hr).mul
        (continuousOn_forwardHeatJet_scaled β r hβ hr F hF K hK 1))

 theorem continuousOn_forwardHeatDensityXX (β r:ℝ) (hβ:β≠0) (hr:0<r)
    (F:ℝ→ℝ) (hF:ContDiff ℝ ∞ F) (K:ℕ→ℝ)
    (hK:∀j x,‖iteratedDeriv j F x‖≤K j) :
    ContinuousOn (fun p:ℝ×ℝ=>forwardHeatDensityXX β r F p.1 p.2)
      (Ioi r ×ˢ (univ:Set ℝ)) := by
  have hn:∀p∈Ioi r ×ˢ (univ:Set ℝ),β^2*p.1≠0:=fun p hp=>
    (mul_pos (sq_pos_of_ne_zero hβ) (hr.trans hp.1)).ne'
  have hfrac:ContinuousOn (fun p:ℝ×ℝ=>-p.2/(β^2*p.1)) (Ioi r ×ˢ (univ:Set ℝ)):=
    continuous_snd.neg.continuousOn.div (continuous_const.mul continuous_fst).continuousOn hn
  have hcoeff:ContinuousOn (fun p:ℝ×ℝ=>p.2^2/(β^2*p.1)^2-1/(β^2*p.1))
      (Ioi r ×ˢ (univ:Set ℝ)):=
    ((continuous_snd.pow 2).continuousOn.div ((continuous_const.mul continuous_fst).pow 2).continuousOn
      (fun p hp=>pow_ne_zero 2 (hn p hp))).sub
        (continuousOn_const.div (continuous_const.mul continuous_fst).continuousOn hn)
  have hg:=continuousOn_heatDensity_scaled β r hβ hr
  exact (((hcoeff.mul hg).mul (continuousOn_forwardHeatFactor_scaled β r hβ hr F hF K hK)).add
      (((continuousOn_const.mul (hfrac.mul hg)).mul
        (continuousOn_forwardHeatJet_scaled β r hβ hr F hF K hK 1)))).add
      (hg.mul (continuousOn_forwardHeatJet_scaled β r hβ hr F hF K hK 2))

end FRSB
