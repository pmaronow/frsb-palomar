module

public import FRSB.BackwardsJets

@[expose] public section

noncomputable section
open Filter
open scoped Topology
namespace FRSB

theorem tendsto_backwardHxJet {A : Type*} {l : Filter A} {c d e f : A → ℝ}
    {C D E F a : ℝ} (hc : Tendsto c l (𝓝 C)) (hd : Tendsto d l (𝓝 D))
    (he : Tendsto e l (𝓝 E)) (hf : Tendsto f l (𝓝 F)) (hC : C ≠ 0) :
    Tendsto (fun n => backwardHxJet a (c n) (d n) (e n) (f n)) l (𝓝 (backwardHxJet a C D E F)) := by
  have hz : Tendsto (fun n => -d n/(2*c n)) l (𝓝 (-D/(2*C))) :=
    hd.neg.div (tendsto_const_nhds.mul hc) (mul_ne_zero (by norm_num) hC)
  have hzx : Tendsto (fun n => -e n/(2*c n)+d n^2/(2*c n^2)) l (𝓝 (-E/(2*C)+D^2/(2*C^2))) :=
    (he.neg.div (tendsto_const_nhds.mul hc) (mul_ne_zero (by norm_num) hC)).add
      ((hd.pow 2).div (tendsto_const_nhds.mul (hc.pow 2)) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC)))
  have hzxx : Tendsto (fun n => -f n/(2*c n)+3*d n*e n/(2*c n^2)-d n^3/c n^3) l
      (𝓝 (-F/(2*C)+3*D*E/(2*C^2)-D^3/C^3)) :=
    ((hf.neg.div (tendsto_const_nhds.mul hc) (mul_ne_zero (by norm_num) hC)).add
      (((tendsto_const_nhds.mul hd).mul he).div (tendsto_const_nhds.mul (hc.pow 2))
        (mul_ne_zero (by norm_num) (pow_ne_zero 2 hC)))).sub
      ((hd.pow 3).div (hc.pow 3) (pow_ne_zero 3 hC))
  exact (((tendsto_const_nhds.mul hz).mul hzx).add (tendsto_const_nhds.mul hd)).sub
    (tendsto_const_nhds.mul (hzxx.sub (tendsto_const_nhds.mul hd)))

end FRSB
