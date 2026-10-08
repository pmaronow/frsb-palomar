module

public import FRSB.MartingaleCrossSum
public import FRSB.BrownianMarkov

@[expose] public section

/-! Exact variance factorization for bounded coefficients known before an
actual scaled canonical Brownian increment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter
open scoped NNReal ENNReal Topology
namespace FRSB

theorem integral_square_centered_gaussian (v : ℝ≥0) :
    (∫x : ℝ,x^2 ∂gaussianReal 0 v) = v := by
  have he := variance_fun_id_gaussianReal (μ := 0) (v := v)
  rw [variance_eq_integral (by fun_prop),integral_id_gaussianReal] at he
  simpa only [sub_zero] using he

theorem integral_square_scaledBrownian_increment (β : ℝ) (a b : ℝ≥0) (hab : a ≤ b) :
    (∫sample,(β*(canonicalBrownian b sample-canonicalBrownian a sample))^2
      ∂canonicalBrownianMeasure) = β^2*((b:ℝ)-a) := by
  have he := (hasLaw_scaledBrownian_increment β a b hab).integral_comp
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x^2) _)
  change (∫sample,(β*(canonicalBrownian b sample-canonicalBrownian a sample))^2
      ∂canonicalBrownianMeasure) = ∫x : ℝ,x^2 ∂gaussianReal 0 _ at he
  rw [he,integral_square_centered_gaussian]
  exact Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β) (sub_nonneg.mpr (show (a:ℝ) ≤ b from hab)))

theorem integral_square_known_scaledBrownian_increment (β : ℝ) (a b : ℝ≥0) (hab : a ≤ b)
    (H : BrownianSample → ℝ) (hH : StronglyMeasurable[canonicalBrownianFiltration a] H) :
    (∫sample,(H sample*(β*(canonicalBrownian b sample-canonicalBrownian a sample)))^2
      ∂canonicalBrownianMeasure) =
    β^2*((b:ℝ)-a)*(∫sample,(H sample)^2 ∂canonicalBrownianMeasure) := by
  have hFB := isBrownianReal_canonicalBrownian.toIsPreBrownianReal.isFilteredPreBrownian
    measurable_canonicalBrownian
  have hraw : IndepFun (canonicalBrownian b-canonicalBrownian a) H canonicalBrownianMeasure := by
    apply (IndepFun_iff_Indep _ _ _).2
    exact indep_of_indep_of_le_right (hFB.indep a b hab) hH.measurable.comap_le
  have hI : IndepFun H (fun sample => β*(canonicalBrownian b sample-canonicalBrownian a sample))
      canonicalBrownianMeasure := by
    simpa only [Function.comp_def,Pi.sub_apply,Pi.mul_apply,id_eq] using
      (hraw.comp (measurable_const.mul measurable_id) measurable_id).symm
  have hsquare : Measurable (fun x : ℝ => x^2) := by fun_prop
  have hsq := hI.comp hsquare hsquare
  have hHg : AEStronglyMeasurable H canonicalBrownianMeasure :=
    (hH.mono (canonicalBrownianFiltration.le a)).aestronglyMeasurable
  have hΔg : AEStronglyMeasurable (fun sample => β*(canonicalBrownian b sample-canonicalBrownian a sample))
      canonicalBrownianMeasure :=
    (((measurable_canonicalBrownian b).sub (measurable_canonicalBrownian a)).const_mul β).aestronglyMeasurable
  have he := hsq.integral_mul_eq_mul_integral (hHg.pow 2) (hΔg.pow 2)
  simp only [Function.comp_def,Pi.mul_apply] at he
  have hfun : (fun sample => (H sample*(β*(canonicalBrownian b sample-canonicalBrownian a sample)))^2) =
      fun sample => (H sample)^2*(β*(canonicalBrownian b sample-canonicalBrownian a sample))^2 := by
    funext sample
    rw [mul_pow]
  rw [hfun,he,integral_square_scaledBrownian_increment β a b hab,mul_comm]

end FRSB
