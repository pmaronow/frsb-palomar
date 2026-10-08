module

public import FRSB.BrownianCrossVariance
public import StochasticCalculus.QuadraticVariationContract

@[expose] public section

/-! Gaussian moments and the vanishing uniform-cell cross-remainder bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace FRSB

theorem integral_fourth_scaledBrownian_increment (β : ℝ) (a b : ℝ≥0) (hab : a ≤ b) :
    (∫sample,(β*(canonicalBrownian b sample-canonicalBrownian a sample))^4
      ∂canonicalBrownianMeasure) = 3*(β^2*((b:ℝ)-a))^2 := by
  have he := integral_pow_four_of_hasLaw_gaussianReal _
    (hasLaw_scaledBrownian_increment β a b hab)
  rw [Real.coe_toNNReal _ (mul_nonneg (sq_nonneg β)
    (sub_nonneg.mpr (show (a:ℝ) ≤ b from hab)))] at he
  exact he

/-- A beta-only polynomial constant suffices; no sharp absolute-moment
constant is needed for convergence of the uniform-cell remainder. -/
def brownianCrossRemainderConstant (β : ℝ) : ℝ := (1+2*β^2+3*β^4)/2

theorem integral_abs_scaledBrownian_cross_remainder (β : ℝ) (a b : ℝ≥0) (hab : a ≤ b) :
    (∫sample, |β*(canonicalBrownian b sample-canonicalBrownian a sample)| *
      (((b:ℝ)-a)+(β*(canonicalBrownian b sample-canonicalBrownian a sample))^2)
      ∂canonicalBrownianMeasure) ≤
    brownianCrossRemainderConstant β*((b:ℝ)-a)*Real.sqrt ((b:ℝ)-a) := by
  let d : ℝ := (b:ℝ)-a
  let Z : BrownianSample → ℝ := fun sample =>
    β*(canonicalBrownian b sample-canonicalBrownian a sample)
  have hd : 0 ≤ d := sub_nonneg.mpr (show (a:ℝ) ≤ b from hab)
  by_cases hz : d = 0
  · have hab' : a = b := by apply NNReal.coe_injective;dsimp [d] at hz;linarith
    subst b
    simp [brownianCrossRemainderConstant]
  have hdpos : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
  let r : ℝ := Real.sqrt d
  have hr : 0 < r := Real.sqrt_pos.mpr hdpos
  have hrsq : r^2 = d := Real.sq_sqrt hd
  have hLaw := hasLaw_scaledBrownian_increment β a b hab
  have h2 : MemLp Z 2 canonicalBrownianMeasure := hLaw.hasGaussianLaw.memLp (by norm_num)
  have h4 : MemLp Z 4 canonicalBrownianMeasure := hLaw.hasGaussianLaw.memLp (by norm_num)
  have hi2 : Integrable (fun sample => Z sample^2) canonicalBrownianMeasure := by
    simpa only [Real.norm_eq_abs,sq_abs] using h2.integrable_norm_pow'
  have hi4 : Integrable (fun sample => Z sample^4) canonicalBrownianMeasure :=
    integrable_pow_four_of_hasLaw_gaussianReal _ hLaw
  have hiabs : Integrable (fun sample => |Z sample|) canonicalBrownianMeasure :=
    ((h2.integrable (by norm_num)).norm).congr (Filter.Eventually.of_forall fun _ => Real.norm_eq_abs _)
  have hi3 : Integrable (fun sample => |Z sample|^3) canonicalBrownianMeasure := by
    have h3 : MemLp Z 3 canonicalBrownianMeasure := hLaw.hasGaussianLaw.memLp (by norm_num)
    simpa only [Real.norm_eq_abs] using h3.integrable_norm_pow'
  have hifun : Integrable (fun sample => |Z sample| *(d+Z sample^2)) canonicalBrownianMeasure := by
    convert (hiabs.mul_const d).add hi3 using 1
    funext sample
    simp only [Pi.add_apply]
    rw [← sq_abs (Z sample)]
    ring
  have hiupper : Integrable (fun sample =>
      (Z sample^4+(d+d)*Z sample^2+d^2)/(2*r)) canonicalBrownianMeasure :=
    ((hi4.add (hi2.const_mul (d+d))).add (integrable_const (d^2))).div_const _
  have hbound (sample : BrownianSample) :
      |Z sample| *(d+Z sample^2) ≤ (Z sample^4+(d+d)*Z sample^2+d^2)/(2*r) := by
    apply (le_div_iff₀ (by positivity : 0 < 2*r)).mpr
    have h1 : 2*r*|Z sample| ≤ Z sample^2+d := by
      have h := sq_nonneg (|Z sample|-r)
      nlinarith [sq_abs (Z sample)]
    have h2' : 2*r*|Z sample|^3 ≤ Z sample^4+d*Z sample^2 := by
      calc
        2*r*|Z sample|^3 = (2*r*|Z sample|)*Z sample^2 := by
          rw [← sq_abs (Z sample)];ring
        _ ≤ (Z sample^2+d)*Z sample^2 :=
          mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = Z sample^4+d*Z sample^2 := by ring
    have h1d := mul_le_mul_of_nonneg_left h1 hd
    calc
      |Z sample| *(d+Z sample^2)*(2*r) =
          d*(2*r*|Z sample|)+2*r*|Z sample|^3 := by
        rw [← sq_abs (Z sample)];ring
      _ ≤ d*(Z sample^2+d)+(Z sample^4+d*Z sample^2) := add_le_add h1d h2'
      _ = Z sample^4+(d+d)*Z sample^2+d^2 := by ring
  have he2 : (∫sample,Z sample^2 ∂canonicalBrownianMeasure) = β^2*d :=
    integral_square_scaledBrownian_increment β a b hab
  have he4 : (∫sample,Z sample^4 ∂canonicalBrownianMeasure) = 3*(β^2*d)^2 :=
    integral_fourth_scaledBrownian_increment β a b hab
  have hu : (∫sample,(Z sample^4+(d+d)*Z sample^2+d^2)/(2*r)
      ∂canonicalBrownianMeasure) = brownianCrossRemainderConstant β*d*r := by
    have he1 : (∫sample,Z sample^4+(d+d)*Z sample^2+d^2 ∂canonicalBrownianMeasure) =
        (∫sample,Z sample^4+(d+d)*Z sample^2 ∂canonicalBrownianMeasure) +
          (∫sample,d^2 ∂canonicalBrownianMeasure) :=
      integral_add (hi4.add (hi2.const_mul _)) (integrable_const _)
    have he2' : (∫sample,Z sample^4+(d+d)*Z sample^2 ∂canonicalBrownianMeasure) =
        (∫sample,Z sample^4 ∂canonicalBrownianMeasure) +
          (∫sample,(d+d)*Z sample^2 ∂canonicalBrownianMeasure) :=
      integral_add hi4 (hi2.const_mul _)
    rw [integral_div,he1,he2',integral_const_mul,he2,he4,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    apply (div_eq_iff (by positivity : 2*r ≠ 0)).mpr
    dsimp [brownianCrossRemainderConstant]
    calc
      3*(β^2*d)^2+(d+d)*(β^2*d)+d^2 = (1+2*β^2+3*β^4)*d^2 := by ring
      _ = ((1+2*β^2+3*β^4)/2*d*r)*(2*r) := by rw [← hrsq];ring
  change (∫sample, |Z sample| *(d+Z sample^2) ∂canonicalBrownianMeasure) ≤ _
  exact (integral_mono hifun hiupper hbound).trans_eq hu

end FRSB
