module

public import FRSB.MomentRegularity

@[expose] public section

/-! Genuine higher self-consistency derivatives on constant-mass intervals.
The third derivative is computed from the closed stochastic polynomial
hierarchy, rather than imposed as an analytical assumption. -/
noncomputable section
open Set Filter MeasureTheory MvPolynomial Paper
open scoped Topology ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

 def gammaThirdPolynomial (m:ℝ) : MomentPolynomial :=
  X 3^2-MvPolynomial.C (12*m)*X 1*X 2^2+MvPolynomial.C (6*m^2)*X 1^4

 def GammaThird (β:ℝ) (μ:ParisiMeasure) (m s:ℝ) : ℝ :=
  β^6*moment β μ (gammaThirdPolynomial m) s

 theorem GammaThird_eq_integral (β:ℝ) (μ:ParisiMeasure) (m s:ℝ) :
    GammaThird β μ m s=β^6*(∫sample,A β μ s sample^2-
      12*m*C β μ s sample*D β μ s sample^2+6*m^2*C β μ s sample^4
      ∂canonicalBrownianMeasure) := by
  simp only [GammaThird,moment,momentPolynomialValue,gammaThirdPolynomial,
    map_add,map_sub,map_mul,map_pow,eval_X,eval_C,Nat.reduceAdd]

 theorem gammaThird_generator_moment (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m:ℝ) {s:ℝ} (hs:s∈Icc (0:ℝ) 1) :
    moment β μ (gammaThirdPolynomial m) s=
      moment β μ (momentDrift0 quotientNumeratorPolynomial) s+
        m*moment β μ (momentDrift1 quotientNumeratorPolynomial) s-
      2*m*(moment β μ (momentDrift0 quotientDenominatorPolynomial) s+
        m*moment β μ (momentDrift1 quotientDenominatorPolynomial) s) := by
  have h0A:=integrable_momentPolynomialValue β hβ μ (momentDrift0 quotientNumeratorPolynomial) hs
  have h1A:=integrable_momentPolynomialValue β hβ μ (momentDrift1 quotientNumeratorPolynomial) hs
  have h0B:=integrable_momentPolynomialValue β hβ μ (momentDrift0 quotientDenominatorPolynomial) hs
  have h1B:=integrable_momentPolynomialValue β hβ μ (momentDrift1 quotientDenominatorPolynomial) hs
  unfold moment
  calc
    (∫sample,momentPolynomialValue β μ (gammaThirdPolynomial m) s sample
      ∂canonicalBrownianMeasure)=∫sample,
        momentPolynomialValue β μ (momentDrift0 quotientNumeratorPolynomial) s sample+
          m*momentPolynomialValue β μ (momentDrift1 quotientNumeratorPolynomial) s sample-
        2*m*(momentPolynomialValue β μ (momentDrift0 quotientDenominatorPolynomial) s sample+
          m*momentPolynomialValue β μ (momentDrift1 quotientDenominatorPolynomial) s sample)
          ∂canonicalBrownianMeasure := by
      apply integral_congr_ae
      exact .of_forall fun sample=>by
        unfold momentPolynomialValue
        dsimp only
        rw [eval_momentDrift0_quotientNumerator,eval_momentDrift1_quotientNumerator,
          eval_momentDrift0_quotientDenominator,eval_momentDrift1_quotientDenominator]
        simp only [gammaThirdPolynomial,map_add,map_sub,map_mul,map_pow,eval_C,eval_X]
        ring
    _=_ := by
      rw [integral_sub
        (f:=fun sample=>momentPolynomialValue β μ (momentDrift0 quotientNumeratorPolynomial) s sample+
          m*momentPolynomialValue β μ (momentDrift1 quotientNumeratorPolynomial) s sample)
        (g:=fun sample=>2*m*(momentPolynomialValue β μ (momentDrift0 quotientDenominatorPolynomial) s sample+
          m*momentPolynomialValue β μ (momentDrift1 quotientDenominatorPolynomial) s sample))
        (h0A.add (h1A.const_mul m)) ((h0B.add (h1B.const_mul m)).const_mul (2*m)),
        integral_add (f:=momentPolynomialValue β μ (momentDrift0 quotientNumeratorPolynomial) s)
          (g:=fun sample=>m*momentPolynomialValue β μ (momentDrift1 quotientNumeratorPolynomial) s sample)
          h0A (h1A.const_mul m),integral_const_mul,
        integral_const_mul,
        integral_add (f:=momentPolynomialValue β μ (momentDrift0 quotientDenominatorPolynomial) s)
          (g:=fun sample=>m*momentPolynomialValue β μ (momentDrift1 quotientDenominatorPolynomial) s sample)
          h0B (h1B.const_mul m),integral_const_mul]

 theorem hasDerivAt_GammaSecond_of_constant_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) {s:ℝ} (hs:s∈Ioo a b) :
    HasDerivAt (GammaSecond β μ) (GammaThird β μ m s) s := by
  have hA:=hasDerivAt_moment_of_constant_CDF β hβ μ m a b hI hCDF quotientNumeratorPolynomial hs
  have hB:=hasDerivAt_moment_of_constant_CDF β hβ μ m a b hI hCDF quotientDenominatorPolynomial hs
  have hd:=(hA.sub (hB.const_mul (2*m))).const_mul (β^4)
  have he:GammaSecond β μ =ᶠ[nhds s] fun t=>β^4*(quotientNumerator β μ t-
      2*m*quotientDenominator β μ t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact GammaSecond_eq_constant_mass β μ m a b hCDF ht
  have hv : GammaThird β μ m s=β^4*(
      β^2*(moment β μ (momentDrift0 quotientNumeratorPolynomial) s+
        m*moment β μ (momentDrift1 quotientNumeratorPolynomial) s)-
      (2*m)*(β^2*(moment β μ (momentDrift0 quotientDenominatorPolynomial) s+
        m*moment β μ (momentDrift1 quotientDenominatorPolynomial) s))) := by
    rw [GammaThird,gammaThird_generator_moment β hβ μ m ⟨(hI hs).1.le,(hI hs).2.le⟩]
    ring
  rw [hv]
  exact hd.congr_of_eventuallyEq he

 theorem contDiffOn_Gamma_of_constant_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) : ContDiffOn ℝ ∞ (Gamma β μ) (Ioo a b) := by
  have he:Gamma β μ=moment β μ (X 0^2):=funext fun s=>Gamma_eq_moment β μ s
  rw [he]
  exact contDiffOn_moment_of_constant_CDF β hβ μ m a b hI hCDF _

 theorem contDiffOn_Gamma_three_of_constant_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) : ContDiffOn ℝ 3 (Gamma β μ) (Ioo a b) :=
  (contDiffOn_Gamma_of_constant_CDF β hβ μ m a b hI hCDF).of_le (by simp)

 theorem hasDerivAt_deriv_Gamma_of_constant_CDF (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) {s:ℝ} (hs:s∈Ioo a b) :
    HasDerivAt (deriv (Gamma β μ)) (GammaSecond β μ s) s := by
  have he:deriv (Gamma β μ)=ᶠ[nhds s] GammaPrime β μ := by
    filter_upwards [isOpen_Ioo.mem_nhds (hI hs)] with t ht
    exact (hasDerivAt_Gamma_GammaPrime β hβ μ ht).deriv
  exact (hasDerivAt_GammaPrime_of_constant_CDF β hβ μ m a b hI hCDF hs).congr_of_eventuallyEq he

 theorem hasDerivAt_deriv_deriv_Gamma_of_constant_CDF (β:ℝ) (hβ:β≠0)
    (μ:ParisiMeasure) (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) {s:ℝ} (hs:s∈Ioo a b) :
    HasDerivAt (deriv (deriv (Gamma β μ))) (GammaThird β μ m s) s := by
  have he:deriv (deriv (Gamma β μ))=ᶠ[nhds s] GammaSecond β μ := by
    filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht
    exact (hasDerivAt_deriv_Gamma_of_constant_CDF β hβ μ m a b hI hCDF ht).deriv
  exact (hasDerivAt_GammaSecond_of_constant_CDF β hβ μ m a b hI hCDF hs).congr_of_eventuallyEq he

end FRSB
