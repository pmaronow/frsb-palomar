module

public import FRSB.ParisiMinimizer

@[expose] public section

/-! The new paper's literal ordered-pair SK model. Its independent Gaussian
couplings give exactly the overlap covariance, and its expected free energy
agrees with the previously checked increasing-pair model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology
namespace FRSB
open Paper
open SpinGlass.GeneralizedLatala

abbrev OrderedSKEdge (n : ℕ) := Fin n × Fin n

def orderedSKIndex {n : ℕ} (e : OrderedSKEdge n) : (ℕ × ℕ) ⊕ ℕ :=
  Sum.inl (e.1.val, e.2.val)

theorem orderedSKIndex_injective (n : ℕ) :
    Function.Injective (orderedSKIndex (n := n)) := by
  intro e f hef
  have he := Sum.inl.inj hef
  exact Prod.ext (Fin.ext (Prod.mk.inj he).1) (Fin.ext (Prod.mk.inj he).2)

/-- A fixed countable independent Gaussian probability space carries all sizes. -/
def orderedSKCoupling (n : ℕ) (e : OrderedSKEdge n) (ω : PhysicalSKGaussianSpace) : ℝ :=
  ω (orderedSKIndex e)

theorem measurable_orderedSKCoupling (n : ℕ) (e : OrderedSKEdge n) :
    Measurable (orderedSKCoupling n e) := measurable_pi_apply _

theorem orderedSKCoupling_law (n : ℕ) (e : OrderedSKEdge n) :
    (volume : Measure PhysicalSKGaussianSpace).map (orderedSKCoupling n e) = gaussianReal 0 1 :=
  (measurePreserving_eval_infinitePi (fun _ : (ℕ × ℕ) ⊕ ℕ => gaussianReal 0 1)
    (orderedSKIndex e)).map_eq

theorem orderedSKCoupling_independent (n : ℕ) :
    iIndepFun (orderedSKCoupling n) (volume : Measure PhysicalSKGaussianSpace) := by
  have hI : iIndepFun
      (fun k : (ℕ × ℕ) ⊕ ℕ => fun ω : PhysicalSKGaussianSpace => ω k)
      (volume : Measure PhysicalSKGaussianSpace) :=
    iIndepFun_infinitePi (X := fun _ x => x) (by fun_prop)
  exact iIndepFun.precomp (g := orderedSKIndex) (orderedSKIndex_injective n) hI

/-- The finite family has exactly the product standard Gaussian distribution. -/
theorem orderedSKCoupling_joint_law (n : ℕ) :
    (volume : Measure PhysicalSKGaussianSpace).map (fun ω e => orderedSKCoupling n e ω) =
      Measure.pi (fun _ : OrderedSKEdge n => gaussianReal 0 1) := by
  simpa only [orderedSKCoupling_law] using
    (orderedSKCoupling_independent n).map_fun_eq_pi_map
      (fun e => (measurable_orderedSKCoupling n e).aemeasurable)

def orderedSKCoefficient (n : ℕ) (β : ℝ) (σ : SKConfiguration n)
    (e : OrderedSKEdge n) : ℝ :=
  β / Real.sqrt (2 * (n : ℝ)) * spinSign (σ e.1) * spinSign (σ e.2)

/-- Literal ordered-pair Hamiltonian, including all diagonal terms. -/
def orderedSKHamiltonian (n : ℕ) (β : ℝ) (ω : PhysicalSKGaussianSpace)
    (σ : SKConfiguration n) : ℝ :=
  β / Real.sqrt (2 * (n : ℝ)) *
    ∑ e : OrderedSKEdge n, orderedSKCoupling n e ω * spinSign (σ e.1) * spinSign (σ e.2)

/-- The paper's finite expected free energy, at zero field. -/
def orderedSKFreeEnergy (β : ℝ) (n : ℕ) : ℝ :=
  (1 / (n : ℝ)) * ∫ ω : PhysicalSKGaussianSpace,
    Real.log (∑ σ : SKConfiguration n, Real.exp (orderedSKHamiltonian n β ω σ))

/-- All ordered pairs yield the exact SK covariance without a correction. -/
theorem orderedSKCoefficient_covariance (n : ℕ) (β : ℝ) (σ τ : SKConfiguration n) :
    (∑ e, orderedSKCoefficient n β σ e * orderedSKCoefficient n β τ e) =
      SpinGlass.sk_cov_kernel n β σ τ := by
  classical
  by_cases hn : n = 0
  · subst n
    simp [SpinGlass.sk_cov_kernel, SpinGlass.overlap]
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hnnonneg : 0 ≤ 2 * (n : ℝ) := by positivity
  let x : Fin n → ℝ := fun i => spinSign (σ i) * spinSign (τ i)
  have hterm (e : OrderedSKEdge n) :
      orderedSKCoefficient n β σ e * orderedSKCoefficient n β τ e =
        (β / Real.sqrt (2 * (n : ℝ))) ^ 2 * (x e.1 * x e.2) := by
    unfold orderedSKCoefficient x
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, Fintype.sum_prod_type, ← Finset.sum_mul_sum, ← pow_two,
    div_pow, Real.sq_sqrt hnnonneg]
  simp only [SpinGlass.sk_cov_kernel, SpinGlass.overlap, SpinGlass.spin]
  change β ^ 2 / (2 * (n : ℝ)) * (∑ i, x i) ^ 2 =
    (n : ℝ) * β ^ 2 / 2 * ((1 / (n : ℝ)) * ∑ i, x i) ^ 2
  field_simp [hnr]

def orderedSKGaussian (n : ℕ) (β : ℝ) :
    PhysLean.Probability.GaussianIBP.IsGaussianHilbert
      (gaussianCoordinateEnergy n (orderedSKCoupling n) (orderedSKCoefficient n β)) := by
  let Y : PhysicalSKGaussianSpace → (OrderedSKEdge n → ℝ) :=
    fun ω e => orderedSKCoupling n e ω
  have hYg : HasGaussianLaw Y (volume : Measure PhysicalSKGaussianSpace) :=
    (orderedSKCoupling_independent n).hasGaussianLaw fun e =>
      standardGaussianCoordinate_gaussian _ _ (measurable_orderedSKCoupling n e)
        (orderedSKCoupling_law n e)
  have hY0 : (∫ ω, Y ω ∂(volume : Measure PhysicalSKGaussianSpace)) = 0 := by
    ext e
    rw [eval_integral (fun j => hYg.integrable.eval j)]
    exact standardGaussianCoordinate_mean _ _ (measurable_orderedSKCoupling n e)
      (orderedSKCoupling_law n e)
  apply PhysLean.Probability.GaussianIBP.IsGaussianHilbert.of_hasGaussianLaw
    (gaussianCoordinateEnergy n (orderedSKCoupling n) (orderedSKCoefficient n β))
  · exact (gaussianEnergyLinearMap n (orderedSKCoefficient n β)).measurable.comp
      (measurable_pi_iff.mpr (measurable_orderedSKCoupling n))
  · exact hYg.map (gaussianEnergyLinearMap n (orderedSKCoefficient n β))
  · change (∫ ω, gaussianEnergyLinearMap n (orderedSKCoefficient n β) (Y ω)) = 0
    rw [(gaussianEnergyLinearMap n (orderedSKCoefficient n β)).integral_comp_comm
      hYg.integrable, hY0]
    simp

/-- An actual Gaussian disorder satisfies the exact imported SK hypotheses. -/
def orderedSKDisorder (n : ℕ) (β : ℝ) :
    SpinGlass.SKDisorder (Ω := PhysicalSKGaussianSpace) n β 0 := by
  let hG := orderedSKGaussian n β
  refine ⟨gaussianCoordinateEnergy n (orderedSKCoupling n) (orderedSKCoefficient n β), hG, ?_⟩
  intro σ τ
  rw [← gaussianHilbert_eval_pairing]
  change (∫ ω, (∑ e, orderedSKCoefficient n β σ e * orderedSKCoupling n e ω) *
      (∑ e, orderedSKCoefficient n β τ e * orderedSKCoupling n e ω)) = _
  rw [independent_standardGaussian_linear_covariance (orderedSKCoupling n)
    (measurable_orderedSKCoupling n) (orderedSKCoupling_law n) (orderedSKCoupling_independent n)]
  exact orderedSKCoefficient_covariance n β σ τ

@[simp] theorem orderedSKDisorder_U (n : ℕ) (β : ℝ) (ω : PhysicalSKGaussianSpace)
    (σ : SKConfiguration n) : (orderedSKDisorder n β).U ω σ =
      orderedSKHamiltonian n β ω σ := by
  change (∑ e, orderedSKCoefficient n β σ e * orderedSKCoupling n e ω) = _
  unfold orderedSKHamiltonian orderedSKCoefficient
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- Any two centered Gaussian SK disorders have the same actual vector law. -/
theorem skDisorder_law_eq {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (volume : Measure Ω)] [IsProbabilityMeasure (volume : Measure Ω')]
    (n : ℕ) (β h : ℝ) (sk : SpinGlass.SKDisorder (Ω := Ω) n β h)
    (sk' : SpinGlass.SKDisorder (Ω := Ω') n β h) :
    Measure.map sk.U (volume : Measure Ω) = Measure.map sk'.U (volume : Measure Ω') := by
  let μ := Measure.map sk.U (volume : Measure Ω)
  let ν := Measure.map sk'.U (volume : Measure Ω')
  have hg := gaussianHilbert_hasGaussianLaw sk.hU
  have hg' := gaussianHilbert_hasGaussianLaw sk'.hU
  let : IsGaussian μ := hg.isGaussian_map
  let : IsGaussian ν := hg'.isGaussian_map
  have hmatrix (σ τ : SKConfiguration n) :
      covarianceBilin μ (SpinGlass.std_basis n σ) (SpinGlass.std_basis n τ) =
        covarianceBilin ν (SpinGlass.std_basis n σ) (SpinGlass.std_basis n τ) := by
    simp only [μ, ν]
    rw [covarianceBilin_apply hg.isGaussian_map.memLp_two_id,
      covarianceBilin_apply hg'.isGaussian_map.memLp_two_id,
      map_gaussian_mean_zero n sk.U sk.hU, map_gaussian_mean_zero n sk'.U sk'.hU]
    simp only [sub_zero]
    rw [integral_map hg.aemeasurable, integral_map hg'.aemeasurable]
    · simpa [SpinGlass.inner_std_basis_apply, real_inner_comm] using
        (gaussianHilbert_eval_pairing n sk.U sk.hU σ τ).trans
          (((sk.cov_eq σ τ).trans (sk'.cov_eq σ τ).symm).trans
            (gaussianHilbert_eval_pairing n sk'.U sk'.hU σ τ).symm)
    · fun_prop
    · fun_prop
  apply ProbabilityTheory.IsGaussian.ext
  · simpa [μ, ν] using (map_gaussian_mean_zero n sk.U sk.hU).trans
      (map_gaussian_mean_zero n sk'.U sk'.hU).symm
  · apply ContinuousLinearMap.ext
    intro x
    apply ContinuousLinearMap.ext
    intro y
    calc
      covarianceBilin μ x y = ∑ σ, ∑ τ, x σ * y τ *
          covarianceBilin μ (SpinGlass.std_basis n σ) (SpinGlass.std_basis n τ) :=
        bilin_eq_sum_std n (covarianceBilin μ) x y
      _ = ∑ σ, ∑ τ, x σ * y τ *
          covarianceBilin ν (SpinGlass.std_basis n σ) (SpinGlass.std_basis n τ) := by
        simp_rw [hmatrix]
      _ = covarianceBilin ν x y := (bilin_eq_sum_std n (covarianceBilin ν) x y).symm

/-- Identical disorder laws give identical quenched free entropy. -/
theorem skDisorder_freeEntropy_eq {Ω Ω' : Type*} [MeasureSpace Ω] [MeasureSpace Ω']
    [IsProbabilityMeasure (volume : Measure Ω)] [IsProbabilityMeasure (volume : Measure Ω')]
    (n : ℕ) (β h : ℝ) (sk : SpinGlass.SKDisorder (Ω := Ω) n β h)
    (sk' : SpinGlass.SKDisorder (Ω := Ω') n β h) :
    SpinGlass.free_entropy (Ω := Ω) (N := n) (β := β) (h := h) sk.U =
      SpinGlass.free_entropy (Ω := Ω') (N := n) (β := β) (h := h) sk'.U := by
  let F : SpinGlass.EnergySpace n → ℝ := fun u =>
    SpinGlass.free_energy_density n (SpinGlass.skEnergy (β := β) (h := h) u)
  have hF : Measurable F := by
    apply (SpinGlass.contDiff_free_energy_density n).continuous.measurable.comp
    unfold SpinGlass.skEnergy
    fun_prop
  have hg := gaussianHilbert_hasGaussianLaw sk.hU
  have hg' := gaussianHilbert_hasGaussianLaw sk'.hU
  unfold SpinGlass.free_entropy
  change (∫ ω, F (sk.U ω)) = ∫ ω, F (sk'.U ω)
  rw [← integral_map hg.aemeasurable hF.aestronglyMeasurable,
    skDisorder_law_eq n β h sk sk', integral_map hg'.aemeasurable hF.aestronglyMeasurable]

/-- The abstract exact-covariance model is precisely the literal paper model. -/
theorem orderedSKDisorder_freeEntropy_eq (n : ℕ) (β : ℝ) :
    SpinGlass.free_entropy (Ω := PhysicalSKGaussianSpace) (N := n) (β := β) (h := 0)
      (orderedSKDisorder n β).U = orderedSKFreeEnergy β n := by
  unfold SpinGlass.free_entropy SpinGlass.free_energy_density orderedSKFreeEnergy
  change (∫ ω : PhysicalSKGaussianSpace, (1 / (n : ℝ)) *
    Real.log (SpinGlass.skZ (β := β) (h := 0) ((orderedSKDisorder n β).U ω))) = _
  rw [integral_const_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun ω => by
    change Real.log (SpinGlass.skZ (β := β) (h := 0) ((orderedSKDisorder n β).U ω)) = _
    rw [SpinGlass.skZ_eq]
    simp only [zero_mul, add_zero, orderedSKDisorder_U]

/-- The logarithmic expectation defining the ordered model is genuinely integrable. -/
theorem integrable_orderedSK_logPartition (n : ℕ) (β : ℝ) :
    Integrable (fun ω : PhysicalSKGaussianSpace =>
      Real.log (∑ σ : SKConfiguration n, Real.exp (orderedSKHamiltonian n β ω σ)))
      (volume : Measure PhysicalSKGaussianSpace) := by
  have hh := SpinGlass.integrable_log_skZ β 0 (orderedSKDisorder n β)
  simpa only [SpinGlass.skZ_eq, zero_mul, add_zero, orderedSKDisorder_U] using hh

/-- Ordered pairs and increasing pairs have exactly equal expected free energies. -/
theorem orderedSKFreeEnergy_eq_physical (β : ℝ) (n : ℕ) :
    orderedSKFreeEnergy β n = finiteSKFreeEnergy β 0 n := by
  calc
    _ = SpinGlass.free_entropy (Ω := PhysicalSKGaussianSpace) (N := n) (β := β) (h := 0)
      (orderedSKDisorder n β).U := (orderedSKDisorder_freeEntropy_eq n β).symm
    _ = SpinGlass.free_entropy (Ω := PhysicalSKGaussianSpace) (N := n) (β := β) (h := 0)
      (physicalTalagrandDisorder n β 0).U :=
      skDisorder_freeEntropy_eq n β 0 (orderedSKDisorder n β) (physicalTalagrandDisorder n β 0)
    _ = _ := physicalTalagrandDisorder_freeEntropy_eq n β 0

/-- The literal ordered-pair model converges to the actual PDE variational value. -/
theorem orderedSK_parisiFormula (β : ℝ) (hβ : 0 < β) :
    Tendsto (orderedSKFreeEnergy β) atTop (𝓝 (parisiPDEValue β 0)) := by
  have he : orderedSKFreeEnergy β = finiteSKFreeEnergy β 0 :=
    funext (orderedSKFreeEnergy_eq_physical β)
  rw [he]
  exact physicalParisiFormula β 0 hβ

/-- The limit is attained by the constructed actual minimizing measure. -/
theorem orderedSK_tendsto_minimizer (β : ℝ) (hβ : 0 < β) :
    Tendsto (orderedSKFreeEnergy β) atTop
      (𝓝 (parisiPDEFunctional β 0 (parisiMinimizer β 0))) := by
  rw [parisiMinimizer_value]
  exact orderedSK_parisiFormula β hβ

end FRSB
