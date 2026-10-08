module

public import FRSB.Main
public import FRSB.PDERegularity
public import FRSB.MeasureApproximation
public import FRSB.DiffusionApproximation
public import FRSB.PolynomialMomentConvergence
public import FRSB.ConstantMassEvolution
public import FRSB.ConstantMassDensityLaw
public import FRSB.StoppedOptimalProcess
public import FRSB.MStochasticL2
public import FRSB.GammaIdentity
public import FRSB.GammaPrime
public import FRSB.CurvatureIdentity
public import FRSB.GammaHigher
public import FRSB.GammaSecond
public import FRSB.PolynomialMomentContinuity
public import FRSB.PolynomialMomentIdentity
public import FRSB.Optimality
public import FRSB.ComparisonBounded
public import FRSB.BackwardsProposition
public import FRSB.BackwardsBounded
public import FRSB.BackwardsLower
public import FRSB.BackwardsSmooth
public import FRSB.BackwardsMagnetizationRemark
public import FRSB.BackwardsSusceptibilitySigns
public import FRSB.BackwardsSlopeTime
public import FRSB.BackwardsRelativeGlobal
public import FRSB.BackwardsRelativeFields
public import FRSB.BackwardsConstantEquations
public import FRSB.BackwardsActualAtoms
public import FRSB.BackwardsJets
public import FRSB.BackwardsTerminal
public import FRSB.ForwardProposition
public import FRSB.ForwardApproximationEverySequence
public import FRSB.ForwardBridgeApproximation
public import FRSB.ForwardConclusions
public import FRSB.CrossingProposition
public import FRSB.CrossingPositiveRepresentation
public import FRSB.CrossingTransportBundle
public import FRSB.CrossMagnetizationRemark
public import FRSB.CrossingDecayBundle
public import FRSB.CrossingActualMonotonicity
public import FRSB.CrossingActualForwardMonotonicity
public import FRSB.FullSupport
public import FRSB.MinimizerConclusions
public import FRSB.CrossingOpenInterval

@[expose] public section

/-! Numbered paper statement correspondence. Each target has a closed proof;
several targets include broader parameter domains or auxiliary conclusions.
COVERAGE.md records those differences and separately mapped parts of remarks.
The cited mixed-model history in Remark 6.4 is recorded as background in the ledger. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper StochasticCalculus SignType
open scoped NNReal ENNReal Topology ContDiff BigOperators
namespace FRSB.Numbered

/-- Paper 1.1. -/
def Statement_1_1 : Prop :=
  ∀ β : ℝ, 1 < β → FullRSBMeasure β (parisiMinimizer β 0)

theorem result_1_1 : Statement_1_1 := @fullRSB

/-- Paper 1.2. -/
def Statement_1_2 : Prop :=
  QuantitativeAtomTarget

theorem result_1_2 : Statement_1_2 := @quantitative_atom

/-- Paper 2.1. -/
def Statement_2_1 : Prop :=
  ∀ (β : ℝ),
    PDERegularityTarget β

theorem result_2_1 : Statement_2_1 := @pde_regularity

/-- Paper 2.2. -/
def Statement_2_2 : Prop :=
  ∀ (μ : ParisiMeasure) (S : Set Overlap)
    (hS : S.Finite),
    ∃ μn : ℕ → ParisiMeasure,
      (∀ n, (μn n : Measure Overlap).support.Finite) ∧
      Tendsto μn atTop (𝓝 μ) ∧
      (∀ s ∈ S, ∀ n,
        (μn n : Measure Overlap) (Iio s) = (μ : Measure Overlap) (Iio s) ∧
        (μn n : Measure Overlap) {s} = (μ : Measure Overlap) {s}) ∧
      Tendsto (fun n => parisiCDFDistance (μn n) μ) atTop (𝓝 0)

theorem result_2_2 : Statement_2_2 := @exists_preservingApproximation

/-- Paper 2.3. -/
def Statement_2_3 : Prop :=
  (∀ (β : ℝ) (μ ν : ParisiMeasure) (sample : BrownianSample)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1),
    ‖optimalStateReal β μ sample t - optimalStateReal β ν sample t‖ ≤
      β ^ 2 * Real.exp (β ^ 2) *
        (‖Paper.parisiGradientBCF β μ - Paper.parisiGradientBCF β ν‖ +
          Paper.parisiCDFDistance μ ν)) ∧
  (∀ {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (μs : ι → ParisiMeasure) (μ : ParisiMeasure)
    (hμ : Tendsto μs L (nhds μ)),
    ∀ ε > 0, ∀ᶠ i in L, ∀ sample : BrownianSample, ∀ t ∈ Icc (0 : ℝ) 1,
      ‖optimalStateReal β (μs i) sample t - optimalStateReal β μ sample t‖ < ε) ∧
  (∀ {ι : Type*} {L : Filter ι}
    [L.IsCountablyGenerated] (β : ℝ) (hβ : β ≠ 0) (ν : ι → ParisiMeasure)
    (μ : ParisiMeasure) (hμ : Tendsto ν L (nhds μ)) (f : MomentPolynomial),
    TendstoUniformlyOn (fun i => moment β (ν i) f) (moment β μ f) L (Icc (0 : ℝ) 1))

theorem result_2_3 : Statement_2_3 := ⟨@optimalState_dist_le,@optimalState_uniform_convergence_of_weak,@tendstoUniformlyOn_moment_of_weak⟩

/-- Paper 2.4. -/
def Statement_2_4 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hm : 0 < m) (hc : ∀ s ∈ Ico a b, parisiCDF μ s = m)
    {r t : ℝ} (hr : r ∈ Icc a b) (ht : t ∈ Icc r b) (x : ℝ),
    Real.exp (m * parisiPotential β μ (r, x)) =
      Paper.heatSemigroup (β ^ 2 * (t - r)) (fun y => Real.exp (m * parisiPotential β μ (t, y))) x) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ico a b, parisiCDF μ s = 0)
    {r t : ℝ} (hr : r ∈ Icc a b) (ht : t ∈ Icc r b) (x : ℝ),
    parisiPotential β μ (r, x) =
      Paper.heatSemigroup (β ^ 2 * (t - r)) (fun y => parisiPotential β μ (t, y)) x) ∧
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m),
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ t.toNNReal)=
      volume.withDensity (fun x=>ENNReal.ofReal (constantMassDensityFromLaw β μ r t m
        (canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)) x))) ∧
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (r t:ℝ) (hr:0≤r) (hrt:r<t) (ht:t≤1) (m:ℝ)
    (hc:∀s∈Ico r t,parisiCDF μ s=m) (x:ℝ),
    forwardBridgeDensity β μ t ⟨hr.trans_lt hrt,ht⟩ x=
      Real.exp (m*parisiPotential β μ (t,x))*
        ∫y,heatDensity (β^2*(t-r)) (x-y)*Real.exp (-m*parisiPotential β μ (r,y))
          ∂(canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ r.toNNReal)))

theorem result_2_4 : Statement_2_4 := ⟨@parisiPotential_exp_heat_on_constant_interval,@parisiPotential_heat_on_zeroCDF_interval,@selectedState_endpoint_eq_constantMassDensityLaw,@forwardBridgeDensity_constantMass_initialLaw_formula⟩

/-- Paper 2.5. -/
def Statement_2_5 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure),
    Martingale (stoppedMagnetization β hβ μ) canonicalBrownianFiltration canonicalBrownianMeasure) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (t : ℝ≥0) (sample : BrownianSample),
    ‖stoppedMagnetization β hβ μ t sample‖ ≤ 1) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (T : ℝ≥0) (hT : T ≤ 1),
    TendstoInMeasure canonicalBrownianMeasure (optimalMLeftSum β hβ μ T) atTop
      (M β μ T)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure),
    ContDiffOn ℝ 1 (Gamma β μ) (Icc (0:ℝ) 1)) ∧
  (∀ (β : ℝ) (hβ : β≠0)
    (μ : ParisiMeasure) {t : ℝ} (ht:t∈Icc (0:ℝ) 1),
    HasDerivWithinAt (Gamma β μ) (GammaPrime β μ t) (Icc (0:ℝ) 1) t) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hrt : r ≤ t),
    GammaPrime β μ t-GammaPrime β μ r =
      β^4*∫s in r..t,∫sample,D β μ s sample ^ 2-2*parisiCDF μ s*C β μ s sample ^ 3
        ∂canonicalBrownianMeasure) ∧
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m),
    ContDiffOn ℝ 3 (Gamma β μ) (Ioo a b)) ∧
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {s:ℝ} (hs:s∈Icc (0:ℝ) 1),
    GammaSecond β μ s=β^4*(∫ sample, D β μ s sample ^ 2-2*parisiCDF μ s*C β μ s sample ^ 3
      ∂canonicalBrownianMeasure)) ∧
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) {s:ℝ} (hs:s∈Ioo a b),
    HasDerivAt (deriv (Gamma β μ)) (GammaSecond β μ s) s) ∧
  (∀ (β:ℝ) (hβ:β≠0)
    (μ:ParisiMeasure) (m a b:ℝ) (hI:Ioo a b⊆Ioo (0:ℝ) 1)
    (hCDF:∀t∈Ioo a b,parisiCDF μ t=m) {s:ℝ} (hs:s∈Ioo a b),
    HasDerivAt (deriv (deriv (Gamma β μ))) (GammaThird β μ m s) s) ∧
  (∀ (β:ℝ) (μ:ParisiMeasure) (m s:ℝ),
    GammaThird β μ m s=β^6*(∫sample,A β μ s sample^2-
      12*m*C β μ s sample*D β μ s sample^2+6*m^2*C β μ s sample^4
      ∂canonicalBrownianMeasure)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial),
    ContinuousOn (moment β μ f) (Icc (0 : ℝ) 1)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (f : MomentPolynomial) {r t : ℝ} (hr : r ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1),
    moment β μ f t-moment β μ f r = β^2*∫s in r..t,
      moment β μ (momentDrift0 f) s+parisiCDF μ s*moment β μ (momentDrift1 f) s)

theorem result_2_5 : Statement_2_5 := ⟨@martingale_stoppedMagnetization,@norm_stoppedMagnetization_le_one,@optimalM_stochastic_identity,@contDiffOn_Gamma_one,@hasDerivWithinAt_Gamma_GammaPrime,@GammaPrime_interval_integral,@contDiffOn_Gamma_three_of_constant_CDF,@GammaSecond_eq_integral,@hasDerivAt_deriv_Gamma_of_constant_CDF,@hasDerivAt_deriv_deriv_Gamma_of_constant_CDF,@GammaThird_eq_integral,@continuousOn_moment,@moment_interval_integral_physical⟩

/-- Paper 2.6. -/
def Statement_2_6 : Prop :=
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (hmin:∀ν:ParisiMeasure,parisiPDEFunctional β 0 μ≤parisiPDEFunctional β 0 ν)
    (q:Overlap) (hq:q∈(μ:Measure Overlap).support),
    Gamma β μ q=(q:ℝ)) ∧
  (∀ (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (hmin:∀ν:ParisiMeasure,parisiPDEFunctional β 0 μ≤parisiPDEFunctional β 0 ν)
    (q:Overlap) (hq:q∈(μ:Measure Overlap).support),
    GammaPrime β μ q≤1)

theorem result_2_6 : Statement_2_6 := ⟨@Gamma_eq_overlap_of_support,@GammaPrime_le_one_of_support⟩

/-- Paper 2.7. -/
def Statement_2_7 : Prop :=
  ∀ (halfLine : Bool)
    (T K M : ℝ) (hT : 0 ≤ T) (hK : 0 ≤ K) (hM : 0 ≤ M)
    (v vt b κ : ℝ × ℝ → ℝ)
    (hv : ContinuousOn v (Icc 0 T ×ˢ comparisonSpace halfLine))
    (ht : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      HasDerivWithinAt (fun s => v (s, x)) (vt (t, x)) (Icc 0 T) t)
    (hx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (fun y => v (t, y)) x)
    (hxx : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      DifferentiableAt ℝ (deriv (fun y => v (t, y))) x)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T, ∀ x ∈ comparisonSpace halfLine, |v (t, x)| ≤ M)
    (hb : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      b (t, x) * sign x ≤ K)
    (hκ : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine, κ (t, x) ≤ K)
    (hPDE : ∀ t ∈ Ioc (0 : ℝ) T, ∀ x ∈ comparisonSpaceInterior halfLine,
      0 ≤ vt (t, x) - (1 / 2 : ℝ) * deriv (deriv (fun y => v (t, y))) x -
        b (t, x) * deriv (fun y => v (t, y)) x - κ (t, x) * v (t, x))
    (hinitial : ∀ x ∈ comparisonSpace halfLine, 0 ≤ v (0, x))
    (hboundary : halfLine = true → ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ v (t, 0)),
    ∀ p ∈ Icc 0 T ×ˢ comparisonSpace halfLine, 0 ≤ v p

theorem result_2_7 : Statement_2_7 := @bounded_supersolution_nonneg

/-- Paper 3.1. -/
def Statement_3_1 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x),
    Paper.parisiCDF μ t*backwardB β μ (t,x) ≤ backwardZ β μ (t,x) ∧
    backwardZ β μ (t,x) ≤ Paper.parisiCDF μ t*backwardB β μ (t,x)+1-Paper.parisiCDF μ t ∧
    Paper.parisiCDF μ t*backwardB β μ (t,x)+1-Paper.parisiCDF μ t ≤ 1 ∧
    0 ≤ backwardQ β μ (Paper.parisiCDF μ t) (t,x) ∧
    backwardQ β μ (Paper.parisiCDF μ t) (t,x) ≤ 1-Paper.parisiCDF μ t ∧
    0 ≤ backwardHx β μ (Paper.parisiCDF μ t) (t,x) ∧
    backwardHx β μ (Paper.parisiCDF μ t) (t,x) ≤ 6*(1-Paper.parisiCDF μ t)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
    |backwardZ β μ (t,x)| ≤ 1 ∧ |backwardQ β μ (Paper.parisiCDF μ t) (t,x)| ≤ 1 ∧
    |backwardH β μ (Paper.parisiCDF μ t) (t,x)| ≤ 2 ∧
    |backwardHx β μ (Paper.parisiCDF μ t) (t,x)| ≤ 6 ∧
    |backwardC β μ (t,x)*backwardHx β μ (Paper.parisiCDF μ t) (t,x)| ≤ 6) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (t x : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) (hx : 0 ≤ x),
    backwardD β μ 3 (t,x) ≤ 0) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1),
    ContDiff ℝ ∞ (fun x => backwardZ β μ (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardZx β μ (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardZxx β μ (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardQ β μ a (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardH β μ a (t,x)) ∧
    ContDiff ℝ ∞ (fun x => backwardHx β μ a (t,x)))

theorem result_3_1 : Statement_3_1 := ⟨@backward_inequalities,@backward_fields_bounded,@backwardD_three_nonpos,@backward_fields_smooth⟩

/-- Paper 3.2. -/
def Statement_3_2 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ioo a b, parisiCDF μ s = m) {τ v : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1),
    deriv (fun r => backwardMagnetizationInverse β μ r v) τ =
      backwardTauZ β μ (τ,backwardMagnetizationInverse β μ τ v) - m*v ∧
    deriv (fun r => backwardChi β μ r v) τ =
      backwardChi β μ τ v^2 * (deriv (deriv (backwardChi β μ τ)) v / 2 + m) ∧
    deriv (fun r => Real.log (backwardChi β μ r v)) τ =
      -backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v) ∧
    deriv (fun b => deriv (fun r => Real.sqrt (backwardChi β μ r b)) τ) v =
      backwardHx β μ m (backwardTime β τ,backwardMagnetizationInverse β μ τ v) /
        (4 * Real.sqrt (backwardChi β μ τ v)) ∧
    deriv (backwardChi β μ τ) v =
      -2 * backwardTauZ β μ (τ,backwardMagnetizationInverse β μ τ v) ∧
    backwardTauQ β μ m (τ,backwardMagnetizationInverse β μ τ v) =
      -backwardChi β μ τ v * (deriv (deriv (backwardChi β μ τ)) v / 2 + m)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ioo a b, parisiCDF μ s = m) (v : ℝ)
    (hv : v ∈ Ioo (-1 : ℝ) 1) (hv0 : 0 ≤ v),
    MonotoneOn (fun r => backwardMagnetizationInverse β μ r v)
      (Ioo (β^2*(1-b)) (β^2*(1-a)))) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ioo a b, parisiCDF μ s = m) (v : ℝ) (hv : v ∈ Ioo (-1 : ℝ) 1),
    AntitoneOn (fun r => backwardChi β μ r v) (Ioo (β^2*(1-b)) (β^2*(1-a)))) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ioo a b, parisiCDF μ s = m) (v : ℝ)
    (hv : v ∈ Ioo (-1 : ℝ) 1) (hv0 : 0 ≤ v),
    MonotoneOn (fun r => deriv (fun b => Real.sqrt (backwardChi β μ r b)) v)
      (Ioo (β^2*(1-b)) (β^2*(1-a))))

theorem result_3_2 : Statement_3_2 := ⟨(fun β hβ μ a b m ha hab hb hc τ v hτ hv => @backward_magnetization_identities β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) τ v hτ hv),(fun β hβ μ a b m ha hab hb hc v hv hv0 => @backwardMagnetizationInverse_monotoneOn_constantCDF β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) v hv hv0),(fun β hβ μ a b m ha hab hb hc v hv => @backwardChi_antitoneOn_constantCDF β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) v hv),(fun β hβ μ a b m ha hab hb hc v hv hv0 => @sqrt_backwardChi_slope_monotoneOn_constantCDF β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) v hv hv0)⟩

/-- Paper 3.3. -/
def Statement_3_3 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0),
    ∃ K > 0, ∀ (μ : Paper.ParisiMeasure) (t x : ℝ), t ∈ Icc (0 : ℝ) 1 →
      ∀ j ∈ Finset.Icc 2 5, |iteratedDeriv j (fun y => Paper.parisiPotential β μ (t,y)) x| ≤
        K*backwardC β μ (t,x)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0),
    ∃ L > 0, ∀ (μ : Paper.ParisiMeasure) (a t x : ℝ), a ∈ Icc (0 : ℝ) 1 → t ∈ Icc (0 : ℝ) 1 →
      |backwardZ β μ (t,x)| ≤ L ∧ |backwardZx β μ (t,x)| ≤ L ∧
      |backwardZxx β μ (t,x)| ≤ L ∧ |backwardQ β μ a (t,x)| ≤ L ∧
      |backwardH β μ a (t,x)| ≤ L ∧ |backwardHx β μ a (t,x)| ≤ L)

theorem result_3_3 : Statement_3_3 := ⟨@relative_derivative_bounds,@relative_fields_bounded⟩

/-- Paper 3.4. -/
def Statement_3_4 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ioo a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ),
    deriv (fun r => backwardTauP β μ m (r, x)) τ -
      deriv (deriv (fun y => backwardTauP β μ m (τ, y))) x / 2 -
      m * backwardTauD β μ 1 (τ, x) *
        deriv (fun y => backwardTauP β μ m (τ, y)) x =
      -2 * backwardTauQ β μ m (τ, x) *
        backwardTauP β μ m (τ, x)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ioo a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ),
    deriv (fun r => backwardTauZ β μ (r, x)) τ -
      deriv (deriv (fun y => backwardTauZ β μ (τ, y))) x / 2 -
      m * backwardTauD β μ 1 (τ, x) *
        deriv (fun y => backwardTauZ β μ (τ, y)) x =
      -2 * backwardTauQ β μ m (τ, x) *
        backwardTauZ β μ (τ, x)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ r ∈ Ioo a b, Paper.parisiCDF μ r = m) {τ : ℝ}
    (hτ : backwardTime β τ ∈ Ioo a b) (x : ℝ),
    deriv (fun r => backwardTauR β μ m (r, x)) τ -
      deriv (deriv (fun y => backwardTauR β μ m (τ, y))) x / 2 -
      m * backwardTauD β μ 1 (τ, x) *
        deriv (fun y => backwardTauR β μ m (τ, y)) x =
      -5 * backwardTauQ β μ m (τ, x) *
        backwardTauR β μ m (τ, x) +
      6 * backwardTauD β μ 2 (τ, x) *
        backwardTauZ β μ (τ, x) *
        backwardTauQ β μ m (τ, x) ^ 2) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (t : ℝ) (ht : t ∈ Ioc (0 : ℝ) 1) (x : ℝ),
    backwardC β μ (t,x) * backwardQ β μ (parisiLeftMass μ t) (t,x) =
      backwardC β μ (t,x) * backwardQ β μ (parisiCDF μ t) (t,x) +
        parisiAtomMass μ t ht * backwardC β μ (t,x)^2 ∧
    backwardC β μ (t,x) * backwardHx β μ (parisiLeftMass μ t) (t,x) =
      backwardC β μ (t,x) * backwardHx β μ (parisiCDF μ t) (t,x) +
        6 * parisiAtomMass μ t ht * backwardC β μ (t,x)^2 * backwardZ β μ (t,x)) ∧
  (∀ (m δ C D E F : ℝ) (hC : C ≠ 0),
    C * backwardQJet (m - δ) C D E = C * backwardQJet m C D E + δ * C ^ 2 ∧
    backwardZJet C D = backwardZJet C D ∧
    C * backwardHxJet (m - δ) C D E F =
      C * backwardHxJet m C D E F + 6 * δ * C ^ 2 * backwardZJet C D) ∧
  (∀ (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ),
    backwardZ β μ (1, x) = Real.tanh x) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (x : ℝ),
    backwardQ β μ 1 (1, x) = 0) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (x : ℝ),
    backwardHx β μ 1 (1, x) = 0)

theorem result_3_4 : Statement_3_4 := ⟨(fun β hβ μ a b m ha hab hb hc τ hτ x => @constantCDF_backward_weightedQ_equation β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) τ hτ x),(fun β hβ μ a b m ha hab hb hc τ hτ x => @constantCDF_backward_z_equation β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) τ hτ x),(fun β hβ μ a b m ha hab hb hc τ hτ x => @constantCDF_backward_weightedHx_equation β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) τ hτ x),@backward_actual_atom_updates,@backward_atom_updates,@backwardZ_terminal,@backwardQ_terminal,@backwardHx_terminal⟩

/-- Paper 4.1. -/
def Statement_4_1 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1),
    canonicalBrownianMeasure.map (selectedParisiItoState β 0 hβ μ s.toNNReal) =
      volume.withDensity (fun x => ENNReal.ofReal (forwardBridgeDensity β μ s hs x)) ∧
    ContDiff ℝ ∞ (forwardBridgeDensity β μ s hs) ∧
    (∀ x, 0 < forwardBridgeDensity β μ s hs x ∧
      forwardBridgeDensity β μ s hs (-x) = forwardBridgeDensity β μ s hs x) ∧
    ContDiff ℝ ∞ (forwardRightPotential β μ s hs) ∧
    ContDiff ℝ ∞ (forwardLeftPotential β μ s hs) ∧
    (∀ x, forwardRightPotential β μ s hs (-x) = forwardRightPotential β μ s hs x ∧
      forwardLeftPotential β μ s hs (-x) = forwardLeftPotential β μ s hs x) ∧
    ContDiff ℝ ∞ (forwardBridgeCorrection β μ s hs) ∧
    ContDiff ℝ ∞ (forwardBridgeLeftCorrection β μ s hs) ∧
    (∀ x, forwardBridgeCorrection β μ s hs (-x) = forwardBridgeCorrection β μ s hs x ∧
      forwardBridgeLeftCorrection β μ s hs (-x) = forwardBridgeLeftCorrection β μ s hs x) ∧
    (∀ x, ‖deriv (forwardBridgeCorrection β μ s hs) x‖ ≤ 1 ∧
      ‖deriv (forwardBridgeLeftCorrection β μ s hs) x‖ ≤ 1) ∧
    (∀ x, (1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardRightPotential β μ s hs) x ∧
        iteratedDeriv 2 (forwardRightPotential β μ s hs) x ≤ 1 / (β ^ 2 * s) + parisiCDF μ s) ∧
      (1 / (β ^ 2 * s) ≤ iteratedDeriv 2 (forwardLeftPotential β μ s hs) x ∧
        iteratedDeriv 2 (forwardLeftPotential β μ s hs) x ≤ 1 / (β ^ 2 * s) + parisiLeftMass μ s)) ∧
    (∀ x, 0 ≤ x → iteratedDeriv 3 (forwardRightPotential β μ s hs) x ≤ 0 ∧
      iteratedDeriv 3 (forwardLeftPotential β μ s hs) x ≤ 0) ∧
    (∀ x, forwardBridgeDensity β μ s hs x ≤ Real.exp (β ^ 2 + |x|) * heatDensity (β ^ 2 * s) x ∧
      forwardBridgeDensity β μ s hs x ≤ forwardBridgeDensity β μ s hs 0 *
        Real.exp (parisiCDF μ s * |x| - x ^ 2 / (2 * (β ^ 2 * s)))) ∧
    (∀ j S, IsCompact S →
      let q : Overlap := ⟨s,hs.1.le,hs.2⟩
      let ν := preservingMeasure μ {q}
      TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeCorrection β (ν n) s hs))
        (iteratedDeriv j (forwardBridgeCorrection β μ s hs)) atTop S ∧
      TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeLeftCorrection β (ν n) s hs))
        (iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs)) atTop S) ∧
    (∀ k : ℕ, 1 ≤ k → ∃ c : ℝ, 0 < c ∧ ∀ (ν : ParisiMeasure) (t : ℝ)
      (ht : t ∈ Ioc (0 : ℝ) 1) (j : ℕ), j ∈ Icc 1 k → ∀ x : ℝ,
      ‖iteratedDeriv j (forwardBridgeCorrection β ν t ht) x‖ ≤ c ∧
      ‖iteratedDeriv j (forwardBridgeLeftCorrection β ν t ht) x‖ ≤ c)) ∧
  (∀ (β : ℝ) (μ : ParisiMeasure) (ν : ℕ → ParisiMeasure)
    (hν : Tendsto ν atTop (𝓝 μ)) (q : Overlap) (hq : 0 < (q : ℝ))
    (hpreserve : ∀ n, (ν n : Measure Overlap) (Iio q) = (μ : Measure Overlap) (Iio q) ∧
      (ν n : Measure Overlap) {q} = (μ : Measure Overlap) {q})
    (j : ℕ) (S : Set ℝ) (hS : IsCompact S),
    let hs : (q : ℝ) ∈ Ioc (0 : ℝ) 1 := ⟨hq,q.property.2⟩
    TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeCorrection β (ν n) q hs))
      (iteratedDeriv j (forwardBridgeCorrection β μ q hs)) atTop S ∧
    TendstoUniformlyOn (fun n => iteratedDeriv j (forwardBridgeLeftCorrection β (ν n) q hs))
      (iteratedDeriv j (forwardBridgeLeftCorrection β μ q hs)) atTop S) ∧
  (∀ {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s)))
    (j : ℕ) (S : Set ℝ) (hS : IsCompact S),
    TendstoUniformlyOn (fun a => iteratedDeriv j (forwardBridgeCorrection β (ν a) s hs))
      (iteratedDeriv j (forwardBridgeCorrection β μ s hs)) l S) ∧
  (∀ {A : Type*} {l : Filter A} [l.IsCountablyGenerated] (β : ℝ) (μ : ParisiMeasure)
    (ν : A → ParisiMeasure) (hν : Tendsto ν l (𝓝 μ)) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
    (hα : Tendsto (fun a => parisiCDF (ν a) s) l (𝓝 (parisiCDF μ s)))
    (hδ : Tendsto (fun a => parisiAtomMass (ν a) s hs) l (𝓝 (parisiAtomMass μ s hs)))
    (j : ℕ) (S : Set ℝ) (hS : IsCompact S),
    TendstoUniformlyOn (fun a => iteratedDeriv j (forwardBridgeLeftCorrection β (ν a) s hs))
      (iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs)) l S)

theorem result_4_1 : Statement_4_1 := ⟨@forward_proposition,@forward_correction_every_preserving_sequence_cloc,@tendstoUniformlyOn_iteratedDeriv_forwardBridgeCorrection_of_weak_cdf,@tendstoUniformlyOn_iteratedDeriv_forwardBridgeLeftCorrection_of_weak_masses⟩

/-- Paper 4.2. -/
def Statement_4_2 : Prop :=
  ∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (r t : ℝ) (hr : r ∈ Ioc (0 : ℝ) 1) (ht : t ∈ Ioc (0 : ℝ) 1)
    (hrt : r < t)
    (hzero : (μ : Measure Overlap) {q : Overlap | r < (q : ℝ) ∧ (q : ℝ) < t} = 0),
    forwardBridgeLeftCorrection β μ t ht =
      forwardHeatCorrection (β ^ 2 * r) (β ^ 2 * t) (forwardBridgeCorrection β μ r hr)

theorem result_4_2 : Statement_4_2 := @forwardBridgeLeftCorrection_heat_of_zero_mass

/-- Paper 4.3. -/
def Statement_4_3 : Prop :=
  ∀ (β : ℝ) (k : ℕ) (_hk : 1 ≤ k),
    ∃ c : ℝ, 0 < c ∧ ∀ (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1)
      (j : ℕ), j ∈ Icc 1 k → ∀ x : ℝ,
      ‖iteratedDeriv j (forwardBridgeCorrection β μ s hs) x‖ ≤ c ∧
      ‖iteratedDeriv j (forwardBridgeLeftCorrection β μ s hs) x‖ ≤ c

theorem result_4_3 : Statement_4_3 := @forward_derivative_bounds

/-- Paper 5.1. -/
def Statement_5_1 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (m a b : ℝ) (hm : 0 < m) (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hCDF : ∀ s ∈ Ioo a b, parisiCDF μ s = m),
    ContDiffOn ℝ 3 (Gamma β μ) (Ioo a b) ∧
      ∀ s ∈ Ioo a b, deriv (deriv (Gamma β μ)) s = 0 →
        0 < deriv (deriv (deriv (Gamma β μ))) s) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (m a b : ℝ) (hm : 0 < m)
    (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hc : ∀ s ∈ Ioo a b,parisiCDF μ s=m) {s : ℝ} (hs : s ∈ Ioo a b),
    deriv (crossingForwardMeanPhi β μ) (β^2*s)-
      (∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))*crossingMeanPhi β μ s =
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
      (fun x=>actualCrossingPhi β μ (parisiCDF μ s) (s,x))
      (bridgeCrossingK β μ s ⟨(hI hs).1,(hI hs).2.le⟩)/2+
    crossingCovariance (crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))
      (fun x=>backwardH β μ (parisiCDF μ s) (s,x))
      (bridgeCrossingPsi β μ s ⟨(hI hs).1,(hI hs).2.le⟩) ∧
    0 < deriv (crossingForwardMeanPhi β μ) (β^2*s)-
      (∫ x,backwardQ β μ (parisiCDF μ s) (s,x)
        ∂crossingWeightLaw (bridgeCrossingWeight β μ s ⟨(hI hs).1,(hI hs).2.le⟩))*crossingMeanPhi β μ s)

theorem result_5_1 : Statement_5_1 := ⟨@crossing_proposition,@crossing_forward_positive_representation⟩

/-- Paper 5.2. -/
def Statement_5_2 : Prop :=
  ∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ioo a b, parisiCDF μ s = m) {s : ℝ} (hs : s ∈ Ioo a b) (x : ℝ),
    crossingMaterialDerivative β μ m (backwardB β μ) s x = 0 ∧
    crossingMaterialDerivative β μ m (backwardC β μ) s x =
      backwardC β μ (s,x) * backwardQ β μ m (s,x) ∧
    crossingMaterialDerivative β μ m (backwardZ β μ) s x =
      backwardZ β μ (s,x) * backwardQ β μ m (s,x) -
        deriv (fun y => backwardQ β μ m (s,y)) x / 2 ∧
    crossingMaterialDerivative β μ m (actualCrossingPhi β μ m) s x =
      backwardQ β μ m (s,x) * actualCrossingPhi β μ m (s,x) +
        backwardZ β μ (s,x) * backwardHx β μ m (s,x) ∧
    crossingMaterialDerivative β μ m (fun p => Real.log (parisiForwardDensity β μ p.1 p.2)) s x =
      bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x / 2 -
        backwardZ β μ (s,x) ^ 2 - m * backwardC β μ (s,x) ∧
    deriv (fun r => crossingPhysicalWeight β μ r x) s / β ^ 2 +
      deriv (fun y => actualCrossingVelocity β μ m (s,y) * crossingPhysicalWeight β μ s y) x =
      (bridgeCrossingK β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x / 2 -
        backwardQ β μ m (s,x) - backwardH β μ m (s,x)) * crossingPhysicalWeight β μ s x ∧
    -deriv (fun y => crossingPhysicalWeight β μ s y * backwardZ β μ (s,y)) x /
        crossingPhysicalWeight β μ s x =
      actualCrossingPhi β μ m (s,x) + bridgeCrossingPsi β μ s ⟨ha.trans_lt hs.1,hs.2.le.trans hb⟩ x

theorem result_5_2 : Statement_5_2 := (fun β hβ μ a b m ha hab hb hc s hs x => @crossing_transport β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) s hs x)

/-- Paper 5.3. -/
def Statement_5_3 : Prop :=
  ∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) {a b m : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (hc : ∀ s ∈ Ioo a b,parisiCDF μ s = m) {t v : ℝ}
    (ht : t/β^2 ∈ Ioo a b) (hv : v ∈ Ioo (-1 : ℝ) 1),
    let s := t/β^2
    let hs : s ∈ Ioc (0 : ℝ) 1 := ⟨ha.trans_lt ht.1,ht.2.le.trans hb⟩
    let x := forwardMagnetizationInverse β μ t v
    canonicalBrownianMeasure.map (M β μ s) =
      (volume.restrict (Ioo (-1 : ℝ) 1)).withDensity
        (fun b => ENNReal.ofReal (magnetizationDensity β μ s hs b)) ∧
    (crossingWeightLaw (bridgeCrossingWeight β μ s hs)).map
      (fun x => parisiGradient β μ (s,x)) =
      (volume.restrict (Ico (0 : ℝ) 1)).withDensity
        (fun b => ENNReal.ofReal (2*magnetizationWeightedDensity β μ s hs b /
          curvatureMoment2 β μ s)) ∧
    magnetizationWeightedDensity β μ s hs v =
      forwardMagnetizationChi β μ t v^2 * magnetizationDensity β μ s hs v ∧
    deriv (fun r => forwardMagnetizationInverse β μ r v) t = actualCrossingVelocity β μ m (s,x) ∧
    deriv (fun r => forwardMagnetizationR β μ r v) t =
      forwardMagnetizationChi β μ t v^2 * deriv (deriv (forwardMagnetizationR β μ t)) v/2+
        2*backwardQ β μ m (s,x)*forwardMagnetizationR β μ t v ∧
    deriv (fun r => Real.log (forwardMagnetizationR β μ r v)) t =
      bridgeCrossingK β μ s hs x/2-backwardQ β μ m (s,x)-backwardH β μ m (s,x) ∧
    bridgeCrossingN β μ s hs x+backwardZ β μ (s,x) =
      -forwardMagnetizationChi β μ t v*deriv (fun b => Real.log (forwardMagnetizationR β μ t b)) v ∧
    bridgeCrossingK β μ s hs x =
      (bridgeCrossingN β μ s hs x^2-deriv (bridgeCrossingN β μ s hs) x)+
        (backwardZ β μ (s,x)^2+deriv (fun y => backwardZ β μ (s,y)) x) ∧
    deriv (fun r => Real.log (forwardMagnetizationChi β μ r v)) t = backwardQ β μ m (s,x) ∧
    (forwardMagnetizationChi β μ t v^2*deriv (deriv (forwardMagnetizationR β μ t)) v /
      (2*forwardMagnetizationR β μ t v) =
        (bridgeCrossingN β μ s hs x^2-backwardZ β μ (s,x)^2-
          deriv (bridgeCrossingN β μ s hs) x-deriv (fun y => backwardZ β μ (s,y)) x)/2 ∧
      forwardMagnetizationChi β μ t v^2*deriv (deriv (forwardMagnetizationR β μ t)) v /
        (2*forwardMagnetizationR β μ t v) =
          bridgeCrossingK β μ s hs x/2-3*backwardQ β μ (parisiCDF μ s) (s,x)-
            backwardH β μ (parisiCDF μ s) (s,x)) ∧
    -deriv (fun b => forwardMagnetizationChi β μ t b*
      backwardZ β μ (s,forwardMagnetizationInverse β μ t b)*forwardMagnetizationR β μ t b) v /
        forwardMagnetizationR β μ t v =
      actualCrossingPhi β μ (parisiCDF μ s) (s,x)+bridgeCrossingPsi β μ s hs x

theorem result_5_3 : Statement_5_3 := (fun β hβ μ a b m ha hab hb hc t v ht hv => @magnetization_weighted_law_remark β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) t v ht hv)

/-- Paper 5.4. -/
def Statement_5_4 : Prop :=
  (∀ (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤1)
    (hc : ∀s∈Ioo a b,parisiCDF μ s=m) (l u : ℝ)
    (hla : a<l) (_hlu : l≤u) (hub : u<b),
    ∃ c : ℝ,0<c ∧ ∀s∈Icc l u,∀x:ℝ,0≤x→
      crossingForwardField β (fun p=>crossingPhysicalWeight β μ p.1 p.2) (β^2*s,x)+
        ‖deriv (fun t=>crossingForwardField β (fun p=>crossingPhysicalWeight β μ p.1 p.2) (t,x)) (β^2*s)‖+
        ‖deriv (fun t=>crossingForwardField β
          (fun p=>actualCrossingPhi β μ m p*crossingPhysicalWeight β μ p.1 p.2) (t,x)) (β^2*s)‖ ≤
      c*(1+x^2)*Real.exp (x-x^2/(2*β^2))) ∧
  (∀ (β : ℝ) (hβ : β≠0) (μ : ParisiMeasure)
    {a b m : ℝ} (ha : 0≤a) (hab : a<b) (hb : b≤1)
    (hc : ∀s∈Ioo a b,parisiCDF μ s=m) {s : ℝ} (hs : s∈Ioo a b) (x : ℝ) (hx : 0≤x),
    ‖actualCrossingVelocity β μ m (s,x)‖≤2 ∧
    ‖backwardZ β μ (s,x)‖≤1 ∧
    ‖actualCrossingPhi β μ m (s,x)‖≤3 ∧
    ‖deriv (fun y=>actualCrossingPhi β μ m (s,y)) x‖≤10 ∧
    ‖crossingMaterialDerivative β μ m (actualCrossingPhi β μ m) s x‖≤9 ∧
    ‖backwardH β μ m (s,x)‖≤4 ∧
    actualCrossingVelocity β μ m (s,0)=0 ∧ backwardZ β μ (s,0)=0)

theorem result_5_4 : Statement_5_4 := ⟨(fun β hβ μ a b m ha hab hb hc l u hla hlu hub => @crossing_decay β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) l u hla hlu hub),(fun β hβ μ a b m ha hab hb hc s hs x hx => @crossing_bounded_transport_fields β hβ μ a b m ha hab hb (parisiCDF_constant_Ico_of_Ioo μ hab hc) s hs x hx)⟩

/-- Paper 5.5. -/
def Statement_5_5 : Prop :=
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (hm : 0 < parisiCDF μ s),
    StrictMonoOn (fun x => actualCrossingPhi β μ (parisiCDF μ s) (s, x)) (Ici 0)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1),
    StrictMonoOn (bridgeCrossingK β μ s hs) (Ici 0)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (hm : 0 < parisiCDF μ s),
    StrictMonoOn (bridgeCrossingPsi β μ s hs) (Ici 0)) ∧
  (∀ (β : ℝ) (hβ : β ≠ 0)
    (μ : ParisiMeasure) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1),
    MonotoneOn (fun x => backwardH β μ (parisiCDF μ s) (s, x)) (Ici 0))

theorem result_5_5 : Statement_5_5 := ⟨@actualCrossingPhi_strictMonoOn,@bridgeCrossingK_strictMonoOn,@bridgeCrossingPsi_strictMonoOn,@actualCrossingH_monotoneOn⟩

/-- Paper 5.6. -/
def Statement_5_6 : Prop :=
  ∀ (β : ℝ) (hβ : β ≠ 0) (μ : ParisiMeasure)
    (m a b : ℝ) (hab : a < b) (hm : 0 < m)
    (hI : Ioo a b ⊆ Ioo (0 : ℝ) 1)
    (hCDF : ∀ s ∈ Ioo a b, parisiCDF μ s = m),
    ∃ c ∈ Icc a b,
      StrictAntiOn (GammaPrime β μ) (Ioc a c ∩ Ioo a b) ∧
      StrictMonoOn (GammaPrime β μ) (Ico c b ∩ Ioo a b)

theorem result_5_6 : Statement_5_6 := @crossing_shape

/-- Paper 6.1. -/
def Statement_6_1 : Prop :=
  ∀ (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ),
    ∃ q ∈ Ioo (0 : ℝ) 1, parisiSupport μ = Icc (0 : ℝ) q

theorem result_6_1 : Statement_6_1 := @minimizer_full_support

/-- Paper 6.2. -/
def Statement_6_2 : Prop :=
  ∀ (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q),
    ContinuousOn (quotientNumerator β μ) (Icc (0 : ℝ) 1) ∧
    ContinuousOn (quotientDenominator β μ) (Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, 0 < quotientDenominator β μ s) ∧
    (∀ s ∈ Ico (0 : ℝ) q, parisiCDF μ s = momentQuotient β μ s) ∧
    parisiLeftMass μ q = momentQuotient β μ q ∧
    (μ : Measure Overlap) {⟨0,by simp⟩} = 0

theorem result_6_2 : Statement_6_2 := @minimizer_quotient

/-- Paper 6.3. -/
def Statement_6_3 : Prop :=
  ∀ (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q),
    (∀ f : MomentPolynomial, ContDiffOn ℝ ∞ (moment β μ f) (Icc (0 : ℝ) q)) ∧
      ContDiffOn ℝ ∞ (momentQuotient β μ) (Icc (0 : ℝ) q)

theorem result_6_3 : Statement_6_3 := @minimizer_moments_smooth

/-- SK specialization and endpoint improvement of Remark 6.4; the cited general mixed-p-spin half-open theorem is recorded separately in the ledger. -/
def Statement_6_4 : Prop :=
  ∀ (β : ℝ) (hβ : 1 < β) (μ : ParisiMeasure)
    (hmin : IsParisiMinimizer β 0 μ) (q : ℝ) (hq : q ∈ parisiSupport μ)
    (hmax : ∀ x ∈ parisiSupport μ, x ≤ q),
    ContDiffOn ℝ ∞ (parisiCDF μ) (Ico (0 : ℝ) q) ∧
    (∀ n : ℕ, ContinuousOn
      (iteratedDerivWithin n (momentQuotient β μ) (Icc (0 : ℝ) q)) (Icc (0 : ℝ) q)) ∧
    (∀ n : ℕ, ContinuousOn
      (iteratedDerivWithin n (parisiSmoothDensity β μ q) (Icc (0 : ℝ) q)) (Icc (0 : ℝ) q)) ∧
    (∀ (f : MomentPolynomial) (n : ℕ), ContinuousOn
      (iteratedDerivWithin n (moment β μ f) (Icc (0 : ℝ) q)) (Icc (0 : ℝ) q))

theorem result_6_4 : Statement_6_4 := @minimizer_endpoint_regular

end FRSB.Numbered
