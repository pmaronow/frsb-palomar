module

public import FRSB.ForwardDensityRegularity
public import FRSB.CrossingBridgeDifferentiation
public import FRSB.CrossingDecay

@[expose] public section

/-! Genuine compact-time Gaussian domination for the actual forward
 density and its spatial and time derivatives. The envelope is uniform
 over probability measures and integrable on the positive half-line. -/
noncomputable section
open Set Filter MeasureTheory Paper
open scoped Topology ContDiff
namespace FRSB
set_option maxHeartbeats 1000000

def forwardCompactDensityConstant (β l : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * (β^2*l)))⁻¹ * Real.exp (β^2)

def forwardCompactScoreConstant (β l : ℝ) : ℝ := 2+|(β^2*l)⁻¹|

def forwardCompactScoreDerivativeConstant (β l : ℝ) : ℝ :=
  uniformSpatialConstant β 1+|(β^2*l)⁻¹|+
    |negativeLogDerivativeConstant (forwardBridgeRelativeConstant β 2) 2|

def forwardCompactGradientConstant (β l : ℝ) : ℝ :=
  2*forwardCompactScoreConstant β l*forwardCompactDensityConstant β l

def forwardCompactSecondConstant (β l : ℝ) : ℝ :=
  (2*(forwardCompactScoreConstant β l)^2+forwardCompactScoreDerivativeConstant β l)*
    forwardCompactDensityConstant β l

def forwardCompactTimeConstant (β l : ℝ) : ℝ :=
  β^2*((1/2:ℝ)*forwardCompactSecondConstant β l+
    uniformSpatialConstant β 1*forwardCompactDensityConstant β l+
    forwardCompactGradientConstant β l)

 theorem heatDensity_compact_time_bound (β:ℝ) (hβ:β≠0) {l t u:ℝ}
    (hl:0<l) (hlt:l≤t) (htu:t≤u) (x:ℝ) :
    heatDensity (β^2*t) x ≤ (Real.sqrt (2*Real.pi*(β^2*l)))⁻¹*
      Real.exp (-x^2/(2*(β^2*u))) := by
  have hb:0<β^2:=sq_pos_of_ne_zero hβ
  have hv:0<β^2*l:=mul_pos hb hl
  have hvT:0<β^2*t:=mul_pos hb (hl.trans_le hlt)
  have hs:0<Real.sqrt (2*Real.pi*(β^2*l)):=Real.sqrt_pos.2 (by positivity)
  have hn:(Real.sqrt (2*Real.pi*(β^2*t)))⁻¹≤(Real.sqrt (2*Real.pi*(β^2*l)))⁻¹:=
    inv_anti₀ hs (Real.sqrt_le_sqrt (by gcongr))
  have he:-x^2/(2*(β^2*t))≤-x^2/(2*(β^2*u)):=by
    have hi:1/(2*(β^2*u))≤1/(2*(β^2*t)):=
      one_div_le_one_div_of_le (by positivity) (by gcongr)
    have hm:=mul_le_mul_of_nonneg_left hi (sq_nonneg x)
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith
  exact mul_le_mul hn (Real.exp_le_exp.2 he) (Real.exp_pos _).le (by positivity)

 theorem forwardBridgeDensity_compact_envelope (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t u:ℝ} (hl:0<l) (hlt:l≤t) (htu:t≤u) (ht:t∈Ioc (0:ℝ) 1)
    {x:ℝ} (hx:0≤x) :
    ‖forwardBridgeDensity β μ t ht x‖≤forwardCompactDensityConstant β l*
      Real.exp (x-x^2/(2*(β^2*u))) := by
  rw [Real.norm_of_nonneg (forwardBridgeDensity_pos β hβ μ t ht x).le]
  calc
    _ ≤ Real.exp (β^2+|x|)*heatDensity (β^2*t) x :=
      forwardBridgeDensity_gaussian_envelope β μ t ht x
    _ ≤ Real.exp (β^2+x)*((Real.sqrt (2*Real.pi*(β^2*l)))⁻¹*
        Real.exp (-x^2/(2*(β^2*u)))) := by
      rw [abs_of_nonneg hx]
      exact mul_le_mul_of_nonneg_left (heatDensity_compact_time_bound β hβ hl hlt htu x)
        (Real.exp_pos _).le
    _ = _ := by
      unfold forwardCompactDensityConstant
      rw [Real.exp_add,sub_eq_add_neg,Real.exp_add,neg_div]
      ring

def forwardDensityScore (β:ℝ) (μ:ParisiMeasure) (t:ℝ) (ht:t∈Ioc (0:ℝ) 1) (x:ℝ) : ℝ :=
  parisiCDF μ t*parisiSpatialJet β μ 1 t x-x/(β^2*t)-deriv (forwardBridgeCorrection β μ t ht) x

def forwardDensityScoreX (β:ℝ) (μ:ParisiMeasure) (t:ℝ) (ht:t∈Ioc (0:ℝ) 1) (x:ℝ) : ℝ :=
  parisiCDF μ t*parisiSpatialJet β μ 2 t x-(β^2*t)⁻¹-
    iteratedDeriv 2 (forwardBridgeCorrection β μ t ht) x

 theorem hasDerivAt_forwardDensityScore (β:ℝ) (μ:ParisiMeasure) (t:ℝ)
    (ht:t∈Ioc (0:ℝ) 1) (x:ℝ) :
    HasDerivAt (forwardDensityScore β μ t ht) (forwardDensityScoreX β μ t ht x) x := by
  have hd:=(((hasDerivAt_parisiSpatialJet_succ β μ 0 t x).const_mul (parisiCDF μ t)).sub
    ((hasDerivAt_id x).div_const (β^2*t))).sub
      (by simpa only [iteratedDeriv_one,Nat.reduceAdd] using
        hasDerivAt_forwardBridgeCorrection_jet β μ t ht 1 x)
  convert hd using 1
  · rfl
  · simp only [forwardDensityScoreX,one_div]

 theorem deriv_forwardBridgeDensity_eq_score (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (t:ℝ) (ht:t∈Ioc (0:ℝ) 1) (x:ℝ) :
    deriv (forwardBridgeDensity β μ t ht) x=
      forwardDensityScore β μ t ht x*forwardBridgeDensity β μ t ht x := by
  rw [(hasDerivAt_forwardBridgeDensity_score β hβ μ t ht x).deriv]
  simp only [forwardDensityScore,bridgeCrossingVx,parisiSpatialJet_one,
    backwardB_eq_gradient β μ t x ⟨ht.1.le,ht.2⟩]
  ring

 theorem iteratedDeriv_forwardBridgeDensity_two_score_fields (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (t:ℝ) (ht:t∈Ioc (0:ℝ) 1) (x:ℝ) :
    iteratedDeriv 2 (forwardBridgeDensity β μ t ht) x=
      (forwardDensityScoreX β μ t ht x+(forwardDensityScore β μ t ht x)^2)*
        forwardBridgeDensity β μ t ht x := by
  have hpd:HasDerivAt (forwardBridgeDensity β μ t ht)
      (forwardDensityScore β μ t ht x*forwardBridgeDensity β μ t ht x) x := by
    rw [←deriv_forwardBridgeDensity_eq_score β hβ μ t ht x]
    exact ((contDiff_forwardBridgeDensity β μ t ht).differentiable (by simp) x).hasDerivAt
  have he:deriv (forwardBridgeDensity β μ t ht)=fun y=>
      forwardDensityScore β μ t ht y*forwardBridgeDensity β μ t ht y:=
    funext (deriv_forwardBridgeDensity_eq_score β hβ μ t ht)
  have hprod : HasDerivAt (fun y=>forwardDensityScore β μ t ht y*forwardBridgeDensity β μ t ht y)
      (forwardDensityScoreX β μ t ht x*forwardBridgeDensity β μ t ht x+
       forwardDensityScore β μ t ht x*(forwardDensityScore β μ t ht x*forwardBridgeDensity β μ t ht x)) x := by
    convert (hasDerivAt_forwardDensityScore β μ t ht x).mul hpd using 1
  rw [iteratedDeriv_succ,iteratedDeriv_one,he,hprod.deriv]
  ring

 theorem norm_forwardDensityScore_compact (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t:ℝ} (hl:0<l) (hlt:l≤t) (ht:t∈Ioc (0:ℝ) 1) {x:ℝ} (hx:0≤x) :
    ‖forwardDensityScore β μ t ht x‖≤forwardCompactScoreConstant β l*(1+x) := by
  have hv:0<β^2*l:=mul_pos (sq_pos_of_ne_zero hβ) hl
  have hvT:0<β^2*t:=mul_pos (sq_pos_of_ne_zero hβ) ht.1
  have hi:(β^2*t)⁻¹≤(β^2*l)⁻¹:=inv_anti₀ hv (by gcongr)
  have hB:‖parisiSpatialJet β μ 1 t x‖≤1:=by
    rw [parisiSpatialJet_one];exact norm_parisiGradient_le_one β μ (t,x)
  have ha:‖parisiCDF μ t‖≤1:=by
    rw [Real.norm_of_nonneg (parisiCDF_nonneg μ t)];exact parisiCDF_le_one μ t
  have hxv:‖x/(β^2*t)‖≤x*(β^2*l)⁻¹:=by
    rw [Real.norm_of_nonneg (div_nonneg hx hvT.le),div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left hi hx
  calc
    _ ≤ ‖parisiCDF μ t*parisiSpatialJet β μ 1 t x‖+‖x/(β^2*t)‖+
      ‖deriv (forwardBridgeCorrection β μ t ht) x‖:=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ 1+x*(β^2*l)⁻¹+1 := by
      gcongr
      · rw [norm_mul];exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using hB)
      · exact forwardBridgeCorrection_slope_bound β μ t ht x
    _ ≤ _ := by
      unfold forwardCompactScoreConstant
      rw [abs_of_nonneg (inv_nonneg.2 hv.le)]
      have hv0:(0:ℝ)≤(β^2*l)⁻¹:=inv_nonneg.2 hv.le
      nlinarith

 theorem norm_forwardDensityScoreX_compact (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t:ℝ} (hl:0<l) (hlt:l≤t) (ht:t∈Ioc (0:ℝ) 1) (x:ℝ) :
    ‖forwardDensityScoreX β μ t ht x‖≤forwardCompactScoreDerivativeConstant β l := by
  have hv:0<β^2*l:=mul_pos (sq_pos_of_ne_zero hβ) hl
  have hvT:0<β^2*t:=mul_pos (sq_pos_of_ne_zero hβ) ht.1
  have hi:(β^2*t)⁻¹≤(β^2*l)⁻¹:=inv_anti₀ hv (by gcongr)
  have hC:‖parisiSpatialJet β μ 2 t x‖≤uniformSpatialConstant β 1:=
    (norm_parisiSpatialJet_succ_le β μ 1 t x).trans (norm_spatialDerivativeBCF_le_uniform β μ 1)
  have ha:‖parisiCDF μ t‖≤1:=by
    rw [Real.norm_of_nonneg (parisiCDF_nonneg μ t)];exact parisiCDF_le_one μ t
  have hW:=forwardBridgeCorrection_uniform_derivative_bound β μ t ht 2 (by norm_num) x
  unfold forwardDensityScoreX forwardCompactScoreDerivativeConstant
  calc
    _ ≤ ‖parisiCDF μ t*parisiSpatialJet β μ 2 t x‖+‖(β^2*t)⁻¹‖+
      ‖iteratedDeriv 2 (forwardBridgeCorrection β μ t ht) x‖:=
      (norm_sub_le _ _).trans (add_le_add (norm_sub_le _ _) (le_refl _))
    _ ≤ _ := by
      apply add_le_add
      · apply add_le_add
        · rw [norm_mul]
          exact (mul_le_mul_of_nonneg_right ha (norm_nonneg _)).trans (by simpa using hC)
        · rw [Real.norm_of_nonneg (inv_nonneg.2 hvT.le)];exact hi.trans (le_abs_self _)
      · exact hW.trans (le_abs_self _)

 theorem forwardCompactDensityConstant_nonneg (β l:ℝ) : 0≤forwardCompactDensityConstant β l := by
  unfold forwardCompactDensityConstant;positivity

 theorem forwardCompactScoreConstant_nonneg (β l:ℝ) : 0≤forwardCompactScoreConstant β l := by
  unfold forwardCompactScoreConstant;positivity

 theorem forwardCompactScoreDerivativeConstant_nonneg (β l:ℝ) :
    0≤forwardCompactScoreDerivativeConstant β l := by
  unfold forwardCompactScoreDerivativeConstant
  exact add_nonneg (add_nonneg (uniformSpatialConstant_pos β 1).le (by positivity)) (abs_nonneg _)

 theorem forwardCompactGradientConstant_nonneg (β l:ℝ) : 0≤forwardCompactGradientConstant β l := by
  unfold forwardCompactGradientConstant
  exact mul_nonneg (mul_nonneg (by norm_num) (forwardCompactScoreConstant_nonneg β l))
    (forwardCompactDensityConstant_nonneg β l)

 theorem forwardCompactSecondConstant_nonneg (β l:ℝ) : 0≤forwardCompactSecondConstant β l := by
  unfold forwardCompactSecondConstant
  exact mul_nonneg (add_nonneg (by positivity) (forwardCompactScoreDerivativeConstant_nonneg β l))
    (forwardCompactDensityConstant_nonneg β l)

 theorem forwardCompactTimeConstant_nonneg (β l:ℝ) : 0≤forwardCompactTimeConstant β l := by
  unfold forwardCompactTimeConstant
  exact mul_nonneg (sq_nonneg β) (add_nonneg
    (add_nonneg (mul_nonneg (by norm_num) (forwardCompactSecondConstant_nonneg β l))
      (mul_nonneg (uniformSpatialConstant_pos β 1).le (forwardCompactDensityConstant_nonneg β l)))
    (forwardCompactGradientConstant_nonneg β l))

 theorem forwardBridgeDensity_compact_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t u:ℝ} (hl:0<l) (hlt:l≤t) (htu:t≤u) (ht:t∈Ioc (0:ℝ) 1)
    {x:ℝ} (hx:0≤x) :
    ‖forwardBridgeDensity β μ t ht x‖≤forwardCompactDensityConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  apply (forwardBridgeDensity_compact_envelope β hβ μ hl hlt htu ht hx).trans
  unfold crossingGaussianEnvelope
  apply mul_le_mul_of_nonneg_left _ (forwardCompactDensityConstant_nonneg β l)
  rw [abs_of_nonneg hx]
  nlinarith [Real.exp_pos (x-x^2/(2*(β^2*u))),sq_nonneg x]

 theorem deriv_forwardBridgeDensity_compact_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t u:ℝ} (hl:0<l) (hlt:l≤t) (htu:t≤u) (ht:t∈Ioc (0:ℝ) 1)
    {x:ℝ} (hx:0≤x) :
    ‖deriv (forwardBridgeDensity β μ t ht) x‖≤forwardCompactGradientConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  rw [deriv_forwardBridgeDensity_eq_score β hβ μ t ht x,norm_mul]
  have hR:=forwardCompactScoreConstant_nonneg β l
  have hP:=forwardCompactDensityConstant_nonneg β l
  calc
    _ ≤ (forwardCompactScoreConstant β l*(1+x))*(forwardCompactDensityConstant β l*
      Real.exp (x-x^2/(2*(β^2*u)))) :=
      mul_le_mul (norm_forwardDensityScore_compact β hβ μ hl hlt ht hx)
        (forwardBridgeDensity_compact_envelope β hβ μ hl hlt htu ht hx)
        (norm_nonneg _) (mul_nonneg hR (by linarith))
    _ ≤ _ := by
      unfold forwardCompactGradientConstant crossingGaussianEnvelope
      rw [abs_of_nonneg hx]
      have hp:1+x≤2*(1+x^2):=by nlinarith [sq_nonneg (x-1)]
      have hh:=mul_le_mul_of_nonneg_left hp
        (mul_nonneg (mul_nonneg hR hP) (Real.exp_pos (x-x^2/(2*(β^2*u)))).le)
      nlinarith [hh]

 theorem iteratedDeriv_forwardBridgeDensity_two_compact_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t u:ℝ} (hl:0<l) (hlt:l≤t) (htu:t≤u) (ht:t∈Ioc (0:ℝ) 1)
    {x:ℝ} (hx:0≤x) :
    ‖iteratedDeriv 2 (forwardBridgeDensity β μ t ht) x‖≤forwardCompactSecondConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  let R:=forwardCompactScoreConstant β l
  let T:=forwardCompactScoreDerivativeConstant β l
  have hR:0≤R:=forwardCompactScoreConstant_nonneg β l
  have hT:0≤T:=forwardCompactScoreDerivativeConstant_nonneg β l
  have hS:‖(forwardDensityScore β μ t ht x)^2‖≤2*R^2*(1+x^2):=by
    rw [norm_pow]
    calc
      _ ≤ (R*(1+x))^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_forwardDensityScore_compact β hβ μ hl hlt ht hx) 2
      _ ≤ _ := by
        have hh:=mul_le_mul_of_nonneg_left (show (1+x)^2≤2*(1+x^2) by nlinarith [sq_nonneg (x-1)]) (sq_nonneg R)
        nlinarith [hh]
  have hSS:‖forwardDensityScoreX β μ t ht x+(forwardDensityScore β μ t ht x)^2‖≤
      (2*R^2+T)*(1+x^2):=by
    apply (norm_add_le _ _).trans
    apply (add_le_add (norm_forwardDensityScoreX_compact β hβ μ hl hlt ht x) hS).trans
    have hh:=mul_nonneg hT (sq_nonneg x)
    nlinarith [hh]
  rw [iteratedDeriv_forwardBridgeDensity_two_score_fields β hβ μ t ht x,norm_mul]
  calc
    _ ≤ ((2*R^2+T)*(1+x^2))*(forwardCompactDensityConstant β l*
        Real.exp (x-x^2/(2*(β^2*u)))) :=
      mul_le_mul hSS (forwardBridgeDensity_compact_envelope β hβ μ hl hlt htu ht hx)
        (norm_nonneg _) (by positivity)
    _ = _ := by
      unfold forwardCompactSecondConstant crossingGaussianEnvelope
      rw [abs_of_nonneg hx]
      dsimp only [R,T]
      ring

 theorem norm_parisiForwardDensityT_compact_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l t u m:ℝ} (hl:0<l) (hlt:l≤t) (htu:t≤u) (ht:t∈Ioc (0:ℝ) 1)
    (hm:m∈Icc (0:ℝ) 1) {x:ℝ} (hx:0≤x) :
    ‖parisiForwardDensityT β μ m t x‖≤forwardCompactTimeConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  have hM:‖m‖≤1:=by rw [Real.norm_of_nonneg hm.1];exact hm.2
  have hB:‖parisiSpatialJet β μ 1 t x‖≤1:=by
    rw [parisiSpatialJet_one];exact norm_parisiGradient_le_one β μ (t,x)
  have hC:‖parisiSpatialJet β μ 2 t x‖≤uniformSpatialConstant β 1:=
    (norm_parisiSpatialJet_succ_le β μ 1 t x).trans (norm_spatialDerivativeBCF_le_uniform β μ 1)
  have hP:=forwardBridgeDensity_compact_bound β hβ μ hl hlt htu ht hx
  have hPX:=deriv_forwardBridgeDensity_compact_bound β hβ μ hl hlt htu ht hx
  have hPXX:=iteratedDeriv_forwardBridgeDensity_two_compact_bound β hβ μ hl hlt htu ht hx
  unfold parisiForwardDensityT
  rw [parisiForwardDensity_eq β μ ht,norm_mul,Real.norm_of_nonneg (sq_nonneg β)]
  calc
    _ ≤ β^2*((1/2:ℝ)*‖iteratedDeriv 2 (forwardBridgeDensity β μ t ht) x‖+
      ‖m‖*(‖parisiSpatialJet β μ 2 t x‖*‖forwardBridgeDensity β μ t ht x‖+
        ‖parisiSpatialJet β μ 1 t x‖*‖deriv (forwardBridgeDensity β μ t ht) x‖)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
      apply (norm_sub_le _ _).trans
      rw [norm_mul,norm_mul,Real.norm_of_nonneg (by norm_num :(0:ℝ)≤1/2)]
      apply add_le_add (le_refl _)
      exact mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (by rw [norm_mul,norm_mul])) (norm_nonneg _)
    _ ≤ β^2*((1/2:ℝ)*(forwardCompactSecondConstant β l*crossingGaussianEnvelope (β^2*u) 2 x)+
      (uniformSpatialConstant β 1*(forwardCompactDensityConstant β l*crossingGaussianEnvelope (β^2*u) 2 x)+
        forwardCompactGradientConstant β l*crossingGaussianEnvelope (β^2*u) 2 x)) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg β)
      apply add_le_add (mul_le_mul_of_nonneg_left hPXX (by norm_num))
      apply (mul_le_mul_of_nonneg_right hM (by positivity)).trans
      rw [one_mul]
      apply add_le_add
      · exact mul_le_mul hC hP (norm_nonneg _) (uniformSpatialConstant_pos β 1).le
      · exact (mul_le_mul hB hPX (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
    _ = _ := by unfold forwardCompactTimeConstant;ring

/-- A single time-independent integrable density envelope on every compact
 physical time interval bounded away from zero. -/
 theorem norm_parisiForwardDensity_compact_time_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l u:ℝ} (hl:0<l) (hu:u≤1) {t:ℝ} (ht:t∈Icc l u) {x:ℝ} (hx:0≤x) :
    ‖parisiForwardDensity β μ t x‖≤forwardCompactDensityConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  have ht01:t∈Ioc (0:ℝ) 1:=⟨hl.trans_le ht.1,ht.2.trans hu⟩
  rw [parisiForwardDensity_eq β μ ht01]
  exact forwardBridgeDensity_compact_bound β hβ μ hl ht.1 ht.2 ht01 hx

 theorem norm_deriv_parisiForwardDensity_compact_time_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l u:ℝ} (hl:0<l) (hu:u≤1) {t:ℝ} (ht:t∈Icc l u) {x:ℝ} (hx:0≤x) :
    ‖deriv (parisiForwardDensity β μ t) x‖≤forwardCompactGradientConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  have ht01:t∈Ioc (0:ℝ) 1:=⟨hl.trans_le ht.1,ht.2.trans hu⟩
  rw [parisiForwardDensity_eq β μ ht01]
  exact deriv_forwardBridgeDensity_compact_bound β hβ μ hl ht.1 ht.2 ht01 hx

 theorem norm_iteratedDeriv_parisiForwardDensity_two_compact_time_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l u:ℝ} (hl:0<l) (hu:u≤1) {t:ℝ} (ht:t∈Icc l u) {x:ℝ} (hx:0≤x) :
    ‖iteratedDeriv 2 (parisiForwardDensity β μ t) x‖≤forwardCompactSecondConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x := by
  have ht01:t∈Ioc (0:ℝ) 1:=⟨hl.trans_le ht.1,ht.2.trans hu⟩
  rw [parisiForwardDensity_eq β μ ht01]
  exact iteratedDeriv_forwardBridgeDensity_two_compact_bound β hβ μ hl ht.1 ht.2 ht01 hx

 theorem norm_parisiForwardDensityT_compact_time_bound (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    {l u m:ℝ} (hl:0<l) (hu:u≤1) (hm:m∈Icc (0:ℝ) 1) {t:ℝ} (ht:t∈Icc l u) {x:ℝ} (hx:0≤x) :
    ‖parisiForwardDensityT β μ m t x‖≤forwardCompactTimeConstant β l*
      crossingGaussianEnvelope (β^2*u) 2 x :=
  norm_parisiForwardDensityT_compact_bound β hβ μ hl ht.1 ht.2
    ⟨hl.trans_le ht.1,ht.2.trans hu⟩ hm hx

 theorem integrable_forwardDensity_compact_envelope (β:ℝ) (hβ:β≠0) {u:ℝ} (hu:0<u)
    (K:ℝ) : Integrable (fun x=>K*crossingGaussianEnvelope (β^2*u) 2 x) :=
  (integrable_crossingGaussianEnvelope (β^2*u) 2 (mul_pos (sq_pos_of_ne_zero hβ) hu)).const_mul K

 theorem continuous_parisiForwardDensityT_spatial (β:ℝ) (μ:ParisiMeasure) (m:ℝ)
    {t:ℝ} (ht:t∈Ioc (0:ℝ) 1) : Continuous (fun x=>parisiForwardDensityT β μ m t x) := by
  have hp:ContDiff ℝ ∞ (parisiForwardDensity β μ t):=by
    rw [parisiForwardDensity_eq β μ ht];exact contDiff_forwardBridgeDensity β μ t ht
  have hB:Continuous (fun x=>parisiSpatialJet β μ 1 t x):=by
    convert (continuous_parisiSpatialJet_succ β μ 0).comp
      (show Continuous (fun x:ℝ=>(t,x)) from continuous_const.prodMk continuous_id) using 1
    rfl
  have hC:Continuous (fun x=>parisiSpatialJet β μ 2 t x):=by
    convert (continuous_parisiSpatialJet_succ β μ 1).comp
      (show Continuous (fun x:ℝ=>(t,x)) from continuous_const.prodMk continuous_id) using 1
    rfl
  unfold parisiForwardDensityT
  exact continuous_const.mul ((continuous_const.mul (hp.continuous_iteratedDeriv 2 (by simp))).sub
    (continuous_const.mul ((hC.mul hp.continuous).add
      (hB.mul (by simpa only [iteratedDeriv_one] using hp.continuous_iteratedDeriv 1 (by simp))))))

 theorem integrableOn_parisiForwardDensityT (β:ℝ) (hβ:β≠0) (μ:ParisiMeasure)
    (m:ℝ) (hm:m∈Icc (0:ℝ) 1) {t:ℝ} (ht:t∈Ioc (0:ℝ) 1) :
    IntegrableOn (fun x=>parisiForwardDensityT β μ m t x) (Ioi (0:ℝ)) := by
  apply integrableOn_of_crossingGaussianEnvelope_bound _ (β^2*t) 2 (forwardCompactTimeConstant β t)
    (mul_pos (sq_pos_of_ne_zero hβ) ht.1)
    (continuous_parisiForwardDensityT_spatial β μ m ht).aestronglyMeasurable
  intro x hx
  exact norm_parisiForwardDensityT_compact_bound β hβ μ ht.1 (le_refl t) (le_refl t) ht hm hx.le

end FRSB
