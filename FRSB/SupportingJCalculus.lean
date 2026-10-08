module

public import FRSB.BackwardsCellFields
public import FRSB.BackwardsTerminalBounds
public import Mathlib.Analysis.SpecialFunctions.Sqrt

@[expose] public section

/-! The literal norm calculation in displays (27)--(30).

The fields below are the actual derivatives of the constructed Parisi solution.
Time derivatives in the finite-cell statements are discharged by the genuine
Cole--Hopf time hierarchy; they are not assumed as PDE hypotheses.
-/
noncomputable section
open Set
open scoped Topology
namespace FRSB

/-- The four-component Euclidean norm used in the paper. -/
def jetNorm4 (c d e f : ℝ) : ℝ := Real.sqrt (c^2+d^2+e^2+f^2)
def jetDot4 (c d e f c' d' e' f' : ℝ) : ℝ := c*c'+d*d'+e*e'+f*f'

theorem jetNorm4_sq (c d e f : ℝ) :
    jetNorm4 c d e f ^ 2 = c^2+d^2+e^2+f^2 := by
  exact Real.sq_sqrt (by positivity)

theorem jetNorm4_pos {c d e f : ℝ} (hc : 0 < c) : 0 < jetNorm4 c d e f := by
  apply Real.sqrt_pos.mpr
  nlinarith [sq_nonneg d,sq_nonneg e,sq_nonneg f]

theorem hasDerivAt_jetNorm4 {c d e f : ℝ → ℝ} {c' d' e' f' x : ℝ}
    (hc : HasDerivAt c c' x) (hd : HasDerivAt d d' x)
    (he : HasDerivAt e e' x) (hf : HasDerivAt f f' x)
    (hpos : 0 < c x) :
    HasDerivAt (fun y => jetNorm4 (c y) (d y) (e y) (f y))
      (jetDot4 (c x) (d x) (e x) (f x) c' d' e' f' /
        jetNorm4 (c x) (d x) (e x) (f x)) x := by
  have hs : c x^2+d x^2+e x^2+f x^2 ≠ 0 := by
    have : 0 < c x^2+d x^2+e x^2+f x^2 := by
      nlinarith [sq_nonneg (d x),sq_nonneg (e x),sq_nonneg (f x)]
    exact this.ne'
  have h := (((hc.pow 2).add (hd.pow 2)).add (he.pow 2)).add (hf.pow 2)
  have hh := h.sqrt hs
  convert hh using 1 <;>
    simp only [jetNorm4,jetDot4,Pi.add_apply,Pi.pow_apply,Nat.reduceSub,pow_one,Nat.cast_ofNat]
  ring

/-- Lagrange's sum-of-squares form of the nonnegative curvature remainder. -/
theorem jetNorm4_cauchy_remainder_nonneg (c d e f v w z y : ℝ) :
    0 ≤ jetNorm4 c d e f^2 * (v^2+w^2+z^2+y^2) -
      jetDot4 c d e f v w z y ^ 2 := by
  rw [jetNorm4_sq]
  have hid : (c^2+d^2+e^2+f^2)*(v^2+w^2+z^2+y^2)-
      jetDot4 c d e f v w z y^2 =
      (c*w-d*v)^2+(c*z-e*v)^2+(c*y-f*v)^2+
      (d*z-e*w)^2+(d*y-f*w)^2+(e*y-f*z)^2 := by
    dsimp [jetDot4]
    ring
  rw [hid]
  positivity

theorem jetNorm4_nonneg (c d e f : ℝ) : 0 ≤ jetNorm4 c d e f := Real.sqrt_nonneg _

theorem jetNorm4_abs_component_le (c d e f : ℝ) :
    |c| ≤ jetNorm4 c d e f ∧ |d| ≤ jetNorm4 c d e f ∧
    |e| ≤ jetNorm4 c d e f ∧ |f| ≤ jetNorm4 c d e f := by
  have hs := jetNorm4_sq c d e f
  have hn := jetNorm4_nonneg c d e f
  constructor
  · nlinarith [sq_abs c,sq_nonneg d,sq_nonneg e,sq_nonneg f,abs_nonneg c]
  constructor
  · nlinarith [sq_abs d,sq_nonneg c,sq_nonneg e,sq_nonneg f,abs_nonneg d]
  constructor
  · nlinarith [sq_abs e,sq_nonneg c,sq_nonneg d,sq_nonneg f,abs_nonneg e]
  · nlinarith [sq_abs f,sq_nonneg c,sq_nonneg d,sq_nonneg e,abs_nonneg f]

theorem jetNorm4_le_abs_sum (c d e f : ℝ) : jetNorm4 c d e f ≤ |c|+|d|+|e|+|f| := by
  have hs := jetNorm4_sq c d e f
  have hn := jetNorm4_nonneg c d e f
  nlinarith [sq_abs c,sq_abs d,sq_abs e,sq_abs f,
    abs_nonneg c,abs_nonneg d,abs_nonneg e,abs_nonneg f,
    mul_nonneg (abs_nonneg c) (abs_nonneg d),
    mul_nonneg (abs_nonneg c) (abs_nonneg e),
    mul_nonneg (abs_nonneg c) (abs_nonneg f),
    mul_nonneg (abs_nonneg d) (abs_nonneg e),
    mul_nonneg (abs_nonneg d) (abs_nonneg f),
    mul_nonneg (abs_nonneg e) (abs_nonneg f)]

/-- The literal lower triangular matrix action in the paper. -/
def jetMatrix4 (a c d v w z y : ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (a*c*v,3*a*c*w,a*(3*d*w+4*c*z),a*(10*d*z+5*c*y))

/-- An explicit operator norm bound, uniform over all four-vector inputs. -/
theorem jetMatrix4_norm_le (a c d K v w z y : ℝ)
    (ha : |a| ≤ 1) (hc : |c| ≤ 1) (hd : |d| ≤ K) :
    jetNorm4 (jetMatrix4 a c d v w z y).1 (jetMatrix4 a c d v w z y).2.1
      (jetMatrix4 a c d v w z y).2.2.1 (jetMatrix4 a c d v w z y).2.2.2 ≤
      (13+13*K)*jetNorm4 v w z y := by
  have hK : 0 ≤ K := (abs_nonneg d).trans hd
  obtain ⟨hv,hw,hz,hy⟩ := jetNorm4_abs_component_le v w z y
  have hJ := jetNorm4_nonneg v w z y
  have hac : |a| * |c| ≤ 1 := by
    exact (mul_le_mul ha hc (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
  have h1 : |a*c*v| ≤ jetNorm4 v w z y := by
    rw [abs_mul,abs_mul]
    exact (mul_le_mul hac hv (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have h2 : |3*a*c*w| ≤ 3*jetNorm4 v w z y := by
    rw [abs_mul,abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul hac hw (abs_nonneg _) (by norm_num)
    nlinarith
  have h3a : |3*d*w| ≤ 3*K*jetNorm4 v w z y := by
    rw [abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul hd hw (abs_nonneg _) hK
    nlinarith
  have h3b : |4*c*z| ≤ 4*jetNorm4 v w z y := by
    rw [abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul hc hz (abs_nonneg _) (by norm_num)
    nlinarith
  have h3 : |a*(3*d*w+4*c*z)| ≤ (3*K+4)*jetNorm4 v w z y := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_right ha (abs_nonneg (3*d*w+4*c*z))
    have hh' := abs_add_le (3*d*w) (4*c*z)
    nlinarith
  have h4a : |10*d*z| ≤ 10*K*jetNorm4 v w z y := by
    rw [abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul hd hz (abs_nonneg _) hK
    nlinarith
  have h4b : |5*c*y| ≤ 5*jetNorm4 v w z y := by
    rw [abs_mul,abs_mul]
    norm_num
    have hh := mul_le_mul hc hy (abs_nonneg _) (by norm_num)
    nlinarith
  have h4 : |a*(10*d*z+5*c*y)| ≤ (10*K+5)*jetNorm4 v w z y := by
    rw [abs_mul]
    have hh := mul_le_mul_of_nonneg_right ha (abs_nonneg (10*d*z+5*c*y))
    have hh' := abs_add_le (10*d*z) (5*c*y)
    nlinarith
  have hh := jetNorm4_le_abs_sum (a*c*v) (3*a*c*w)
    (a*(3*d*w+4*c*z)) (a*(10*d*z+5*c*y))
  dsimp [jetMatrix4]
  linarith

theorem jetDot4_le_norm_mul (c d e f v w z y : ℝ) :
    jetDot4 c d e f v w z y ≤ jetNorm4 c d e f * jetNorm4 v w z y := by
  have hr := jetNorm4_cauchy_remainder_nonneg c d e f v w z y
  rw [←jetNorm4_sq v w z y] at hr
  have hnon := mul_nonneg (jetNorm4_nonneg c d e f) (jetNorm4_nonneg v w z y)
  nlinarith [sq_nonneg (jetDot4 c d e f v w z y - jetNorm4 c d e f * jetNorm4 v w z y)]

/-- The paper's actual norm field, in its rescaled backward time. -/
def backwardTauJ (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) : ℝ :=
  jetNorm4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
    (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)

def backwardTauJx (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) : ℝ :=
  jetDot4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
    (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
    (backwardTauD β μ 3 q) (backwardTauD β μ 4 q)
    (backwardTauD β μ 5 q) (backwardTauD β μ 6 q) / backwardTauJ β μ q

def backwardTauJxx (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) : ℝ :=
  (backwardTauD β μ 3 q^2 + backwardTauD β μ 4 q^2 +
    backwardTauD β μ 5 q^2 + backwardTauD β μ 6 q^2 +
    jetDot4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
      (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
      (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
      (backwardTauD β μ 6 q) (backwardTauD β μ 7 q)) / backwardTauJ β μ q -
    jetDot4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
      (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
      (backwardTauD β μ 3 q) (backwardTauD β μ 4 q)
      (backwardTauD β μ 5 q) (backwardTauD β μ 6 q)^2 / backwardTauJ β μ q^3

def backwardTauJt (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  jetDot4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
    (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
    (backwardTauForcing β μ a 2 q) (backwardTauForcing β μ a 3 q)
    (backwardTauForcing β μ a 4 q) (backwardTauForcing β μ a 5 q) / backwardTauJ β μ q

theorem backwardTauJ_pos (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ) : 0 < backwardTauJ β μ (τ,x) :=
  jetNorm4_pos (backwardTauC_pos_le_one β hβ μ τ x hτ).1

theorem continuous_backwardTauJ (β : ℝ) (μ : Paper.ParisiMeasure) :
    Continuous (backwardTauJ β μ) := by
  unfold backwardTauJ jetNorm4
  exact ((((continuous_backwardTauD β μ 2).pow 2).add
    ((continuous_backwardTauD β μ 3).pow 2)).add
    ((continuous_backwardTauD β μ 4).pow 2)).add
    ((continuous_backwardTauD β μ 5).pow 2) |>.sqrt

theorem hasDerivAt_backwardTauJ_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (τ x : ℝ) (hτ : τ ∈ Icc 0 (β^2)) :
    HasDerivAt (fun y => backwardTauJ β μ (τ,y)) (backwardTauJx β μ (τ,x)) x := by
  exact hasDerivAt_jetNorm4
    (hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 4 τ x hτ)
    (hasDerivAt_backwardTauD_spatial β hβ μ 5 τ x hτ)
    (backwardTauC_pos_le_one β hβ μ τ x hτ).1

theorem hasDerivAt_backwardTauJx_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (τ x : ℝ) (hτ : τ ∈ Icc 0 (β^2)) :
    HasDerivAt (fun y => backwardTauJx β μ (τ,y)) (backwardTauJxx β μ (τ,x)) x := by
  have hc := hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ
  have hd := hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ
  have he := hasDerivAt_backwardTauD_spatial β hβ μ 4 τ x hτ
  have hf := hasDerivAt_backwardTauD_spatial β hβ μ 5 τ x hτ
  have hg := hasDerivAt_backwardTauD_spatial β hβ μ 6 τ x hτ
  have hJ := hasDerivAt_backwardTauJ_spatial β hβ μ τ x hτ
  have hJne := (backwardTauJ_pos β hβ μ hτ x).ne'
  have hh := ((((hc.mul hd).add (hd.mul he)).add (he.mul hf)).add (hf.mul hg)).div hJ hJne
  convert hh using 1
  · rfl
  · simp only [backwardTauJxx,backwardTauJx,jetDot4,Pi.add_apply,Pi.mul_apply,Nat.reduceAdd]
    field_simp [hJne]
    ring

theorem deriv2_backwardTauJ_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (τ x : ℝ) (hτ : τ ∈ Icc 0 (β^2)) :
    deriv (deriv (fun y => backwardTauJ β μ (τ,y))) x = backwardTauJxx β μ (τ,x) := by
  have heq : deriv (fun y => backwardTauJ β μ (τ,y)) =
      fun y => backwardTauJx β μ (τ,y) :=
    funext fun y => (hasDerivAt_backwardTauJ_spatial β hβ μ τ y hτ).deriv
  rw [heq,(hasDerivAt_backwardTauJx_spatial β hβ μ τ x hτ).deriv]

theorem hasDerivAt_finiteCell_backwardTauJ {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    HasDerivAt (fun r => backwardTauJ β (Paper.parisiSchemeMeasure s) (r,x))
      (backwardTauJt β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x)) τ := by
  have hq := backwardCell_strict_of_mem s β hβ hτ
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
  exact hasDerivAt_jetNorm4
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 2 hτ x)
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 3 hτ x)
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 4 hτ x)
    (hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 5 hτ x)
    (backwardTauC_pos_le_one β hβ _ τ x hg).1

/-- A measure-independent bound for the actual lower triangular matrix. -/
def supportingJConstant (β : ℝ) : ℝ := 13+13*uniformSpatialConstant β 2

theorem supportingJConstant_pos (β : ℝ) : 0 < supportingJConstant β := by
  have hp := uniformSpatialConstant_pos β 2
  unfold supportingJConstant
  positivity

def backwardTauJReaction (β : ℝ) (μ : Paper.ParisiMeasure) (a : ℝ) (q : ℝ × ℝ) : ℝ :=
  jetDot4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
    (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
    (a*backwardTauD β μ 2 q^2)
    (3*a*backwardTauD β μ 2 q*backwardTauD β μ 3 q)
    (a*(4*backwardTauD β μ 2 q*backwardTauD β μ 4 q+3*backwardTauD β μ 3 q^2))
    (a*(5*backwardTauD β μ 2 q*backwardTauD β μ 5 q+
      10*backwardTauD β μ 3 q*backwardTauD β μ 4 q))

def backwardTauJRemainder (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) : ℝ :=
  backwardTauJ β μ q^2 * (backwardTauD β μ 3 q^2 + backwardTauD β μ 4 q^2 +
    backwardTauD β μ 5 q^2 + backwardTauD β μ 6 q^2) -
    jetDot4 (backwardTauD β μ 2 q) (backwardTauD β μ 3 q)
      (backwardTauD β μ 4 q) (backwardTauD β μ 5 q)
      (backwardTauD β μ 3 q) (backwardTauD β μ 4 q)
      (backwardTauD β μ 5 q) (backwardTauD β μ 6 q)^2

theorem backwardTauJRemainder_nonneg (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) :
    0 ≤ backwardTauJRemainder β μ q :=
  jetNorm4_cauchy_remainder_nonneg _ _ _ _ _ _ _ _

theorem backwardTauJReaction_le (β : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    (a : ℝ) (ha : a ∈ Icc 0 1) {τ : ℝ} (hτ : τ ∈ Icc 0 (β^2)) (x : ℝ) :
    backwardTauJReaction β μ a (τ,x) ≤ supportingJConstant β * backwardTauJ β μ (τ,x)^2 := by
  have hc := backwardTauC_pos_le_one β hβ μ τ x hτ
  have hd := backwardTauD_uniform_bound β μ 2 (τ,x)
  have hm := jetMatrix4_norm_le a (backwardTauD β μ 2 (τ,x))
    (backwardTauD β μ 3 (τ,x)) (uniformSpatialConstant β 2)
    (backwardTauD β μ 2 (τ,x)) (backwardTauD β μ 3 (τ,x))
    (backwardTauD β μ 4 (τ,x)) (backwardTauD β μ 5 (τ,x))
    (by simpa only [abs_of_nonneg ha.1] using ha.2)
    (by simpa only [abs_of_nonneg hc.1.le] using hc.2) hd
  have hdot := jetDot4_le_norm_mul
    (backwardTauD β μ 2 (τ,x)) (backwardTauD β μ 3 (τ,x))
    (backwardTauD β μ 4 (τ,x)) (backwardTauD β μ 5 (τ,x))
    (a*backwardTauD β μ 2 (τ,x)^2)
    (3*a*backwardTauD β μ 2 (τ,x)*backwardTauD β μ 3 (τ,x))
    (a*(4*backwardTauD β μ 2 (τ,x)*backwardTauD β μ 4 (τ,x)+3*backwardTauD β μ 3 (τ,x)^2))
    (a*(5*backwardTauD β μ 2 (τ,x)*backwardTauD β μ 5 (τ,x)+
      10*backwardTauD β μ 3 (τ,x)*backwardTauD β μ 4 (τ,x)))
  have hm' : jetNorm4
      (a*backwardTauD β μ 2 (τ,x)^2)
      (3*a*backwardTauD β μ 2 (τ,x)*backwardTauD β μ 3 (τ,x))
      (a*(4*backwardTauD β μ 2 (τ,x)*backwardTauD β μ 4 (τ,x)+3*backwardTauD β μ 3 (τ,x)^2))
      (a*(5*backwardTauD β μ 2 (τ,x)*backwardTauD β μ 5 (τ,x)+
        10*backwardTauD β μ 3 (τ,x)*backwardTauD β μ 4 (τ,x))) ≤
      supportingJConstant β * backwardTauJ β μ (τ,x) := by
    convert hm using 1
    · dsimp [jetMatrix4]
      congr 1 <;> ring
    · rfl
  have hh := mul_le_mul_of_nonneg_left hm' (backwardTauJ_pos β hβ μ hτ x).le
  dsimp only [backwardTauJReaction] at ⊢
  change _ ≤ supportingJConstant β * backwardTauJ β μ (τ,x)^2
  have : jetNorm4 (backwardTauD β μ 2 (τ,x)) (backwardTauD β μ 3 (τ,x))
      (backwardTauD β μ 4 (τ,x)) (backwardTauD β μ 5 (τ,x)) = backwardTauJ β μ (τ,x) := rfl
  rw [this] at hdot
  exact hdot.trans (by nlinarith [hh])

/-- The exact norm-generator identity, including its Cauchy--Schwarz remainder. -/
theorem finiteCell_generator_J_identity {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauJ β (Paper.parisiSchemeMeasure s)) (τ,x) =
      backwardTauJReaction β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) /
        backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x) -
      backwardTauJRemainder β (Paper.parisiSchemeMeasure s) (τ,x) /
        (2*backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x)^3) := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
  have hJne := (backwardTauJ_pos β hβ (Paper.parisiSchemeMeasure s) hg x).ne'
  dsimp only [backwardGenerator]
  rw [(hasDerivAt_finiteCell_backwardTauJ s β hβ hp hτ x).deriv,
    deriv2_backwardTauJ_spatial β hβ _ τ x hg,
    (hasDerivAt_backwardTauJ_spatial β hβ _ τ x hg).deriv]
  simp only [backwardTauJt,backwardTauJx,backwardTauJxx,backwardTauJRemainder,
    backwardTauJReaction,backwardCellDrift,jetDot4,
    backwardTauForcing_two,backwardTauForcing_three,backwardTauForcing_four,backwardTauForcing_five,
    backwardCtJet,backwardDtJet,backwardEtJet,backwardFtJet]
  field_simp [hJne]
  ring

/-- The literal estimate T J ≤ Kβ J, for the genuine finite-step solution. -/
theorem finiteCell_generator_J_le {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardTauJ β (Paper.parisiSchemeMeasure s)) (τ,x) ≤
      supportingJConstant β * backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x) := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
  have hJ := backwardTauJ_pos β hβ (Paper.parisiSchemeMeasure s) hg x
  have hreact := backwardTauJReaction_le β hβ (Paper.parisiSchemeMeasure s)
    (s.m p) ⟨s.m_nonneg hp,s.m_le_one hp⟩ hg x
  have hrem := backwardTauJRemainder_nonneg β (Paper.parisiSchemeMeasure s) (τ,x)
  rw [finiteCell_generator_J_identity s β hβ hp hτ x]
  have hr : 0 ≤ backwardTauJRemainder β (Paper.parisiSchemeMeasure s) (τ,x) /
      (2*backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x)^3) := div_nonneg hrem (by positivity)
  have hdiv : backwardTauJReaction β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x) /
      backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x) ≤
      supportingJConstant β * backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x) := by
    apply (div_le_iff₀ hJ).mpr
    nlinarith [hreact]
  linarith

/-- Exact terminal norm polynomial, before taking the ratio. -/
theorem backwardTauJ_terminal_sq (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardTauJ β μ (0,x)^2 = backwardTauD β μ 2 (0,x)^2 *
      (576*Real.tanh x^6-732*Real.tanh x^4+236*Real.tanh x^2+5) := by
  simp only [backwardTauJ,jetNorm4_sq,backwardTauD,backwardTime,zero_div,sub_zero]
  rw [show backwardD β μ 2 (1,x) = Paper.sech x^2 from backwardC_terminal β μ x,
    backwardD_three_terminal,backwardD_four_terminal,backwardD_five_terminal]
  have hi : Paper.sech x^2 = 1-Real.tanh x^2 := by
    linarith [Paper.tanh_sq_add_sech_sq x]
  have hi4 : Paper.sech x^4 = (1-Real.tanh x^2)^2 := by
    rw [show Paper.sech x^4 = (Paper.sech x^2)^2 by ring,hi]
  rw [hi4,hi]
  ring

/-- The literal quotient in display (29), including its bound by 85. -/
theorem backwardTauJ_terminal_ratio (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardTauJ β μ (0,x)^2 / backwardTauD β μ 2 (0,x)^2 =
      576*Real.tanh x^6-732*Real.tanh x^4+236*Real.tanh x^2+5 ∧
    backwardTauJ β μ (0,x)^2 / backwardTauD β μ 2 (0,x)^2 ≤ 85 := by
  have hC : backwardTauD β μ 2 (0,x) ≠ 0 := by
    simp only [backwardTauD,backwardTime,zero_div,sub_zero]
    change backwardC β μ (1,x) ≠ 0
    rw [backwardC_terminal]
    exact pow_ne_zero 2 (Paper.sech_pos x).ne'
  have heq : backwardTauJ β μ (0,x)^2 / backwardTauD β μ 2 (0,x)^2 =
      576*Real.tanh x^6-732*Real.tanh x^4+236*Real.tanh x^2+5 := by
    rw [backwardTauJ_terminal_sq]
    field_simp
  refine ⟨heq,?_⟩
  rw [heq]
  exact terminal_derivative_polynomial_le _ (Paper.tanh_sq_le_one x)

theorem backwardTauJ_terminal_le (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    backwardTauJ β μ (0,x) ≤ 10*backwardTauD β μ 2 (0,x) := by
  have hC : 0 < backwardTauD β μ 2 (0,x) := by
    simp only [backwardTauD,backwardTime,zero_div,sub_zero]
    change 0 < backwardC β μ (1,x)
    rw [backwardC_terminal]
    exact sq_pos_of_pos (Paper.sech_pos x)
  have hrat := (backwardTauJ_terminal_ratio β μ x).2
  have hs := (div_le_iff₀ (sq_pos_of_pos hC)).mp hrat
  have hJ : 0 ≤ backwardTauJ β μ (0,x) := jetNorm4_nonneg _ _ _ _
  nlinarith

/-- The literal exponential comparison barrier in display (30). -/
def backwardJBarrier (β : ℝ) (μ : Paper.ParisiMeasure) (q : ℝ × ℝ) : ℝ :=
  10*Real.exp (supportingJConstant β*q.1)*backwardTauD β μ 2 q-backwardTauJ β μ q

theorem backwardJBarrier_initial_nonneg (β : ℝ) (μ : Paper.ParisiMeasure) (x : ℝ) :
    0 ≤ backwardJBarrier β μ (0,x) := by
  have hh := backwardTauJ_terminal_le β μ x
  simpa only [backwardJBarrier,mul_zero,Real.exp_zero,mul_one] using sub_nonneg.mpr hh

theorem hasDerivAt_backwardJBarrier_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (τ x : ℝ) (hτ : τ ∈ Icc 0 (β^2)) :
    HasDerivAt (fun y => backwardJBarrier β μ (τ,y))
      (10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 3 (τ,x)-
        backwardTauJx β μ (τ,x)) x :=
  ((hasDerivAt_backwardTauD_spatial β hβ μ 2 τ x hτ).const_mul
    (10*Real.exp (supportingJConstant β*τ))).sub
      (hasDerivAt_backwardTauJ_spatial β hβ μ τ x hτ)

theorem deriv2_backwardJBarrier_spatial (β : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (τ x : ℝ) (hτ : τ ∈ Icc 0 (β^2)) :
    deriv (deriv (fun y => backwardJBarrier β μ (τ,y))) x =
      10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 4 (τ,x)-
        backwardTauJxx β μ (τ,x) := by
  have heq : deriv (fun y => backwardJBarrier β μ (τ,y)) =
      fun y => 10*Real.exp (supportingJConstant β*τ)*backwardTauD β μ 3 (τ,y)-
        backwardTauJx β μ (τ,y) :=
    funext fun y => (hasDerivAt_backwardJBarrier_spatial β hβ μ τ y hτ).deriv
  rw [heq]
  exact (((hasDerivAt_backwardTauD_spatial β hβ μ 3 τ x hτ).const_mul
    (10*Real.exp (supportingJConstant β*τ))).sub
    (hasDerivAt_backwardTauJx_spatial β hβ μ τ x hτ)).deriv

theorem hasDerivAt_finiteCell_backwardJBarrier {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    HasDerivAt (fun r => backwardJBarrier β (Paper.parisiSchemeMeasure s) (r,x))
      (10*Real.exp (supportingJConstant β*τ)*
        (supportingJConstant β*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x)+
          backwardTauForcing β (Paper.parisiSchemeMeasure s) (s.m p) 2 (τ,x))-
        backwardTauJt β (Paper.parisiSchemeMeasure s) (s.m p) (τ,x)) τ := by
  have hq := backwardCell_strict_of_mem s β hβ hτ
  have he := ((Real.hasDerivAt_exp (supportingJConstant β*τ)).comp τ
    ((hasDerivAt_id τ).const_mul (supportingJConstant β))).const_mul 10
  have hc := hasDerivAt_finiteCell_backwardTauD s β hβ hp hq 2 hτ x
  have hJ := hasDerivAt_finiteCell_backwardTauJ s β hβ hp hτ x
  convert (he.mul hc).sub hJ using 1
  · funext r
    rfl
  · dsimp
    ring

/-- Exact generator of the displayed exponential barrier. -/
theorem finiteCell_JBarrier_generator_identity {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardJBarrier β (Paper.parisiSchemeMeasure s)) (τ,x)-
        supportingJConstant β*backwardJBarrier β (Paper.parisiSchemeMeasure s) (τ,x) =
      10*Real.exp (supportingJConstant β*τ)*
        (s.m p*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x)^2)-
      (backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
        (backwardTauJ β (Paper.parisiSchemeMeasure s)) (τ,x)-
          supportingJConstant β*backwardTauJ β (Paper.parisiSchemeMeasure s) (τ,x)) := by
  have hg := backwardCell_mem_global s β hp ⟨hτ.1.le,hτ.2.le⟩
  dsimp only [backwardGenerator]
  rw [(hasDerivAt_finiteCell_backwardJBarrier s β hβ hp hτ x).deriv,
    deriv2_backwardJBarrier_spatial β hβ _ τ x hg,
    (hasDerivAt_backwardJBarrier_spatial β hβ _ τ x hg).deriv,
    (hasDerivAt_finiteCell_backwardTauJ s β hβ hp hτ x).deriv,
    deriv2_backwardTauJ_spatial β hβ _ τ x hg,
    (hasDerivAt_backwardTauJ_spatial β hβ _ τ x hg).deriv,
    backwardTauForcing_two]
  dsimp only [backwardJBarrier,backwardCellDrift,backwardCtJet]
  ring

/-- The actual exponential barrier is a supersolution on every finite cell. -/
theorem finiteCell_JBarrier_supersolution {k : ℕ} (s : SpinGlass.Targets.RSBScheme k)
    (β : ℝ) (hβ : β ≠ 0) {p : ℕ} (hp : p ≤ k+1) {τ : ℝ}
    (hτ : τ ∈ Ioo (backwardCellStart s β p) (backwardCellEnd s β p)) (x : ℝ) :
    0 ≤ backwardGenerator (backwardCellDrift β (Paper.parisiSchemeMeasure s) (s.m p))
      (backwardJBarrier β (Paper.parisiSchemeMeasure s)) (τ,x)-
        supportingJConstant β*backwardJBarrier β (Paper.parisiSchemeMeasure s) (τ,x) := by
  rw [finiteCell_JBarrier_generator_identity s β hβ hp hτ x]
  have hh := finiteCell_generator_J_le s β hβ hp hτ x
  have hsource : 0 ≤ 10*Real.exp (supportingJConstant β*τ)*
      (s.m p*backwardTauD β (Paper.parisiSchemeMeasure s) 2 (τ,x)^2) := by
    have hm := s.m_nonneg hp
    positivity
  linarith

end FRSB
