module

public import FRSB.ForwardLeftAtoms

@[expose] public section

/-! Actual excluded-atom bridge jets, with derivative and integral formulas. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped ContDiff Topology
namespace FRSB

def forwardBridgeLeftJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  ∫ t : Overlap, if (t : ℝ) < s then
    forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
      (t,forwardBridgePoint β s hs path x t) else 0 ∂(μ : Measure Overlap)

lemma measurable_forwardBridgeLeftJet_integrand (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Measurable (fun t : Overlap => if (t : ℝ) < s then
      forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
        (t, forwardBridgePoint β s hs path x t) else 0) := by
  have hc : Continuous (fun t : Overlap => forwardBridgePoint β s hs path x t) :=
    (continuous_forwardBridgePoint β s hs).comp (show Continuous
      (fun t : Overlap => ((path, x), t)) by fun_prop)
  apply Measurable.ite (measurableSet_lt (by fun_prop) measurable_const)
  · exact ((show Continuous (fun t : Overlap => forwardBridgeFraction s t) by
      unfold forwardBridgeFraction; fun_prop).pow j |>.mul
        ((continuous_parisiSpatialField β μ j).comp (continuous_subtype_val.prodMk hc))).measurable
  · exact measurable_const

lemma norm_forwardBridgeLeftJet_integrand_succ_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    ‖if (t : ℝ) < s then forwardBridgeFraction s t ^ (j + 1) *
      parisiSpatialField β μ (j + 1) (t, forwardBridgePoint β s hs path x t) else 0‖ ≤
        uniformSpatialConstant β j := by
  split_ifs
  · rw [norm_mul, norm_pow, Real.norm_of_nonneg (forwardBridgeFraction_mem s hs.1 t).1]
    exact (mul_le_mul (pow_le_one₀ (forwardBridgeFraction_mem s hs.1 t).1
      (forwardBridgeFraction_mem s hs.1 t).2) (parisiSpatialField_uniform_bound β j μ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · simpa using (uniformSpatialConstant_pos β j).le

lemma norm_forwardBridgeLeftJet_integrand_zero_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) (t : Overlap) :
    ‖if (t : ℝ) < s then forwardBridgeFraction s t ^ (0 : ℕ) *
      parisiSpatialField β μ 0 (t, forwardBridgePoint β s hs path x t) else 0‖ ≤
        β ^ 2 + |x| + 2 * |β| * ‖path‖ := by
  split_ifs
  · simp only [pow_zero, one_mul, parisiSpatialField, Real.norm_eq_abs]
    have hp := norm_forwardBridgePoint_le β s hs path x t
    rw [Real.norm_eq_abs] at hp
    have hu := parisiPotential_absolute_growth β μ t (forwardBridgePoint β s hs path x t) t.property
    linarith
  · simp only [norm_zero]
    positivity

lemma integrable_forwardBridgeLeftJet_integrand (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    Integrable (fun t : Overlap => if (t : ℝ) < s then
      forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
        (t, forwardBridgePoint β s hs path x t) else 0) (μ : Measure Overlap) := by
  cases j with
  | zero =>
    exact (integrable_const (β ^ 2 + |x| + 2 * |β| * ‖path‖)).mono'
      (measurable_forwardBridgeLeftJet_integrand β μ s hs 0 path x).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_forwardBridgeLeftJet_integrand_zero_le β μ s hs path x))
  | succ j =>
    exact (integrable_const (uniformSpatialConstant β j)).mono'
      (measurable_forwardBridgeLeftJet_integrand β μ s hs (j + 1) path x).aestronglyMeasurable
      (Filter.Eventually.of_forall (norm_forwardBridgeLeftJet_integrand_succ_le β μ s hs j path x))

theorem norm_forwardBridgeLeftJet_succ_le (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    ‖forwardBridgeLeftJet β μ s hs (j + 1) path x‖ ≤ uniformSpatialConstant β j := by
  exact norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall
    (norm_forwardBridgeLeftJet_integrand_succ_le β μ s hs j path x)) |>.trans_eq (by simp)

theorem continuous_forwardBridgeLeftJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    Continuous (fun p : ForwardBridgePath × ℝ => forwardBridgeLeftJet β μ s hs j p.1 p.2) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  let C := if j = 0 then β ^ 2 + (|p₀.2| + 1) + 2 * |β| * (‖p₀.1‖ + 1)
    else uniformSpatialConstant β (j - 1)
  apply continuousAt_of_dominated (μ := (μ : Measure Overlap))
    (F := fun (p : ForwardBridgePath × ℝ) (t : Overlap) => if (t : ℝ) < s then
      forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
        (t, forwardBridgePoint β s hs p.1 p.2 t) else 0)
    (bound := fun _ => C)
  · exact Filter.Eventually.of_forall fun p =>
      (measurable_forwardBridgeLeftJet_integrand β μ s hs j p.1 p.2).aestronglyMeasurable
  · have hp := ((continuous_norm.comp continuous_fst).tendsto p₀).eventually
      (Iio_mem_nhds (lt_add_one ‖p₀.1‖))
    have hx := ((continuous_abs.comp continuous_snd).tendsto p₀).eventually
      (Iio_mem_nhds (lt_add_one |p₀.2|))
    filter_upwards [hp, hx] with p hp hx
    simp only [Function.comp_def] at hp hx
    exact Filter.Eventually.of_forall fun t => by
      cases j with
      | zero =>
        have hb := norm_forwardBridgeLeftJet_integrand_zero_le β μ s hs p.1 p.2 t
        dsimp [C]
        exact hb.trans (by nlinarith [abs_nonneg β])
      | succ j =>
        simpa only [C, Nat.succ_ne_zero, ite_false, Nat.add_one_sub_one] using
          norm_forwardBridgeLeftJet_integrand_succ_le β μ s hs j p.1 p.2 t
  · exact integrable_const C
  · exact Filter.Eventually.of_forall fun t => by
      by_cases ht : (t : ℝ) < s
      · have hc : Continuous (fun p : ForwardBridgePath × ℝ =>
          forwardBridgeFraction s t ^ j * parisiSpatialField β μ j
            (t, forwardBridgePoint β s hs p.1 p.2 t)) :=
          continuous_const.mul ((continuous_parisiSpatialField β μ j).comp
            (continuous_const.prodMk ((continuous_forwardBridgePoint β s hs).comp
              (continuous_id.prodMk continuous_const))))
        simpa only [ht, ite_true] using hc.continuousAt
      · simpa only [ht, ite_false] using (continuous_const :
          Continuous (fun _ : ForwardBridgePath × ℝ => (0 : ℝ))).continuousAt

theorem hasDerivAt_forwardBridgeLeftJet (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    HasDerivAt (forwardBridgeLeftJet β μ s hs j path)
      (forwardBridgeLeftJet β μ s hs (j + 1) path x) x := by
  apply hasDerivAt_integral_uniform (μ : Measure Overlap)
    (fun y t => if (t : ℝ) < s then forwardBridgeFraction s t ^ j *
      parisiSpatialField β μ j (t, forwardBridgePoint β s hs path y t) else 0)
    (fun y t => if (t : ℝ) < s then forwardBridgeFraction s t ^ (j + 1) *
      parisiSpatialField β μ (j + 1) (t, forwardBridgePoint β s hs path y t) else 0)
    x (uniformSpatialConstant β j)
  · intro y
    exact (measurable_forwardBridgeLeftJet_integrand β μ s hs j path y).aestronglyMeasurable
  · exact integrable_forwardBridgeLeftJet_integrand β μ s hs j path x
  · exact (measurable_forwardBridgeLeftJet_integrand β μ s hs (j + 1) path x).aestronglyMeasurable
  · exact norm_forwardBridgeLeftJet_integrand_succ_le β μ s hs j path
  · intro y t
    by_cases ht : (t : ℝ) < s
    · simp only [ht, ite_true]
      have hd := ((hasDerivAt_parisiSpatialField β μ j t
        (forwardBridgePoint β s hs path y t) t.property).comp y
        (((hasDerivAt_id y).const_mul (forwardBridgeFraction s t)).add_const
          (β * (path t - forwardBridgeFraction s t * path ⟨s, hs.1.le, hs.2⟩)))).const_mul
            (forwardBridgeFraction s t ^ j)
      convert hd using 1
      · rfl
      · rw [pow_succ]
        ring
    · simp only [ht, ite_false]
      exact hasDerivAt_const y 0

theorem iteratedDeriv_forwardBridgeLeftAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    iteratedDeriv j (forwardBridgeLeftAction β μ s hs path) x =
      forwardBridgeLeftJet β μ s hs j path x := by
  induction j generalizing x with
  | zero => simp only [iteratedDeriv_zero, forwardBridgeLeftAction, forwardBridgeLeftJet, pow_zero, one_mul, parisiSpatialField]
  | succ j ih =>
    have he : iteratedDeriv j (forwardBridgeLeftAction β μ s hs path) =
        forwardBridgeLeftJet β μ s hs j path := funext ih
    rw [iteratedDeriv_succ, he]
    exact (hasDerivAt_forwardBridgeLeftJet β μ s hs j path x).deriv

theorem contDiff_forwardBridgeLeftAction (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) :
    ContDiff ℝ ∞ (forwardBridgeLeftAction β μ s hs path) := by
  apply contDiff_of_differentiable_iteratedDeriv
  intro j hj
  have he : iteratedDeriv j (forwardBridgeLeftAction β μ s hs path) =
      forwardBridgeLeftJet β μ s hs j path :=
    funext (iteratedDeriv_forwardBridgeLeftAction β μ s hs j path)
  rw [he]
  exact fun x => (hasDerivAt_forwardBridgeLeftJet β μ s hs j path x).differentiableAt

def forwardBridgeLeftPathFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) : ℝ :=
  Real.exp (-forwardBridgeLeftAction β μ s hs path x)

theorem forwardBridgeLeftPathFactor_pos (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    0 < forwardBridgeLeftPathFactor β μ s hs path x := Real.exp_pos _

theorem forwardBridgeLeftPathFactor_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    forwardBridgeLeftPathFactor β μ s hs path x ≤ 1 :=
  Real.exp_le_one_iff.mpr (neg_nonpos.mpr (forwardBridgeLeftAction_nonneg β μ s hs path x))

theorem contDiff_forwardBridgeLeftPathFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) :
    ContDiff ℝ ∞ (forwardBridgeLeftPathFactor β μ s hs path) :=
  (contDiff_forwardBridgeLeftAction β μ s hs path).neg.exp

theorem continuous_iteratedDeriv_forwardBridgeLeftPathFactor (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) :
    Continuous (fun p : ForwardBridgePath × ℝ =>
      iteratedDeriv j (forwardBridgeLeftPathFactor β μ s hs p.1) p.2) := by
  induction j using Nat.strong_induction_on with
  | h j ih =>
    cases j with
    | zero =>
      have hc := Real.continuous_exp.comp (continuous_forwardBridgeLeftJet β μ s hs 0).neg
      simpa only [iteratedDeriv_zero, forwardBridgeLeftPathFactor, forwardBridgeLeftAction,
        forwardBridgeLeftJet, pow_zero, one_mul, parisiSpatialField, Function.comp_def, Pi.neg_apply] using hc
    | succ n =>
      have he : (fun p : ForwardBridgePath × ℝ =>
          iteratedDeriv (n + 1) (forwardBridgeLeftPathFactor β μ s hs p.1) p.2) =
          fun p => ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
            (-1 * forwardBridgeLeftJet β μ s hs (i + 1) p.1 p.2) *
              iteratedDeriv (n - i) (forwardBridgeLeftPathFactor β μ s hs p.1) p.2 := by
        funext p
        have h := exp_neg_mul_iteratedDeriv_formula (forwardBridgeLeftAction β μ s hs p.1) 1
          (contDiff_forwardBridgeLeftAction β μ s hs p.1) n p.2
        unfold forwardBridgeLeftPathFactor
        simpa only [neg_mul, one_mul, forwardBridgeLeftPathFactor,
          iteratedDeriv_forwardBridgeLeftAction] using h
      rw [he]
      apply continuous_finsetSum
      intro i hi
      exact (continuous_const.mul (continuous_const.mul
        (continuous_forwardBridgeLeftJet β μ s hs (i + 1)))).mul (ih (n - i) (by omega))

theorem norm_iteratedDeriv_forwardBridgeLeftPathFactor_le (β : ℝ) (μ : ParisiMeasure)
    (s : ℝ) (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (path : ForwardBridgePath) (x : ℝ) :
    ‖iteratedDeriv j (forwardBridgeLeftPathFactor β μ s hs path) x‖ ≤
      forwardBridgeExponentialConstant β j * forwardBridgeLeftPathFactor β μ s hs path x := by
  have h := norm_iteratedDeriv_exp_neg_mul_le (forwardBridgeLeftAction β μ s hs path) 1
    (contDiff_forwardBridgeLeftAction β μ s hs path) (by norm_num)
    (forwardBridgeDerivativeConstant β) (fun n => (uniformSpatialConstant_pos β _).le)
    (fun n y => by
      rw [iteratedDeriv_forwardBridgeLeftAction]
      exact norm_forwardBridgeLeftJet_succ_le β μ s hs n path y) j x
  unfold forwardBridgeLeftPathFactor
  simpa only [forwardBridgeLeftPathFactor, forwardBridgeExponentialConstant, neg_mul, one_mul] using h

lemma integrable_forwardBridgeLeftPathFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    Integrable (fun path => forwardBridgeLeftPathFactor β μ s hs path x) canonicalWienerMeasure :=
  (integrable_const (1 : ℝ)).mono'
    (((continuous_iteratedDeriv_forwardBridgeLeftPathFactor β μ s hs 0).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun path => by
      rw [Real.norm_of_nonneg (forwardBridgeLeftPathFactor_pos β μ s hs path x).le]
      exact forwardBridgeLeftPathFactor_le_one β μ s hs path x)

theorem iteratedDeriv_forwardBridgeLeftFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (j : ℕ) (x : ℝ) :
    iteratedDeriv j (forwardBridgeLeftFactor β μ s hs) x =
      ∫ path, iteratedDeriv j (forwardBridgeLeftPathFactor β μ s hs path) x ∂canonicalWienerMeasure := by
  have he : forwardBridgeLeftFactor β μ s hs = fun y =>
      ∫ path, forwardBridgeLeftPathFactor β μ s hs path y ∂canonicalWienerMeasure :=
    funext (forwardBridgeLeftFactor_eq_integral β μ s hs)
  rw [he]
  apply iteratedDeriv_integral_uniform canonicalWienerMeasure
    (fun y path => forwardBridgeLeftPathFactor β μ s hs path y)
    (contDiff_forwardBridgeLeftPathFactor β μ s hs)
    (integrable_forwardBridgeLeftPathFactor β μ s hs)
    (fun n y => ((continuous_iteratedDeriv_forwardBridgeLeftPathFactor β μ s hs n).comp
      (show Continuous (fun path : ForwardBridgePath => (path, y)) by fun_prop)).aestronglyMeasurable)
    (fun n => forwardBridgeExponentialConstant β (n + 1))
  intro n y path
  exact (norm_iteratedDeriv_forwardBridgeLeftPathFactor_le β μ s hs (n + 1) path y).trans
    (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β _)
      (forwardBridgeLeftPathFactor_le_one β μ s hs path y))

theorem contDiff_forwardBridgeLeftFactor (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) : ContDiff ℝ ∞ (forwardBridgeLeftFactor β μ s hs) := by
  have he : forwardBridgeLeftFactor β μ s hs = fun y =>
      ∫ path, forwardBridgeLeftPathFactor β μ s hs path y ∂canonicalWienerMeasure :=
    funext (forwardBridgeLeftFactor_eq_integral β μ s hs)
  rw [he]
  apply contDiff_integral_uniform canonicalWienerMeasure
    (fun y path => forwardBridgeLeftPathFactor β μ s hs path y)
    (contDiff_forwardBridgeLeftPathFactor β μ s hs)
    (integrable_forwardBridgeLeftPathFactor β μ s hs)
    (fun n y => ((continuous_iteratedDeriv_forwardBridgeLeftPathFactor β μ s hs n).comp
      (show Continuous (fun path : ForwardBridgePath => (path, y)) by fun_prop)).aestronglyMeasurable)
    (fun n => forwardBridgeExponentialConstant β (n + 1))
  intro n y path
  exact (norm_iteratedDeriv_forwardBridgeLeftPathFactor_le β μ s hs (n + 1) path y).trans
    (mul_le_of_le_one_right (forwardBridgeExponentialConstant_nonneg β _)
      (forwardBridgeLeftPathFactor_le_one β μ s hs path y))

lemma norm_forwardBridgeLeftAction_deriv_le_one (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (path : ForwardBridgePath) (x : ℝ) :
    ‖deriv (forwardBridgeLeftAction β μ s hs path) x‖ ≤ 1 := by
  have he : forwardBridgeLeftAction β μ s hs path = forwardBridgeLeftJet β μ s hs 0 path := by
    funext y
    simp only [forwardBridgeLeftAction, forwardBridgeLeftJet, pow_zero, one_mul, parisiSpatialField]
  rw [he, (hasDerivAt_forwardBridgeLeftJet β μ s hs 0 path x).deriv]
  have hbound : ∀ᵐ t : Overlap ∂(μ : Measure Overlap),
      ‖if (t : ℝ) < s then forwardBridgeFraction s t ^ 1 *
        parisiSpatialField β μ 1 (t, forwardBridgePoint β s hs path x t) else 0‖ ≤ 1 :=
    Filter.Eventually.of_forall fun t => by
      split_ifs
      · have he : parisiSpatialField β μ 1 = parisiGradient β μ := by
          funext p
          simp only [parisiSpatialField, bcfSpatialDerivative, iteratedDeriv_zero,
            parisiGradient, bcfTranslate_zero]
        rw [he, pow_one, norm_mul, Real.norm_of_nonneg (forwardBridgeFraction_mem s hs.1 t).1]
        exact (mul_le_mul (forwardBridgeFraction_mem s hs.1 t).2
          (norm_parisiGradient_le_one β μ _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
      · simp
  exact (norm_integral_le_of_norm_le_const hbound).trans_eq (by simp)

lemma forwardBridgeLeftFactor_first_relative_bound (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖deriv (forwardBridgeLeftFactor β μ s hs) x‖ ≤ forwardBridgeLeftFactor β μ s hs x := by
  have hpoint (path : ForwardBridgePath) :
      ‖iteratedDeriv 1 (forwardBridgeLeftPathFactor β μ s hs path) x‖ ≤
        forwardBridgeLeftPathFactor β μ s hs path x := by
    have hh := ((contDiff_forwardBridgeLeftAction β μ s hs path).differentiable
      (by simp) x).hasDerivAt.neg.exp
    have he : (fun y => Real.exp (-forwardBridgeLeftAction β μ s hs path y)) =
        forwardBridgeLeftPathFactor β μ s hs path := rfl
    simp only [Pi.neg_apply] at hh
    rw [he] at hh
    rw [iteratedDeriv_one, hh.deriv, norm_mul, norm_neg,
      Real.norm_of_nonneg (Real.exp_pos _).le]
    exact (mul_le_mul_of_nonneg_left (norm_forwardBridgeLeftAction_deriv_le_one β μ s hs path x)
      (forwardBridgeLeftPathFactor_pos β μ s hs path x).le).trans_eq (mul_one _)
  have hi : Integrable (fun path => iteratedDeriv 1 (forwardBridgeLeftPathFactor β μ s hs path) x)
      canonicalWienerMeasure := (integrable_forwardBridgeLeftPathFactor β μ s hs x).mono'
    (((continuous_iteratedDeriv_forwardBridgeLeftPathFactor β μ s hs 1).comp
      (show Continuous (fun path : ForwardBridgePath => (path, x)) by fun_prop)).aestronglyMeasurable)
    (Filter.Eventually.of_forall hpoint)
  rw [← iteratedDeriv_one, iteratedDeriv_forwardBridgeLeftFactor]
  rw [forwardBridgeLeftFactor_eq_integral]
  exact (norm_integral_le_integral_norm _).trans
    (integral_mono hi.norm (integrable_forwardBridgeLeftPathFactor β μ s hs x) hpoint)

/-- The sharp unit slope bound. -/
theorem forwardBridgeLeftCorrection_slope_bound (β : ℝ) (μ : ParisiMeasure) (s : ℝ)
    (hs : s ∈ Ioc (0 : ℝ) 1) (x : ℝ) :
    ‖deriv (forwardBridgeLeftCorrection β μ s hs) x‖ ≤ 1 := by
  have h := ((contDiff_forwardBridgeLeftFactor β μ s hs).differentiable (by simp) x).hasDerivAt.log
    (forwardBridgeLeftFactor_pos β μ s hs x).ne' |>.neg
  have he : (-fun y => Real.log (forwardBridgeLeftFactor β μ s hs y)) =
      forwardBridgeLeftCorrection β μ s hs :=
    funext (fun y => (forwardBridgeLeftCorrection_eq_negativeLog β μ s hs y).symm)
  rw [he] at h
  rw [h.deriv, norm_neg, norm_div, Real.norm_of_nonneg (forwardBridgeLeftFactor_pos β μ s hs x).le]
  exact (div_le_one (forwardBridgeLeftFactor_pos β μ s hs x)).mpr
    (forwardBridgeLeftFactor_first_relative_bound β μ s hs x)


end FRSB
