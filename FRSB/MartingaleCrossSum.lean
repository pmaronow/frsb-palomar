module

public import StochasticCalculus.MartingaleLeftSum
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! Genuine martingale conditioning for the cross term between a terminal
martingale increment and an adapted finite Brownian/martingale left sum. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal Topology
namespace FRSB

theorem integral_known_mul_martingaleIncrement_eq_zero {Ω ι : Type*}
    [MeasurableSpace Ω] [Preorder ι] {P : Measure Ω}
    {V : Filtration ι ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {M : ι → Ω → ℝ} (hM : Martingale M V P) {a b : ι} (hab : a ≤ b)
    (Z : Ω → ℝ) (hZ : StronglyMeasurable[V a] Z)
    (hprod : Integrable (fun sample => Z sample*(M b sample-M a sample)) P) :
    (∫sample,Z sample*(M b sample-M a sample) ∂P) = 0 := by
  let D := M b-M a
  have hDint : Integrable D P := (hM.integrable b).sub (hM.integrable a)
  have hpull := condExp_mul_of_stronglyMeasurable_left hZ hprod hDint
  have hDzero : P[D | V a] =ᵐ[P] 0 := by
    have hs := condExp_sub (hM.integrable b) (hM.integrable a) (V a)
    filter_upwards [hs,hM.condExp_ae_eq hab,Filter.Eventually.of_forall (congrFun
      (condExp_of_stronglyMeasurable (V.le a) (hM.stronglyMeasurable a) (hM.integrable a)))]
      with sample hsub hfuture hpast
    change P[D | V a] sample = 0
    change P[D | V a] sample = (P[M b | V a]-P[M a | V a]) sample at hsub
    rw [hsub]
    simp only [Pi.sub_apply,hfuture,hpast,sub_self]
  have hz : P[Z*D | V a] =ᵐ[P] 0 := by
    filter_upwards [hpull,hDzero] with sample hp hd
    change P[Z*D | V a] sample = Z sample*P[D | V a] sample at hp
    change P[Z*D | V a] sample = 0
    rw [hp,hd]
    simp only [Pi.zero_apply,mul_zero]
  calc
    (∫sample,Z sample*(M b sample-M a sample) ∂P) = ∫sample,P[Z*D | V a] sample ∂P :=
      (integral_condExp (V.le a)).symm
    _ = 0 := by rw [integral_congr_ae hz];simp

/-- A bounded known coefficient preserves square integrability. -/
theorem memLp_two_mul_bounded {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (Z D : Ω → ℝ) (hZ : AEStronglyMeasurable Z P) (hD : MemLp D 2 P)
    (K : ℝ≥0) (hK : ∀ sample,‖Z sample‖ ≤ K) :
    MemLp (fun sample => Z sample*D sample) 2 P := by
  apply hD.of_le_mul (c := K) (hZ.mul hD.aestronglyMeasurable)
  exact .of_forall fun sample => by
    rw [Pi.mul_apply,norm_mul]
    exact mul_le_mul_of_nonneg_right (hK sample) (norm_nonneg _)

/-- Future and past martingale conditioning remove every cross term outside
the same observation interval. The coefficient is only known at its left end. -/
theorem terminal_martingale_cross_increment {Ω ι : Type*}
    [MeasurableSpace Ω] [Preorder ι] {P : Measure Ω}
    {V : Filtration ι ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {M J : ι → Ω → ℝ} (hM : Martingale M V P) (hJ : Martingale J V P)
    (hM2 : ∀ t,MemLp (M t) 2 P) (hJ2 : ∀ t,MemLp (J t) 2 P)
    {o a b T : ι} (hoa : o ≤ a) (hab : a ≤ b) (hbT : b ≤ T)
    (H : Ω → ℝ) (hH : StronglyMeasurable[V a] H)
    (K : ℝ≥0) (hK : ∀ sample,‖H sample‖ ≤ K) :
    (∫sample,(M T sample-M o sample)*(H sample*(J b sample-J a sample)) ∂P) =
      ∫sample,(M b sample-M a sample)*H sample*(J b sample-J a sample) ∂P := by
  let A : Ω → ℝ := fun sample => H sample*(J b sample-J a sample)
  have hA2 : MemLp A 2 P := memLp_two_mul_bounded H _
    (hH.mono (V.le a)).aestronglyMeasurable ((hJ2 b).sub (hJ2 a)) K hK
  have hAb : StronglyMeasurable[V b] A :=
    (hH.mono (V.mono hab)).mul ((hJ.stronglyMeasurable b).sub
      ((hJ.stronglyMeasurable a).mono (V.mono hab)))
  have hi (r s : ι) : Integrable (fun sample => (M r sample-M s sample)*A sample) P :=
    memLp_one_iff_integrable.mp (((hM2 r).sub (hM2 s)).mul hA2)
  have hfuture : (∫sample,(M T sample-M b sample)*A sample ∂P) = 0 := by
    have he := integral_known_mul_martingaleIncrement_eq_zero hM hbT A hAb
      (show Integrable (fun sample => A sample*(M T sample-M b sample)) P from by
        simpa only [mul_comm] using hi T b)
    simpa only [mul_comm] using he
  have hZ2 : MemLp (fun sample => (M a sample-M o sample)*H sample) 2 P := by
    simpa only [Pi.sub_apply,mul_comm] using memLp_two_mul_bounded H _
      (hH.mono (V.le a)).aestronglyMeasurable ((hM2 a).sub (hM2 o)) K hK
  have hZa : StronglyMeasurable[V a] (fun sample => (M a sample-M o sample)*H sample) :=
    ((hM.stronglyMeasurable a).sub ((hM.stronglyMeasurable o).mono (V.mono hoa))).mul hH
  have hpast : (∫sample,(M a sample-M o sample)*A sample ∂P) = 0 := by
    have he := integral_known_mul_martingaleIncrement_eq_zero hJ hab _ hZa
      (memLp_one_iff_integrable.mp (hZ2.mul ((hJ2 b).sub (hJ2 a))))
    convert! he using 1
    congr 1
    funext sample
    dsimp only [A]
    ring
  have hsplit : (fun sample => (M T sample-M o sample)*A sample) =
      (fun sample => (M T sample-M b sample)*A sample) +
      (fun sample => (M b sample-M a sample)*A sample) +
      (fun sample => (M a sample-M o sample)*A sample) := by
    funext sample
    simp only [Pi.add_apply]
    ring
  rw [hsplit]
  change (∫sample, ((M T sample-M b sample)*A sample+
    (M b sample-M a sample)*A sample)+(M a sample-M o sample)*A sample ∂P) = _
  have he1 : (∫sample, ((M T sample-M b sample)*A sample+
      (M b sample-M a sample)*A sample)+(M a sample-M o sample)*A sample ∂P) =
      (∫sample,(M T sample-M b sample)*A sample+(M b sample-M a sample)*A sample ∂P) +
        (∫sample,(M a sample-M o sample)*A sample ∂P) :=
    integral_add ((hi T b).add (hi b a)) (hi a o)
  have he2 : (∫sample,(M T sample-M b sample)*A sample+(M b sample-M a sample)*A sample ∂P) =
      (∫sample,(M T sample-M b sample)*A sample ∂P)+
        (∫sample,(M b sample-M a sample)*A sample ∂P) := integral_add (hi T b) (hi b a)
  rw [he1,he2,hfuture,hpast,zero_add,add_zero]
  apply integral_congr_ae
  exact .of_forall fun sample => by dsimp only [A];ring

/-- The exact cross identity for the vendor's genuine uniform adapted left sum. -/
theorem integral_terminal_martingale_mul_uniformLeftSum {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω}
    {V : Filtration ℝ≥0 ‹MeasurableSpace Ω›} [SigmaFiniteFiltration P V]
    {M J H : ℝ≥0 → Ω → ℝ} (hM : Martingale M V P) (hJ : Martingale J V P)
    (hM2 : ∀ t,MemLp (M t) 2 P) (hJ2 : ∀ t,MemLp (J t) 2 P)
    (hH : StronglyAdapted V H) (K : ℝ≥0) (hK : ∀ t sample,‖H t sample‖ ≤ K)
    (T : ℝ≥0) (n : ℕ) :
    (∫sample,(M T sample-M 0 sample)*
      uniformAdaptedMartingaleLeftSumProcess J H T (n+1) T sample ∂P) =
    ∑ i ∈ Finset.range (n+1),∫sample,
      (M (uniformPartitionTime T (n+1) (i+1)) sample-
       M (uniformPartitionTime T (n+1) i) sample)*
      H (uniformPartitionTime T (n+1) i) sample*
      (J (uniformPartitionTime T (n+1) (i+1)) sample-
       J (uniformPartitionTime T (n+1) i) sample) ∂P := by
  have hi (i : ℕ) : Integrable (fun sample => (M T sample-M 0 sample)*
      (H (uniformPartitionTime T (n+1) i) sample*
        (J (uniformPartitionTime T (n+1) (i+1)) sample-
          J (uniformPartitionTime T (n+1) i) sample))) P := by
    exact memLp_one_iff_integrable.mp (((hM2 T).sub (hM2 0)).mul
      (memLp_two_mul_bounded _ _ ((hH _).mono (V.le _)).aestronglyMeasurable
        ((hJ2 _).sub (hJ2 _)) K (hK _)))
  have he : (fun sample => (M T sample-M 0 sample)*
      uniformAdaptedMartingaleLeftSumProcess J H T (n+1) T sample) =
    fun sample => ∑ i ∈ Finset.range (n+1), (M T sample-M 0 sample)*
      (H (uniformPartitionTime T (n+1) i) sample*
        (J (uniformPartitionTime T (n+1) (i+1)) sample-
          J (uniformPartitionTime T (n+1) i) sample)) := by
    funext sample
    rw [uniformAdaptedMartingaleLeftSumProcess_terminal,Finset.mul_sum]
  rw [he,integral_finsetSum (Finset.range (n+1)) (fun i _ => hi i)]
  apply Finset.sum_congr rfl
  intro i hi'
  have hib := uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n)
    (show i+1 ≤ n+1 by have := Finset.mem_range.mp hi';omega)
  exact terminal_martingale_cross_increment hM hJ hM2 hJ2 (by positivity)
    (monotone_uniformPartitionTime_general T (n+1) (Nat.le_succ i)) hib.2 _ (hH _)
    K (hK _)

end FRSB
