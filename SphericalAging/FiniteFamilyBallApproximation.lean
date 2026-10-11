module

public import SphericalAging.ForkBallProjectionLipschitz
public import SphericalAging.ForkNormalizedEnergy
public import Mathlib.Algebra.Order.Chebyshev

public section

/-! Finite-family average, deterministic normalization and literal ball
projection preserve actual coefficient Lipschitz bounds and strong errors.
The quadratic error uses the genuine finite Jensen inequality. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.FiniteFamilyBallApproximation
open FiniteModel HardSphereDynamics ForkBallProjection ForkBallProjectionLipschitz
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N K : ℕ} {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  [IsProbabilityMeasure μ]

@[expose] def average (Z : Fin K→State N) : State N := (K:ℝ)⁻¹ • ∑b,Z b

@[expose] def output (Q : ℝ) (Z : Fin K→State N) : State N :=
  clip (Real.sqrt N) ((Real.sqrt Q)⁻¹ • average Z)

@[expose] def normalizedRate (L : ℝ≥0) (Q : ℝ) : ℝ≥0 :=
  ⟨(Real.sqrt Q)⁻¹*(L:ℝ),by positivity⟩

theorem average_sub_norm_le (Z W : Fin K→State N) :
    ‖average Z-average W‖≤(K:ℝ)⁻¹*∑b,‖Z b-W b‖ := by
  have he : average Z-average W=(K:ℝ)⁻¹ • ∑b,(Z b-W b) := by
    simp only [average,←smul_sub,←Finset.sum_sub_distrib]
  rw [he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (Nat.cast_nonneg K)]
  exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)

theorem average_sub_norm_sq_le (hK : 0<K) (Z W : Fin K→State N) :
    ‖average Z-average W‖^2≤(K:ℝ)⁻¹*∑b,‖Z b-W b‖^2 := by
  have hKn : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hs := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun b : Fin K => ‖Z b-W b‖)
  simp only [Finset.card_univ,Fintype.card_fin] at hs
  have hn := average_sub_norm_le Z W
  have hh : ‖average Z-average W‖^2≤((K:ℝ)⁻¹*∑b,‖Z b-W b‖)^2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg ((K:ℝ)⁻¹))
  rw [mul_pow] at hh
  have he : (K:ℝ)⁻¹^2*((K:ℝ)*∑b,‖Z b-W b‖^2)=(K:ℝ)⁻¹*∑b,‖Z b-W b‖^2 := by
    field_simp
  exact hh.trans (hm.trans_eq he)

theorem output_norm_le (Q : ℝ) (Z : Fin K→State N) : ‖output Q Z‖≤Real.sqrt N :=
  clip_norm_le (Real.sqrt_nonneg _) _

theorem output_sub_norm_sq_le (hK : 0<K) {Q : ℝ} (hQ : 0<Q) (Z W : Fin K→State N) :
    ‖output Q Z-output Q W‖^2≤Q⁻¹*(K:ℝ)⁻¹*∑b,‖Z b-W b‖^2 := by
  have hh := (SphereBallMetricProjection.project_lipschitz (SphereBallMetricProjection.sphereRadius N)).dist_le_mul
    ((Real.sqrt Q)⁻¹ • average Z) ((Real.sqrt Q)⁻¹ • average W)
  have hn : ‖output Q Z-output Q W‖≤(Real.sqrt Q)⁻¹*‖average Z-average W‖ := by
    simpa only [output,clip_sphereRadius_eq,dist_eq_norm,NNReal.coe_one,one_mul,←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg Q)] using hh
  have hsq := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  rw [mul_pow,inv_pow,Real.sq_sqrt hQ.le] at hsq
  exact hsq.trans (by
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_left (average_sub_norm_sq_le hK Z W) (inv_nonneg.mpr hQ.le))

theorem output_measurable {Q : ℝ} (Z : Fin K→Ω→State N) (hZ : ∀b,Measurable (Z b)) :
    Measurable (fun omega => output Q (fun b => Z b omega)) := by
  have ha : Measurable (fun omega => average (fun b => Z b omega)) := by
    unfold average
    have hh := (Finset.measurable_sum Finset.univ (fun b _ => hZ b)).const_smul ((K:ℝ)⁻¹)
    change Measurable (fun omega => (K:ℝ)⁻¹ • ∑b,Z b omega) at hh
    exact hh
  have hs : Measurable (fun omega => (Real.sqrt Q)⁻¹ • average (fun b => Z b omega)) :=
    by
      have hh := ha.const_smul ((Real.sqrt Q)⁻¹)
      change Measurable (fun omega => (Real.sqrt Q)⁻¹ • average (fun b => Z b omega)) at hh
      exact hh
  have hh := (SphereBallMetricProjection.project_continuous (SphereBallMetricProjection.sphereRadius N)).measurable.comp hs
  simpa only [output,clip_sphereRadius_eq,Function.comp_def] using hh

theorem output_lipschitz {E : Type*} [PseudoMetricSpace E] (hK : 0<K) (L : ℝ≥0) (Q : ℝ)
    (Z : Fin K→E→State N) (hZ : ∀b,LipschitzWith L (Z b)) :
    LipschitzWith (normalizedRate L Q) (fun x => output Q (fun b => Z b x)) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have hKpos : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have ha : ‖average (fun b => Z b x)-average (fun b => Z b y)‖≤(L:ℝ)*dist x y := by
    calc
      _≤(K:ℝ)⁻¹*∑b,‖Z b x-Z b y‖ := average_sub_norm_le _ _
      _≤(K:ℝ)⁻¹*∑_b : Fin K,(L:ℝ)*dist x y :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun b _ => by
          simpa only [dist_eq_norm] using (hZ b).dist_le_mul x y) (by positivity)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp
  have hh := (SphereBallMetricProjection.project_lipschitz (SphereBallMetricProjection.sphereRadius N)).dist_le_mul
    ((Real.sqrt Q)⁻¹ • average (fun b => Z b x)) ((Real.sqrt Q)⁻¹ • average (fun b => Z b y))
  have hn : dist (output Q (fun b => Z b x)) (output Q (fun b => Z b y))≤
      (Real.sqrt Q)⁻¹*‖average (fun b => Z b x)-average (fun b => Z b y)‖ := by
    simpa only [output,clip_sphereRadius_eq,dist_eq_norm,NNReal.coe_one,one_mul,←smul_sub,norm_smul,
      Real.norm_eq_abs,abs_inv,abs_of_nonneg (Real.sqrt_nonneg Q)] using hh
  exact hn.trans (by
    change (Real.sqrt Q)⁻¹*‖average (fun b => Z b x)-average (fun b => Z b y)‖≤
      ((Real.sqrt Q)⁻¹*(L:ℝ))*dist x y
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr (Real.sqrt_nonneg Q)))


theorem output_memLp {Q : ℝ} (Z : Fin K→Ω→State N) (hZ : ∀b,MemLp (Z b) 2 μ) :
    MemLp (fun omega => output Q (fun b => Z b omega)) 2 μ := by
  have hAvg : MemLp (fun omega => average (fun b => Z b omega)) 2 μ := by
    have hh := (memLp_finsetSum Finset.univ (fun b _ => hZ b)).const_smul ((K:ℝ)⁻¹)
    change MemLp (fun omega => (K:ℝ)⁻¹ • ∑b,Z b omega) 2 μ at hh
    exact hh
  have hScaled : MemLp (fun omega => (Real.sqrt Q)⁻¹ • average (fun b => Z b omega)) 2 μ := by
    have hh := hAvg.const_smul ((Real.sqrt Q)⁻¹)
    change MemLp (fun omega => (Real.sqrt Q)⁻¹ • average (fun b => Z b omega)) 2 μ at hh
    exact hh
  have hsm : AEStronglyMeasurable (fun omega => output Q (fun b => Z b omega)) μ := by
    have hh := (SphereBallMetricProjection.project_continuous (SphereBallMetricProjection.sphereRadius N)).comp_aestronglyMeasurable hScaled.aestronglyMeasurable
    simpa only [output,clip_sphereRadius_eq,Function.comp_def] using hh
  exact MemLp.of_bound hsm (Real.sqrt N) (.of_forall (fun omega => output_norm_le Q _))

/-- Genuine mean-square error of the finite average after normalization
and projection. Independence of the branches is unnecessary. -/
theorem output_integral_sq_le (hK : 0<K) {Q : ℝ} (hQ : 0<Q)
    (Z W : Fin K→Ω→State N) (hZ : ∀b,MemLp (Z b) 2 μ) (hW : ∀b,MemLp (W b) 2 μ) :
    (∫omega,‖output Q (fun b => Z b omega)-output Q (fun b => W b omega)‖^2 ∂μ)≤
      Q⁻¹*(K:ℝ)⁻¹*∑b,(∫omega,‖Z b omega-W b omega‖^2 ∂μ) := by
  have hd b : MemLp (fun omega => Z b omega-W b omega) 2 μ := (hZ b).sub (hW b)
  have hi b : Integrable (fun omega => ‖Z b omega-W b omega‖^2) μ := (hd b).integrable_norm_pow'
  have hOut : MemLp (fun omega => output Q (fun b => Z b omega)-output Q (fun b => W b omega)) 2 μ :=
    (output_memLp Z hZ).sub (output_memLp W hW)
  calc
    _≤∫omega,Q⁻¹*(K:ℝ)⁻¹*∑b,‖Z b omega-W b omega‖^2 ∂μ := by
      apply integral_mono hOut.integrable_norm_pow'
        ((integrable_finsetSum Finset.univ (fun b _ => hi b)).const_mul _)
      exact fun omega => output_sub_norm_sq_le hK hQ _ _
    _=_ := by
      rw [integral_const_mul,integral_finset_sum Finset.univ (fun b _ => hi b)]

/-- A uniform normalized branch error B becomes B/Q for the literal
projected normalized mean. -/
theorem output_normalized_error_le (hN : 0<N) (hK : 0<K) {Q : ℝ} (hQ : 0<Q)
    (Z W : Fin K→Ω→State N) (hZ : ∀b,MemLp (Z b) 2 μ) (hW : ∀b,MemLp (W b) 2 μ)
    (B : ℝ) (hError : ∀b,(∫omega,‖Z b omega-W b omega‖^2 ∂μ)/(N:ℝ)≤B) :
    (∫omega,‖output Q (fun b => Z b omega)-output Q (fun b => W b omega)‖^2 ∂μ)/(N:ℝ)≤Q⁻¹*B := by
  have hKn : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hBound := div_le_div_of_nonneg_right (output_integral_sq_le hK hQ Z W hZ hW) (Nat.cast_nonneg N)
  rw [mul_div_assoc,Finset.sum_div] at hBound
  have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun b _ => hError b)
  have hm := mul_le_mul_of_nonneg_left hSum
    (mul_nonneg (inv_nonneg.mpr hQ.le) (inv_nonneg.mpr hKn.le))
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hm
  have he : Q⁻¹*(K:ℝ)⁻¹*((K:ℝ)*B)=Q⁻¹*B := by field_simp
  exact hBound.trans (hm.trans_eq he)

end SphericalAging.FiniteFamilyBallApproximation
