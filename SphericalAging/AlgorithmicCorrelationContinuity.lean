module

public import SphericalAging.AlgorithmicOverlapConcentration

public section

/-! The actual Gaussian algorithm correlation function is continuous,
with its endpoint at correlation one computed from the original disorder.
No correlation-function regularity is supplied as an assumption. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AlgorithmicCorrelationContinuity
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
  AlgorithmicOverlapLipschitz AlgorithmicOverlapConcentration
open scoped InnerProductSpace NNReal
variable {N p : ℕ}

@[expose] def correlation (A : TensorSpace N p→Vector N) (ρ : ℝ) : ℝ :=
  ∫J,rawOverlap ρ A J ∂pairLaw N p

theorem tensorInputs_continuous : Continuous (tensorInputs (N:=N) (p:=p)) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin 2 => TensorSpace N p)).comp
    (continuous_pi (fun i =>
      (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).comp (continuous_apply i)))

theorem rawOverlap_joint_continuous (A : TensorSpace N p→Vector N) (hA : Continuous A) :
    Continuous (fun z : ℝ×(Fin 2→Disorder N p) => rawOverlap z.1 A z.2) := by
  unfold rawOverlap overlap correlatedInput
  have hI : Continuous (fun z : ℝ×(Fin 2→Disorder N p) => tensorInputs z.2) :=
    (tensorInputs_continuous (N:=N) (p:=p)).comp continuous_snd
  have h0 : Continuous (fun z : ℝ×(Fin 2→Disorder N p) => tensorInputs z.2 0) :=
    (coordinate_lipschitz N p 0).continuous.comp hI
  have h1 : Continuous (fun z : ℝ×(Fin 2→Disorder N p) => tensorInputs z.2 1) :=
    (coordinate_lipschitz N p 1).continuous.comp hI
  exact ((hA.comp h0).inner (hA.comp
    ((continuous_fst.smul h0).add
      ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_fst.pow 2))).smul h1)))).div_const _

theorem rawOverlap_abs_bound (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hball : ∀J,‖A J‖≤Real.sqrt N) (ρ : ℝ) (J : Fin 2→Disorder N p) :
    |rawOverlap ρ A J|≤1 := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  unfold rawOverlap overlap
  rw [abs_div,abs_of_pos hNr]
  apply (div_le_one hNr).mpr
  calc
    _≤‖A (tensorInputs J 0)‖*‖A (correlatedInput ρ (tensorInputs J))‖ := abs_real_inner_le_norm _ _
    _≤Real.sqrt N*Real.sqrt N := mul_le_mul (hball _) (hball _) (norm_nonneg _) (Real.sqrt_nonneg _)
    _=N := Real.mul_self_sqrt hNr.le

theorem correlation_continuous (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) : Continuous (correlation A) := by
  have hC := rawOverlap_joint_continuous A hA
  apply continuous_of_dominated (bound:=fun _ => (1:ℝ))
  · intro ρ
    exact (hC.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · intro ρ
    exact ae_of_all _ (fun J => by
      rw [Real.norm_eq_abs]
      exact rawOverlap_abs_bound hN A hball ρ J)
  · exact integrable_const _
  · exact ae_of_all _ (fun J => hC.comp (continuous_id.prodMk continuous_const))

theorem correlation_abs_bound (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) (ρ : ℝ) :
    |correlation A ρ|≤1 := by
  have hmap : Continuous (fun J : Fin 2→Disorder N p => (ρ,J)) := continuous_const.prodMk continuous_id
  have hc : Continuous (fun J : Fin 2→Disorder N p => rawOverlap ρ A J) :=
    (rawOverlap_joint_continuous A hA).comp hmap
  have hm : Measurable (rawOverlap ρ A) := hc.measurable
  have hi : Integrable (rawOverlap ρ A) (pairLaw N p) :=
    (integrable_const (1:ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun J => by rw [Real.norm_eq_abs];exact rawOverlap_abs_bound hN A hball ρ J))
  unfold correlation
  calc
    _≤∫J,|rawOverlap ρ A J| ∂pairLaw N p := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (rawOverlap ρ A)
    _≤∫_J,1 ∂pairLaw N p := integral_mono hi.norm (integrable_const _)
      (rawOverlap_abs_bound hN A hball ρ)
    _=1 := by simp

theorem correlation_one (A : TensorSpace N p→Vector N) :
    correlation A 1=∫J,‖A (tensorInputs J 0)‖^2/(N:ℝ) ∂pairLaw N p := by
  unfold correlation rawOverlap overlap correlatedInput
  simp only [one_smul,one_pow,sub_self,Real.sqrt_zero,zero_smul,add_zero,
    real_inner_self_eq_norm_sq]

end SphericalAging.AlgorithmicCorrelationContinuity
