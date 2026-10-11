module

public import SphericalAging.AlgorithmicCorrelationContinuity
public import Mathlib.MeasureTheory.Function.L2Space

public section

/-! Both endpoint values of the literal Gaussian algorithm correlation
function, derived under the original ordered disorder law. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AlgorithmicCorrelationEndpoints
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
  AlgorithmicOverlapLipschitz AlgorithmicOverlapConcentration AlgorithmicCorrelationContinuity
open scoped InnerProductSpace NNReal
variable {N p : ℕ}

@[expose] def output (A : TensorSpace N p→Vector N) (J : Disorder N p) : Vector N := A (WithLp.toLp 2 J)
@[expose] def mean (A : TensorSpace N p→Vector N) : Vector N := ∫J,output A J ∂disorderLaw N p

theorem output_continuous (A : TensorSpace N p→Vector N) (hA : Continuous A) :
    Continuous (output A) :=
  hA.comp (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ))

theorem output_integrable (A : TensorSpace N p→Vector N) (hA : Continuous A)
    (hball : ∀J,‖A J‖≤Real.sqrt N) : Integrable (output A) (disorderLaw N p) :=
  (integrable_const (Real.sqrt (N:ℝ))).mono' (output_continuous A hA).aestronglyMeasurable
    (ae_of_all _ (fun J => hball _))

theorem correlation_zero (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) :
    correlation A 0=‖mean A‖^2/(N:ℝ) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hf := output_integrable A hA hball
  have hC : Continuous (fun z : Disorder N p×Disorder N p => ⟪output A z.1,output A z.2⟫_ℝ) :=
    ((output_continuous A hA).comp continuous_fst).inner ((output_continuous A hA).comp continuous_snd)
  have hI : Integrable (fun z : Disorder N p×Disorder N p => ⟪output A z.1,output A z.2⟫_ℝ)
      ((disorderLaw N p).prod (disorderLaw N p)) := by
    apply (integrable_const (N:ℝ)).mono' hC.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs]
      calc
        _≤‖output A z.1‖*‖output A z.2‖ := abs_real_inner_le_norm _ _
        _≤Real.sqrt N*Real.sqrt N := mul_le_mul (hball _) (hball _) (norm_nonneg _) (Real.sqrt_nonneg _)
        _=N := Real.mul_self_sqrt hNr.le)
  have hpair := (measurePreserving_piFinTwo (fun _ : Fin 2 => disorderLaw N p)).hasLaw.integral_comp
    (hI.div_const (N:ℝ)).aestronglyMeasurable
  change (∫J,⟪output A (J 0),output A (J 1)⟫_ℝ/(N:ℝ) ∂pairLaw N p)=
      (∫z : Disorder N p×Disorder N p,⟪output A z.1,output A z.2⟫_ℝ/(N:ℝ)
        ∂(disorderLaw N p).prod (disorderLaw N p)) at hpair
  have hzero : correlation A 0=∫J,⟪output A (J 0),output A (J 1)⟫_ℝ/(N:ℝ) ∂pairLaw N p := by
    unfold correlation rawOverlap overlap correlatedInput tensorInputs output
    simp only [zero_smul,zero_pow (by norm_num : 2≠0),sub_zero,Real.sqrt_one,one_smul,zero_add]
  rw [hzero,hpair,integral_div,integral_prod _ hI]
  simp_rw [integral_inner hf]
  have hi : (∫J,⟪output A J,mean A⟫_ℝ ∂disorderLaw N p)=‖mean A‖^2 := by
    calc
      _=(∫J,⟪mean A,output A J⟫_ℝ ∂disorderLaw N p) :=
        integral_congr_ae (ae_of_all _ (fun J => real_inner_comm _ _))
      _=⟪mean A,mean A⟫_ℝ := integral_inner hf (mean A)
      _=_ := real_inner_self_eq_norm_sq _
  exact congrArg (fun z : ℝ => z/(N:ℝ)) hi

theorem correlation_one_original (A : TensorSpace N p→Vector N) (hA : Continuous A)
    (hball : ∀J,‖A J‖≤Real.sqrt N) :
    correlation A 1=∫J,‖output A J‖^2/(N:ℝ) ∂disorderLaw N p := by
  have hC : Continuous (fun J : Disorder N p => ‖output A J‖^2/(N:ℝ)) :=
    (output_continuous A hA).norm.pow 2 |>.div_const _
  have hh := (measurePreserving_eval (fun _ : Fin 2 => disorderLaw N p) (0:Fin 2)).hasLaw.integral_comp
    hC.aestronglyMeasurable
  rw [correlation_one]
  exact hh

end SphericalAging.AlgorithmicCorrelationEndpoints
