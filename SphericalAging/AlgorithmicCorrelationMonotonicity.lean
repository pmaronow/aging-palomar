module

public import SphericalAging.GaussianVectorNoiseCorrelation
public import SphericalAging.AlgorithmicCorrelationEndpoints

public section

/-! Genuine Huang--Sellke Proposition 2.1 for the actual ordered Gaussian
ball algorithm. Positivity and monotonicity are derived from the Gaussian
noise semigroup; continuity and endpoint values use the original law. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AlgorithmicCorrelationMonotonicity
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure OrthogonalGaussianDisclosure
  AlgorithmicOverlapLipschitz AlgorithmicOverlapConcentration AlgorithmicCorrelationContinuity
  AlgorithmicCorrelationEndpoints GaussianNoiseSymmetry
open scoped InnerProductSpace NNReal
variable {N p : ℕ}

@[expose] def inputPair (J : Fin 2→Disorder N p) : TensorSpace N p×TensorSpace N p :=
  (WithLp.toLp 2 (J 0),WithLp.toLp 2 (J 1))

theorem inputPair_measurePreserving : MeasurePreserving (inputPair (N:=N) (p:=p))
    (pairLaw N p) ((stdGaussian (TensorSpace N p)).prod (stdGaussian (TensorSpace N p))) := by
  have ht : MeasurePreserving (WithLp.toLp 2 : Disorder N p→TensorSpace N p)
      (disorderLaw N p) (stdGaussian (TensorSpace N p)) :=
    ⟨(PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable,
      (ordered_tensor_hasLaw N p).map_eq⟩
  have hh := (ht.prod ht).comp (measurePreserving_piFinTwo (fun _ : Fin 2 => disorderLaw N p))
  exact hh

theorem correlation_eq_vectorStability (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) (ρ : ℝ) :
    correlation A ρ=GaussianVectorNoiseCorrelation.stability ρ A/(N:ℝ) := by
  have hn : Continuous (fun z : TensorSpace N p×TensorSpace N p => noise ρ z.1 z.2) :=
    (GaussianLinearMixtureLaw.mixture (E:=TensorSpace N p) ρ (Real.sqrt (1-ρ^2))).continuous
  have hc : Continuous (fun z : TensorSpace N p×TensorSpace N p =>
      ⟪A z.1,A (noise ρ z.1 z.2)⟫_ℝ/(N:ℝ)) :=
    ((hA.comp continuous_fst).inner (hA.comp hn)).div_const _
  have hh := inputPair_measurePreserving.hasLaw.integral_comp hc.aestronglyMeasurable
  change (∫J,rawOverlap ρ A J ∂pairLaw N p)=_
  have he : (fun J : Fin 2→Disorder N p =>
      ⟪A (inputPair J).1,A (noise ρ (inputPair J).1 (inputPair J).2)⟫_ℝ/(N:ℝ))=
      rawOverlap ρ A := by funext J;rfl
  change (∫J,⟪A (inputPair J).1,A (noise ρ (inputPair J).1 (inputPair J).2)⟫_ℝ/(N:ℝ)
    ∂pairLaw N p)=_ at hh
  rw [he] at hh
  rw [hh,integral_div]
  rfl

theorem correlation_nonneg (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1) :
    0≤correlation A ρ := by
  rw [correlation_eq_vectorStability hN A hA hball ρ]
  exact div_nonneg (GaussianVectorNoiseCorrelation.stability_nonneg ρ h0 h1 A hA.measurable
    (Real.sqrt N) hball) (Nat.cast_nonneg N)

theorem correlation_monotone (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) :
    MonotoneOn (correlation A) (Set.Icc 0 1) := by
  intro ρ hρ σ hσ hρσ
  rw [correlation_eq_vectorStability hN A hA hball ρ,correlation_eq_vectorStability hN A hA hball σ]
  exact div_le_div_of_nonneg_right (GaussianVectorNoiseCorrelation.stability_monotone A hA.measurable
    (Real.sqrt N) hball hρ hσ hρσ) (Nat.cast_nonneg N)

/-- All asserted correlation regularity and endpoints are derived from the
literal independent original-disorder model and actual ball algorithm. -/
theorem actual_source_HS_2_1 (hN : 0<N) (A : TensorSpace N p→Vector N)
    (hA : Continuous A) (hball : ∀J,‖A J‖≤Real.sqrt N) :
    Continuous (correlation A) ∧ MonotoneOn (correlation A) (Set.Icc 0 1) ∧
    (∀ρ∈Set.Icc (0:ℝ) 1,correlation A ρ∈Set.Icc (0:ℝ) 1) ∧
    correlation A 0=‖mean A‖^2/(N:ℝ) ∧
    correlation A 1=∫J,‖output A J‖^2/(N:ℝ) ∂disorderLaw N p := by
  refine ⟨correlation_continuous hN A hA hball,correlation_monotone hN A hA hball,?_,
    correlation_zero hN A hA hball,correlation_one_original A hA hball⟩
  intro ρ hρ
  exact ⟨correlation_nonneg hN A hA hball ρ hρ.1 hρ.2,
    (le_abs_self _).trans (correlation_abs_bound hN A hA hball ρ)⟩

end SphericalAging.AlgorithmicCorrelationMonotonicity
