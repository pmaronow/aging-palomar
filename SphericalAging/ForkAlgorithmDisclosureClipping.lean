module

public import SphericalAging.AdaptiveTensorDisclosureWaitingPairing
public import SphericalAging.SphereEulerCoefficients
public import SphericalAging.ForkNormalizedEnergy

public section

/-! A seed-almost-everywhere admissible algorithm has a globally ball-valued
tensor representative with the same actual energy and pairing integrals.
This supplies the literal model interface from source10.7 to the finite-fork waiting-state argument. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ForkAlgorithmDisclosureClipping
open MeasureTheory ProbabilityTheory Filter FiniteModel AdaptiveGradientDisclosure
open AdaptiveSourceProjectionMoments AdaptiveResidualEnergyLimit
open AlgorithmEnergyDeficit ExternalFieldElementaryPenalty
open scoped NNReal Topology InnerProductSpace
variable {N p : ℕ} {S : Type} [MeasurableSpace S]

@[expose] def clippedTensorAlgorithm (A : S×Disorder N p→Vector N) : S→TensorSpace N p→Vector N :=
  fun s J => SphereEulerCoefficients.clip (A (s,J.ofLp))

theorem measurable_uncurry {A : S×Disorder N p→Vector N} (hA : Measurable A) :
    Measurable (Function.uncurry (clippedTensorAlgorithm A)) := by
  exact SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp
    (hA.comp (measurable_fst.prodMk
      ((PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_snd)))

theorem lipschitz_seed {A : S×Disorder N p→Vector N} {Lip : ℝ≥0}
    {μ : Measure S} (hLip : ∀ᵐs ∂μ,
      LipschitzWith Lip (fun J : TensorSpace N p => A (s,J.ofLp))) :
    ∀ᵐs ∂μ,LipschitzWith Lip (clippedTensorAlgorithm A s) := by
  filter_upwards [hLip] with s hs
  change LipschitzWith Lip (fun J : TensorSpace N p => SphereEulerCoefficients.clip (A (s,J.ofLp)))
  simpa only [one_mul,Function.comp_def] using SphereEulerCoefficients.clip_lipschitz.comp hs

theorem global_ball (A : S×Disorder N p→Vector N) (s : S) (J : TensorSpace N p) :
    ‖clippedTensorAlgorithm A s J‖≤Real.sqrt N := SphereEulerCoefficients.clip_norm_le _

theorem algorithm_ae_eq (μ : Measure S) [IsProbabilityMeasure μ]
    {A : S×Disorder N p→Vector N}
    (hball : ∀ᵐs ∂μ,∀J,‖A (s,J)‖≤Real.sqrt N) :
    algorithm (clippedTensorAlgorithm A)=ᵐ[μ.prod (disorderLaw N p)] A := by
  filter_upwards [(measurePreserving_fst (μ:=μ) (ν:=disorderLaw N p)).quasiMeasurePreserving.ae hball]
    with z hz
  simp only [algorithm,clippedTensorAlgorithm,WithLp.ofLp_toLp]
  exact if_pos (hz z.2)

theorem expected_energy_eq (μ : Measure S) [IsProbabilityMeasure μ]
    {A : S×Disorder N p→Vector N}
    (hball : ∀ᵐs ∂μ,∀J,‖A (s,J)‖≤Real.sqrt N) :
    meanEnergy μ (algorithm (clippedTensorAlgorithm A))=
      ForkNormalizedEnergy.expectedEnergy (μ:=μ.prod (disorderLaw N p)) Prod.snd A := by
  unfold meanEnergy ForkNormalizedEnergy.expectedEnergy
  congr 1
  exact integral_congr_ae ((algorithm_ae_eq μ hball).mono (fun z hz => by dsimp only;rw [hz]))

theorem pairing_integral_eq (μ : Measure S) [IsProbabilityMeasure μ]
    {A : S×Disorder N p→Vector N}
    (hball : ∀ᵐs ∂μ,∀J,‖A (s,J)‖≤Real.sqrt N) (Y : S×Disorder N p→Vector N) :
    (∫z,|⟪algorithm (clippedTensorAlgorithm A) z,Y z⟫_ℝ/(N:ℝ)|^2
      ∂μ.prod (disorderLaw N p))=
    ∫z,|⟪A z,Y z⟫_ℝ/(N:ℝ)|^2 ∂μ.prod (disorderLaw N p) :=
  integral_congr_ae ((algorithm_ae_eq μ hball).mono (fun z hz => by dsimp only;rw [hz]))

/-- The native deficit agrees exactly with the source10.7 tensor deficit,
including varying seed spaces and dimensions. -/
theorem energyDeficit_eq {dim : ℕ→ℕ} {Seeds : ℕ→Type}
    [∀n,MeasurableSpace (Seeds n)] (μ : ∀n,Measure (Seeds n))
    [∀n,IsProbabilityMeasure (μ n)]
    (A : ∀n,Seeds n×Disorder (dim n) p→Vector (dim n))
    (hball : ∀n,∀ᵐs ∂μ n,∀J,‖A n (s,J)‖≤Real.sqrt (dim n)) :
    AdaptiveSourceProjectionRecursion.energyDeficit μ
      (fun n => clippedTensorAlgorithm (A n))=
    deficit (thresholdEnergy p) (fun n =>
      ForkNormalizedEnergy.expectedEnergy (μ:=(μ n).prod (disorderLaw (dim n) p)) Prod.snd (A n)) := by
  unfold AdaptiveSourceProjectionRecursion.energyDeficit
  congr 1
  funext n
  exact expected_energy_eq (μ n) (hball n)

end SphericalAging.ForkAlgorithmDisclosureClipping
