module

public import SphericalAging.ActualCKMeanSupremumConvergence
public import SphericalAging.CKNonnegativeKernelContinuity
public import SphericalAging.ContinuousSupremumMeasurability
public import SphericalAging.ActualBrownianPrimitiveTimeModulus

public section

/-! The literal compact suprema appearing in source 3.3 are almost surely
measurable, by genuine continuous model paths and countable dense sets. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualCKPathSupremumMeasurability
open CompactKernelMemoryLimit ActualModelOverlapVariance ActualStateIncrementMoments
  ActualBrownianPrimitiveTimeModulus BrownianVectorMoments HardSphereDynamics
  CKNonnegativeKernelContinuity ContinuousSupremumMeasurability UniformSupremumError
set_option maxHeartbeats 650000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose]  def correlationCKSup (N p : ℕ) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  supError (fun z : ℝ≥0×ℝ≥0 => actualOverlap β R hR z.1 z.2 ω)
    (fun z => d.C z.1 z.2) (square T)

@[expose]  def gammaCKSup (N p : ℕ) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  supError (fun z : ℝ≥0×ℝ≥0 => actualGamma β R hR z.1 z.2 ω)
    (fun z => ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2) (square T)

 theorem actual_overlap_paths_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,Continuous (fun z : ℝ≥0×ℝ≥0 => actualOverlap β R hR z.1 z.2 ω) := by
  filter_upwards [AnnealedGlobalSDE.globalProcess_continuous
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
      (AnnealedModelLaw.parameter_disorder_memLp N p)] with ω hω
  exact ((hω.comp continuous_fst).inner (hω.comp continuous_snd)).div_const (N : ℝ)

 theorem actual_brownian_path_continuous (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    Continuous (fun s => actualBrownian (N := N) (p := p) s ω) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin N => ℝ)).comp (continuous_pi (fun j => (ω.2 j).continuous))

 theorem actual_gamma_paths_continuous (β R : ℝ≥0) (hR : 0<(R : ℝ)) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,Continuous (fun z : ℝ≥0×ℝ≥0 => actualGamma β R hR z.1 z.2 ω) := by
  filter_upwards [AnnealedGlobalSDE.globalProcess_continuous
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
      (AnnealedModelLaw.parameter_disorder_memLp N p)] with ω hω
  exact ((hω.comp continuous_fst).inner ((actual_brownian_path_continuous ω).comp continuous_snd)).div_const
    (Real.sqrt 2*(N : ℝ))

 theorem correlationCKSup_aestronglyMeasurable (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    AEStronglyMeasurable (correlationCKSup N p β R hR d T) (AnnealedModelLaw.law N p) := by
  apply aestronglyMeasurable_sSup_image_of_ae_continuousOn
  · intro z _
    exact ((ActualOverlapTimeModulus.actualOverlap_memLp_two (p := p) hN β R hR hNR z.1 z.2).aemeasurable.sub
      aemeasurable_const).norm
  · filter_upwards [actual_overlap_paths_continuous (N := N) (p := p) β R hR] with ω hω
    exact (hω.sub (correlation_continuous_nonnegative hd)).norm.continuousOn

 theorem gammaCKSup_aestronglyMeasurable (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    AEStronglyMeasurable (gammaCKSup N p β R hR d T) (AnnealedModelLaw.law N p) := by
  apply aestronglyMeasurable_sSup_image_of_ae_continuousOn
  · intro z _
    exact ((actualGamma_memLp_two (p := p) hN β R hR hNR z.1 z.2).aemeasurable.sub aemeasurable_const).norm
  · filter_upwards [actual_gamma_paths_continuous (N := N) (p := p) β R hR] with ω hω
    exact (hω.sub (responsePrimitive_continuous_nonnegative hd)).norm.continuousOn

end SphericalAging.ActualCKPathSupremumMeasurability
