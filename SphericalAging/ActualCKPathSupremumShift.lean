module

public import SphericalAging.ActualCKPathSupremumMeasurability
public import SphericalAging.ActualOverlapCompactSup
public import SphericalAging.SupremumMeanShift

public section

/-! Literal actual path suprema split into genuine centered random errors
and deterministic CK mean errors. All finite supremum bounds come from
actual continuous paths on compact squares. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualCKPathSupremumShift
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCKPathSupremumMeasurability
  ActualCKMeanSupremumConvergence ActualCKMeanConvergenceOfEquicontinuity
  ActualCanonicalMeanKernelExtraction ActualMeanKernelTimeCompactness
  ActualOverlapCompactPathConcentration ActualModelOverlapVariance
  ActualBrownianPrimitiveTimeModulus CKNonnegativeKernelContinuity SupremumMeanShift
  UniformSupremumError AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose]  def gammaCenteredModelSup (N p : ℕ) (β T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  supError (fun z : ℝ≥0×ℝ≥0 => actualGamma β (N+1) (modelRadius_pos N) z.1 z.2 ω)
    (Function.uncurry (modelGamma N p β)) (square T)

 theorem modelCorrelation_continuous (hN : 1≤N) (hp : 0<p) (β : ℝ≥0) :
    Continuous (Function.uncurry (modelCorrelation N p β)) := by
  have hh := overlapMean_continuous hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N)
  exact hh.congr (fun z => overlapMean_eq_correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) z)

 theorem modelGamma_continuous (hN : 1≤N) (hp : 0<p) (β : ℝ≥0) :
    Continuous (Function.uncurry (modelGamma N p β)) := by
  have hh := (actual_gamma_means_equicontinuous (fun _ : Unit => N) (fun _ => hN) p hp β
    (fun _ => N+1) (fun _ => modelRadius_pos N) (fun _ => modelRadius_sq N)).continuous ()
  exact hh.congr (fun z => gammaMean_eq_annealedGammaPair (N := N) (p := p) β (N+1) (modelRadius_pos N) z)

 theorem overlapCenteredSup_eq_modelSup (β : ℝ≥0) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    overlapCenteredSup N p β (N+1) (modelRadius_pos N) T ω=
      supError (fun z : ℝ≥0×ℝ≥0 => actualOverlap β (N+1) (modelRadius_pos N) z.1 z.2 ω)
        (Function.uncurry (modelCorrelation N p β)) (square T) := by
  unfold overlapCenteredSup DyadicSquareSupremum.squareSup supError
  congr 1
  congr 1
  funext z
  have he := overlapMean_eq_correlationPair (N := N) (p := p) β (N+1) (modelRadius_pos N) z
  simpa only [overlapMean,modelCorrelation,Function.uncurry] using
    congrArg (fun r => |actualOverlap β (N+1) (modelRadius_pos N) z.1 z.2 ω-r|) he

 theorem correlationCKSup_sq_shift (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,
      (correlationCKSup N p β (N+1) (modelRadius_pos N) d T ω)^2≤
        2*(overlapCenteredSup N p β (N+1) (modelRadius_pos N) T ω)^2+
        2*(correlationMeanSupError N p β d T)^2 := by
  have hM := modelCorrelation_continuous hN hp β
  have hf := correlation_continuous_nonnegative hd
  have hMf : BddAbove ((fun z : ℝ≥0×ℝ≥0 => |modelCorrelation N p β z.1 z.2-d.C z.1 z.2|) '' square T) :=
    ((square_isCompact T).image (hM.sub hf).abs).bddAbove
  filter_upwards [actual_overlap_paths_continuous (N := N) (p := p) β (N+1) (modelRadius_pos N)] with ω hω
  have hFM : BddAbove ((fun z : ℝ≥0×ℝ≥0 => |actualOverlap β (N+1) (modelRadius_pos N) z.1 z.2 ω-
      modelCorrelation N p β z.1 z.2|) '' square T) :=
    ((square_isCompact T).image (hω.sub hM).abs).bddAbove
  rw [overlapCenteredSup_eq_modelSup]
  exact supError_sq_le (square_nonempty T) hFM hMf

 theorem gammaCKSup_shift (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,
      gammaCKSup N p β (N+1) (modelRadius_pos N) d T ω≤
        gammaCenteredModelSup N p β T ω+gammaMeanSupError N p β d T := by
  have hM := modelGamma_continuous hN hp β
  have hf := responsePrimitive_continuous_nonnegative hd
  have hMf : BddAbove ((fun z : ℝ≥0×ℝ≥0 => |modelGamma N p β z.1 z.2-
      ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|) '' square T) :=
    ((square_isCompact T).image (hM.sub hf).abs).bddAbove
  filter_upwards [actual_gamma_paths_continuous (N := N) (p := p) β (N+1) (modelRadius_pos N)] with ω hω
  have hFM : BddAbove ((fun z : ℝ≥0×ℝ≥0 => |actualGamma β (N+1) (modelRadius_pos N) z.1 z.2 ω-
      modelGamma N p β z.1 z.2|) '' square T) :=
    ((square_isCompact T).image (hω.sub hM).abs).bddAbove
  exact supError_triangle (square_nonempty T) hFM hMf

end SphericalAging.ActualCKPathSupremumShift
