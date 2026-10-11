module

public import SphericalAging.ActualCKPathSupremumShift
public import SphericalAging.ActualOverlapCompactPathConcentration
public import SphericalAging.ActualGammaCompactPathConcentration

public section

/-! Genuine compact-time convergence of the actual random C and Γ kernels
to the unique CK solution. The C supremum converges in second mean and the
Γ supremum in first mean, as required by the manuscript's source 3.3. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualCKCompactPathConvergence
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCKPathSupremumMeasurability
  ActualCKMeanSupremumConvergence ActualCKMeanConvergenceOfEquicontinuity
  ActualCKPathSupremumShift ActualOverlapCompactPathConcentration
  ActualGammaCompactPathConcentration ActualModelOverlapVariance
  ActualBrownianPrimitiveTimeModulus CKNonnegativeKernelContinuity SupremumMeanShift
  UniformSupremumError AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem correlationCKSup_nonneg (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,0≤correlationCKSup N p β R hR d T ω := by
  filter_upwards [actual_overlap_paths_continuous (N:=N) (p:=p) β R hR] with ω hω
  exact supError_nonneg (square_nonempty T)
    (((square_isCompact T).image (hω.sub (correlation_continuous_nonnegative hd)).abs).bddAbove)

 theorem gammaCKSup_nonneg (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,0≤gammaCKSup N p β R hR d T ω := by
  filter_upwards [actual_gamma_paths_continuous (N:=N) (p:=p) β R hR] with ω hω
  exact supError_nonneg (square_nonempty T)
    (((square_isCompact T).image (hω.sub (responsePrimitive_continuous_nonnegative hd)).abs).bddAbove)

 theorem gammaCenteredSup_eq_modelSup (β T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    gammaCenteredSup N p β (N+1) (modelRadius_pos N) T ω=gammaCenteredModelSup N p β T ω := by
  unfold gammaCenteredSup DyadicSquareSupremum.squareSup gammaCenteredModelSup supError
  congr 1
  congr 1
  funext z
  have he := ActualCanonicalMeanKernelExtraction.gammaMean_eq_annealedGammaPair
    (N:=N) (p:=p) β (N+1) (modelRadius_pos N) z
  simpa only [ActualMeanKernelTimeCompactness.gammaMean,modelGamma,Function.uncurry] using
    congrArg (fun r => |actualGamma β (N+1) (modelRadius_pos N) z.1 z.2 ω-r|) he

 theorem correlationCKSup_memLp_two (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    MemLp (correlationCKSup N p β (N+1) (modelRadius_pos N) d T) 2 (AnnealedModelLaw.law N p) := by
  apply MemLp.of_bound (correlationCKSup_aestronglyMeasurable hN β (N+1)
    (modelRadius_pos N) (modelRadius_sq N) d hd T) (4+2*|correlationMeanSupError N p β d T|)
  filter_upwards [correlationCKSup_nonneg β (N+1) (modelRadius_pos N) d hd T,
    correlationCKSup_sq_shift hN hp β d hd T,
    overlapCenteredSup_bounds hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N) T] with ω hn hs hb
  rw [Real.norm_eq_abs,abs_of_nonneg hn]
  have hc : (overlapCenteredSup N p β (N+1) (modelRadius_pos N) T ω)^2≤4 := by nlinarith [hb.1,hb.2]
  have ha := abs_nonneg (correlationMeanSupError N p β d T)
  have he := sq_abs (correlationMeanSupError N p β d T)
  nlinarith

 theorem gammaCKSup_memLp_two (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    MemLp (gammaCKSup N p β (N+1) (modelRadius_pos N) d T) 2 (AnnealedModelLaw.law N p) := by
  apply ((gammaCenteredSup_memLp_two hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N) T).add
    (memLp_const |gammaMeanSupError N p β d T|)).of_le
      (gammaCKSup_aestronglyMeasurable hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) d hd T)
  filter_upwards [gammaCKSup_nonneg β (N+1) (modelRadius_pos N) d hd T,
    gammaCKSup_shift hN hp β d hd T,
    gammaCenteredSup_bounds hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N) T] with ω hn hs hb
  rw [Real.norm_eq_abs,abs_of_nonneg hn,Real.norm_eq_abs,Pi.add_apply,
    abs_of_nonneg (add_nonneg hb.1 (abs_nonneg _)),gammaCenteredSup_eq_modelSup]
  exact hs.trans (add_le_add_right (le_abs_self _) _)

 theorem correlationCKSup_secondMoment_le (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    (∫ω,(correlationCKSup N p β (N+1) (modelRadius_pos N) d T ω)^2 ∂AnnealedModelLaw.law N p)≤
      2*(∫ω,(overlapCenteredSup N p β (N+1) (modelRadius_pos N) T ω)^2 ∂AnnealedModelLaw.law N p)+
        2*(correlationMeanSupError N p β d T)^2 := by
  have hi := (overlapCenteredSup_memLp_two hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N) T).integrable_sq
  have hh := integral_mono_ae (correlationCKSup_memLp_two hN hp β d hd T).integrable_sq
    ((hi.const_mul 2).add (integrable_const _)) (correlationCKSup_sq_shift hN hp β d hd T)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hi.const_mul 2) (integrable_const _),integral_const_mul] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

 theorem gammaCKSup_firstMoment_le (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    (∫ω,gammaCKSup N p β (N+1) (modelRadius_pos N) d T ω ∂AnnealedModelLaw.law N p)≤
      (∫ω,gammaCenteredSup N p β (N+1) (modelRadius_pos N) T ω ∂AnnealedModelLaw.law N p)+
        gammaMeanSupError N p β d T := by
  have hi := (gammaCenteredSup_memLp_two hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N) T).integrable (by norm_num)
  have hs := gammaCKSup_shift hN hp β d hd T
  simp_rw [←gammaCenteredSup_eq_modelSup] at hs
  have hh := integral_mono_ae ((gammaCKSup_memLp_two hN hp β d hd T).integrable (by norm_num))
    (hi.add (integrable_const _)) hs
  simp only [Pi.add_apply] at hh
  rw [integral_add hi (integrable_const _)] at hh
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

 theorem actual_correlation_ck_compact_secondMoment_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ω,(correlationCKSup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω)^2
      ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  have hc := actual_overlap_centered_compact_secondMoment_tendsto_zero dim hdim (by omega : 2≤p) β T
  have hm := (actual_correlation_mean_supError_tendsto_zero dim hdim hp β hβ d hd T).pow 2
  have hu := (hc.const_mul 2).add (hm.const_mul 2)
  simp only [zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg (fun _ => sq_nonneg _))) _ hu
  filter_upwards [hdim.eventually (eventually_ge_atTop 1)] with n hn
  exact correlationCKSup_secondMoment_le hn (by omega : 0<p) β d hd T

 theorem actual_gamma_ck_compact_firstMoment_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Tendsto (fun n => ∫ω,gammaCKSup (dim n) p β (dim n+1) (modelRadius_pos (dim n)) d T ω
      ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  have hc := actual_gamma_centered_compact_firstMoment_tendsto_zero dim hdim (by omega : 2≤p) β T
  have hm := actual_gamma_mean_supError_tendsto_zero dim hdim hp β hβ d hd T
  have hu := hc.add hm
  simp only [zero_add] at hu
  apply squeeze_zero' (Eventually.of_forall (fun n => integral_nonneg_of_ae
    (gammaCKSup_nonneg β (dim n+1) (modelRadius_pos (dim n)) d hd T))) _ hu
  filter_upwards [hdim.eventually (eventually_ge_atTop 1)] with n hn
  exact gammaCKSup_firstMoment_le hn (by omega : 0<p) β d hd T

end SphericalAging.ActualCKCompactPathConvergence
