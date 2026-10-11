module

public import SphericalAging.ActualCKCompactPathConvergence

public section

/-! The literal causal-triangle suprema used in manuscript source 3.3.
Their measurability and integrability are derived from the actual model,
and their errors are bounded by the genuine compact-square errors. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualCKSource33Suprema
open CompactKernelMemoryLimit ActualCompactCKMemoryLimit ActualCKPathSupremumMeasurability
  ActualCKMeanConvergenceOfEquicontinuity ActualCKMeanSupremumConvergence
  ActualCKCompactPathConvergence ActualModelOverlapVariance
  ActualBrownianPrimitiveTimeModulus CKNonnegativeKernelContinuity
  UniformSupremumError ContinuousSupremumMeasurability AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose]  def bridgeExpectationSup (N p : ℕ) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  sSup ((fun z : ℝ≥0×ℝ≥0 =>
    |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|^2+
    |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|) '' triangle T)

@[expose]  def bridgeProbabilitySup (N p : ℕ) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : ℝ :=
  sSup ((fun z : ℝ≥0×ℝ≥0 =>
    |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|+
    |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|) '' triangle T)

 theorem triangle_nonempty (T : ℝ≥0) : (triangle T).Nonempty := ⟨(0,0),le_rfl,zero_le⟩

 theorem bridgeExpectationSup_eq_causal (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    bridgeExpectationSup N p β R hR d T ω=sSup ((fun z : ℝ≥0×ℝ≥0 =>
      |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|^2+
      |actualGamma β R hR z.1 z.2 ω-(∫u in (0:ℝ)..(z.2:ℝ),d.R z.1 u)|) '' triangle T) := by
  unfold bridgeExpectationSup
  congr 1
  apply image_congr
  intro z hz
  simp only [ResponsePrimitiveInterchange.responsePrimitive,min_eq_right (NNReal.coe_le_coe.mpr hz.1)]

 theorem bridgeProbabilitySup_eq_causal (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) :
    bridgeProbabilitySup N p β R hR d T ω=sSup ((fun z : ℝ≥0×ℝ≥0 =>
      |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|+
      |actualGamma β R hR z.1 z.2 ω-(∫u in (0:ℝ)..(z.2:ℝ),d.R z.1 u)|) '' triangle T) := by
  unfold bridgeProbabilitySup
  congr 1
  apply image_congr
  intro z hz
  simp only [ResponsePrimitiveInterchange.responsePrimitive,min_eq_right (NNReal.coe_le_coe.mpr hz.1)]

 theorem bridgeExpectationSup_aestronglyMeasurable (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    AEStronglyMeasurable (bridgeExpectationSup N p β R hR d T) (AnnealedModelLaw.law N p) := by
  apply aestronglyMeasurable_sSup_image_of_ae_continuousOn
  · intro z _
    exact (((ActualOverlapTimeModulus.actualOverlap_memLp_two (p:=p) hN β R hR hNR z.1 z.2).aemeasurable.sub
      aemeasurable_const).norm.pow_const 2).add
        (((actualGamma_memLp_two (p:=p) hN β R hR hNR z.1 z.2).aemeasurable.sub aemeasurable_const).norm)
  · filter_upwards [actual_overlap_paths_continuous (N:=N) (p:=p) β R hR,
      actual_gamma_paths_continuous (N:=N) (p:=p) β R hR] with ω hC hG
    exact (((hC.sub (correlation_continuous_nonnegative hd)).abs.pow 2).add
      (hG.sub (responsePrimitive_continuous_nonnegative hd)).abs).continuousOn

 theorem bridgeProbabilitySup_aestronglyMeasurable (hN : 1≤N) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    AEStronglyMeasurable (bridgeProbabilitySup N p β R hR d T) (AnnealedModelLaw.law N p) := by
  apply aestronglyMeasurable_sSup_image_of_ae_continuousOn
  · intro z _
    exact (((ActualOverlapTimeModulus.actualOverlap_memLp_two (p:=p) hN β R hR hNR z.1 z.2).aemeasurable.sub
      aemeasurable_const).norm).add
        (((actualGamma_memLp_two (p:=p) hN β R hR hNR z.1 z.2).aemeasurable.sub aemeasurable_const).norm)
  · filter_upwards [actual_overlap_paths_continuous (N:=N) (p:=p) β R hR,
      actual_gamma_paths_continuous (N:=N) (p:=p) β R hR] with ω hC hG
    exact ((hC.sub (correlation_continuous_nonnegative hd)).abs.add
      (hG.sub (responsePrimitive_continuous_nonnegative hd)).abs).continuousOn

 theorem bridgeSup_bounds (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    ∀ᵐω ∂AnnealedModelLaw.law N p,
      0≤bridgeExpectationSup N p β R hR d T ω ∧
      bridgeExpectationSup N p β R hR d T ω≤(correlationCKSup N p β R hR d T ω)^2+gammaCKSup N p β R hR d T ω ∧
      0≤bridgeProbabilitySup N p β R hR d T ω ∧
      bridgeProbabilitySup N p β R hR d T ω≤correlationCKSup N p β R hR d T ω+gammaCKSup N p β R hR d T ω := by
  filter_upwards [actual_overlap_paths_continuous (N:=N) (p:=p) β R hR,
    actual_gamma_paths_continuous (N:=N) (p:=p) β R hR,
    correlationCKSup_nonneg β R hR d hd T] with ω hC hG hCn
  have hCB := ((square_isCompact T).image (hC.sub (correlation_continuous_nonnegative hd)).abs).bddAbove
  have hGB := ((square_isCompact T).image (hG.sub (responsePrimitive_continuous_nonnegative hd)).abs).bddAbove
  have hcp (z : ℝ≥0×ℝ≥0) (hz : z∈triangle T) := abs_le_supError hCB (triangle_subset_square T hz)
  have hgp (z : ℝ≥0×ℝ≥0) (hz : z∈triangle T) := abs_le_supError hGB (triangle_subset_square T hz)
  have hep (z : ℝ≥0×ℝ≥0) (hz : z∈triangle T) :
      |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|^2+
        |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|≤
          (correlationCKSup N p β R hR d T ω)^2+gammaCKSup N p β R hR d T ω := by
    have hc := hcp z hz
    have hg := hgp z hz
    change |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|≤correlationCKSup N p β R hR d T ω at hc
    change |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|≤
      gammaCKSup N p β R hR d T ω at hg
    exact add_le_add (pow_le_pow_left₀ (abs_nonneg _) hc 2) hg
  have hpp (z : ℝ≥0×ℝ≥0) (hz : z∈triangle T) :
      |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|+
        |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|≤
          correlationCKSup N p β R hR d T ω+gammaCKSup N p β R hR d T ω := add_le_add (hcp z hz) (hgp z hz)
  have hEB : BddAbove ((fun z : ℝ≥0×ℝ≥0 => |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|^2+
      |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|) '' triangle T) := by
    refine ⟨(correlationCKSup N p β R hR d T ω)^2+gammaCKSup N p β R hR d T ω,?_⟩
    rintro r ⟨z,hz,rfl⟩
    exact hep z hz
  have hPB : BddAbove ((fun z : ℝ≥0×ℝ≥0 => |actualOverlap β R hR z.1 z.2 ω-d.C z.1 z.2|+
      |actualGamma β R hR z.1 z.2 ω-ResponsePrimitiveInterchange.responsePrimitive d.R z.1 z.2|) '' triangle T) := by
    refine ⟨correlationCKSup N p β R hR d T ω+gammaCKSup N p β R hR d T ω,?_⟩
    rintro r ⟨z,hz,rfl⟩
    exact hpp z hz
  refine ⟨?_,?_,?_,?_⟩
  · exact (by positivity : 0≤|actualOverlap β R hR 0 0 ω-d.C 0 0|^2+
      |actualGamma β R hR 0 0 ω-ResponsePrimitiveInterchange.responsePrimitive d.R 0 0|).trans
        (le_csSup hEB ⟨(0,0),⟨le_rfl,zero_le⟩,rfl⟩)
  · exact csSup_le ((triangle_nonempty T).image _) (by rintro r ⟨z,hz,rfl⟩;exact hep z hz)
  · exact (add_nonneg (abs_nonneg _) (abs_nonneg _)).trans
      (le_csSup hPB ⟨(0,0),⟨le_rfl,zero_le⟩,rfl⟩)
  · exact csSup_le ((triangle_nonempty T).image _) (by rintro r ⟨z,hz,rfl⟩;exact hpp z hz)

 theorem bridgeExpectationSup_integrable (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Integrable (bridgeExpectationSup N p β (N+1) (modelRadius_pos N) d T) (AnnealedModelLaw.law N p) := by
  apply ((correlationCKSup_memLp_two hN hp β d hd T).integrable_sq.add
    ((gammaCKSup_memLp_two hN hp β d hd T).integrable (by norm_num))).mono'
      (bridgeExpectationSup_aestronglyMeasurable hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) d hd T)
  filter_upwards [bridgeSup_bounds β (N+1) (modelRadius_pos N) d hd T] with ω hb
  simpa only [Real.norm_eq_abs,abs_of_nonneg hb.1,Pi.add_apply] using hb.2.1

 theorem bridgeProbabilitySup_integrable (hN : 1≤N) (hp : 0<p) (β : ℝ≥0)
    (d : CKSpecification.CKData) (hd : CKSpecification.CKEquations p β d) (T : ℝ≥0) :
    Integrable (bridgeProbabilitySup N p β (N+1) (modelRadius_pos N) d T) (AnnealedModelLaw.law N p) := by
  apply (((correlationCKSup_memLp_two hN hp β d hd T).integrable (by norm_num)).add
    ((gammaCKSup_memLp_two hN hp β d hd T).integrable (by norm_num))).mono'
      (bridgeProbabilitySup_aestronglyMeasurable hN β (N+1) (modelRadius_pos N) (modelRadius_sq N) d hd T)
  filter_upwards [bridgeSup_bounds β (N+1) (modelRadius_pos N) d hd T] with ω hb
  simpa only [Real.norm_eq_abs,abs_of_nonneg hb.2.2.1,Pi.add_apply] using hb.2.2.2

end SphericalAging.ActualCKSource33Suprema
