module

public import SphericalAging.ActualGammaCompactSup
public import SphericalAging.ActualGammaDyadicApproximation
public import SphericalAging.ActualGammaCompactConcentration
public import SphericalAging.TwoScaleRootConcentrationLimit

public section

/-! The actual full compact centered Γ supremum converges in first mean.
Its proof uses only actual finite-mesh variances, dyadic path tightness and
the genuine Brownian compact maximum moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ActualGammaCompactPathConcentration
open HardSphereDynamics ActualBrownianPrimitiveTimeModulus ActualNormalizedGamma
open ActualGammaDyadicApproximation ActualOverlapCompactPathConcentration
open ActualStateDyadicTightness ActualGammaCompactConcentration ActualOverlapVarianceLimit
open DyadicSquareSupremum CountableCenteredSup UnboundedCountableMeshConcentration
open TwoScaleRootConcentrationLimit
variable {N p : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[expose] def meshGamma (β R : ℝ≥0) (hR : 0<(R:ℝ)) (T : ℝ≥0) (m : ℕ) (k : MeshIndex m) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
  actualGamma β R hR (StochasticCalculus.uniformPartitionTime T (2^m) k.1.val)
    (StochasticCalculus.uniformPartitionTime T (2^m) k.2.val)

@[expose] def gammaMeshRemainderCeiling (p : ℕ) (β T : ℝ≥0) (m : ℕ) : ℝ :=
  2*gridErrorCeiling m*(1+Real.sqrt (1+3*(T:ℝ)^2))+
    4*Real.sqrt ((1+3*(T:ℝ)^2)*gammaTailProbabilityCeiling p β T m)

theorem gammaCenteredSup_integral_le_mesh (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R:ℝ)) (hNR : (N:ℝ)<(R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    (∫ω,gammaCenteredSup N p β R hR T ω ∂AnnealedModelLaw.law N p)≤
      ((2^m+1:ℕ):ℝ)^2*Real.sqrt (compactVarianceCeiling p β (T+1)/(N:ℝ))+
        gammaMeshRemainderCeiling p β T m := by
  have hn : 1≤N := by omega
  have hp0 : 0<p := by omega
  let P := AnnealedModelLaw.law N p
  have he : 0≤gridErrorCeiling m := by norm_num [gridErrorCeiling,dyadicRatio]; positivity
  have hg := centeredSup_integral_le (gridGamma (p:=p) β R hR T)
    (meshGamma (p:=p) β R hR T m) (gridToMesh T m)
    (fun i => actualGamma_memLp_two hn β R hR hNR _ _)
    (fun k => actualGamma_memLp_two hn β R hR hNR _ _)
    (gammaEnvelope_memLp_two T) (.of_forall (gammaEnvelope_nonneg T))
    ((actualGamma_uniform_envelope hn β R hR hNR T).mono (fun ω hω i =>
      hω _ _ (gridPair_mem_square T i).2))
    ((actualGamma_uniform_envelope hn β R hR hNR T).mono (fun ω hω k =>
      hω _ _ (StochasticCalculus.uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^m)
        (Nat.le_of_lt_succ k.2.isLt)).2))
    (gammaBadTail_measurableSet β R hR T m) he
    ((actualGamma_grid_approximation_on_good hn β R hR hNR T m).mono (fun ω hω hgood i =>
      hω hgood (gridPair T i).1 (gridPair T i).2 (gridPair_mem_square T i).1 (gridPair_mem_square T i).2))
  have hEq : (∫ω,gammaCenteredSup N p β R hR T ω ∂P)=
      ∫ω,centeredSup (gridGamma (p:=p) β R hR T) P ω ∂P :=
    integral_congr_ae (gammaCenteredSup_ae_countable hn hp0 β R hR hNR T)
  rw [hEq]
  have hmesh : (∑k : MeshIndex m,∫ω,|meshGamma (p:=p) β R hR T m k ω-
      ∫z,meshGamma β R hR T m k z ∂P| ∂P)≤
      ((2^m+1:ℕ):ℝ)^2*Real.sqrt (compactVarianceCeiling p β (T+1)/(N:ℝ)) := by
    calc
      _≤∑k : MeshIndex m,Real.sqrt (compactVarianceCeiling p β (T+1)/(N:ℝ)) := by
        apply Finset.sum_le_sum
        intro k _
        exact actual_gamma_centered_L1_le_square hN hp β R hR hNR _ _ (T+1)
          ((StochasticCalculus.uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^m)
            (Nat.le_of_lt_succ k.1.isLt)).2.trans (le_add_right le_rfl))
          ((StochasticCalculus.uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^m)
            (Nat.le_of_lt_succ k.2.isLt)).2.trans (le_add_right le_rfl)) (by positivity)
      _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_mul];ring
  have hmean : 2*gridErrorCeiling m*(1+(∫ω,gammaEnvelope (N:=N) (p:=p) T ω ∂P))≤
      2*gridErrorCeiling m*(1+Real.sqrt (1+3*(T:ℝ)^2)) :=
    mul_le_mul_of_nonneg_left (add_le_add (le_rfl : (1:ℝ)≤1) (gammaEnvelope_mean_le (p:=p) hn T)) (by positivity)
  have htail : Real.sqrt ((∫ω,(gammaEnvelope (N:=N) (p:=p) T ω)^2 ∂P)*
      P.real (gammaBadTail β R hR T m))≤
      Real.sqrt ((1+3*(T:ℝ)^2)*gammaTailProbabilityCeiling p β T m) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul (gammaEnvelope_secondMoment_le hn T)
      (gammaBadTail_real_le hn hp0 β R hR hNR T m) measureReal_nonneg (by positivity)
  have hh := hg.trans (add_le_add (add_le_add hmesh hmean) (mul_le_mul_of_nonneg_left htail (by norm_num)))
  convert hh using 1 <;> dsimp only [P,gammaMeshRemainderCeiling] <;> ring

theorem gammaMeshRemainderCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (gammaMeshRemainderCeiling p β T) atTop (𝓝 0) := by
  have h1 := (gridErrorCeiling_tendsto_zero.const_mul 2).mul_const (1+Real.sqrt (1+3*(T:ℝ)^2))
  have hprod : Tendsto (fun m => (1+3*(T:ℝ)^2)*gammaTailProbabilityCeiling p β T m) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (gammaTailProbabilityCeiling_tendsto_zero p β T).const_mul (1+3*(T:ℝ)^2)
  have h2 := hprod.sqrt
  unfold gammaMeshRemainderCeiling
  simpa only [mul_zero,zero_mul,Real.sqrt_zero,zero_add] using
    h1.add (h2.const_mul 4)

theorem actual_gamma_centered_compact_firstMoment_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 2≤p) (β T : ℝ≥0) :
    Tendsto (fun n => ∫ω,gammaCenteredSup (dim n) p β (modelRadius (dim n))
      (modelRadius_pos (dim n)) T ω ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  refine tendsto_zero_of_root_dimension_mesh_bound_eventually _
    (fun m => ((2^m+1:ℕ):ℝ)^2) _ dim ?_ hdim
    (gammaMeshRemainderCeiling_tendsto_zero p β T) (compactVarianceCeiling p β (T+1)) ?_
  · filter_upwards [hdim.eventually (eventually_ge_atTop 3)] with n hn
    exact integral_nonneg_of_ae ((gammaCenteredSup_bounds (by omega : 1≤dim n) (by omega : 0<p)
      β _ _ (modelRadius_sphere_bound (dim n)) T).mono (fun _ h => h.1))
  · intro m
    filter_upwards [hdim.eventually (eventually_ge_atTop 3)] with n hn
    exact gammaCenteredSup_integral_le_mesh hn hp β _ _ (modelRadius_sphere_bound (dim n)) T m

end SphericalAging.ActualGammaCompactPathConcentration
