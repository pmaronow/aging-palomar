module

public import SphericalAging.ActualSphereBackwardPairing
public import SphericalAging.TwoTimeResponseTrace

public section

/-! The literal physical Brownian pairing is the integral of the actual
backward mean derivative composed with the tangent projection. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereBrownianPairing
open HardSphereDynamics LocalSDE VectorIto AnnealedSDECore MultivariateTaylor
open ActualSphereTransition ActualSphereBackwardIto PhysicalC2Ito
open ActualSphereBackwardVariance ActualSphereBackwardPairing
open ActualSphereLinearTransition PredictablePrefixPairing
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Genuine product-time integrability of the backward integrand, obtained
from its constructed predictable L² class and the actual Brownian prefix. -/
theorem backward_kernel_integrable (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T s : ℝ≥0) (j : Fin N)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i k z => noiseColumn z k i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (hreg : SpatialC2Transition β R hR J f) :
    Integrable (FourPapersCommon.continuousAdaptedTimeCut
      (fun r ω => fderiv ℝ (transition (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J (T-r) f) (X r ω) (noiseColumn (X r ω) j)) (min T s))
      (nonnegativeLebesgueMeasure.prod (VectorBrownian.law N)) := by
  let P₀ := VectorBrownian.law N
  let F₀ := NullAugmentation.augment (VectorBrownian.filtration N) P₀
  let g (r : ℝ≥0) (ω : VectorBrownian.Space N) := fderiv ℝ
    (transition (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-r) f)
      (X r ω) (noiseColumn (X r ω) j)
  obtain ⟨V,hV,he⟩ := backward_transition_ito hN β R hR hNR J X T hX hSphere hf hreg
  let U : PredictableProcessL2 F₀ P₀ := ∑ i,V i j
  have hU : (U : TimeProcessL2 P₀)=ᵐ[nonnegativeLebesgueMeasure.prod P₀]
      FourPapersCommon.continuousAdaptedTimeCut g T := by
    have hcoe := Lp.coeFn_fun_finsetSum Finset.univ (fun i => (V i j : TimeProcessL2 P₀))
    have hrows := ae_all_iff.mpr (fun i : Fin N => hV i j)
    filter_upwards [hcoe,hrows] with q hq hv
    have hq' : (U : TimeProcessL2 P₀) q=∑ i : Fin N,(V i j : TimeProcessL2 P₀) q := by
      simpa only [U,Submodule.coe_sum] using hq
    rw [hq']
    simp only [hv,FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs with hr
    · exact (derivative_coordinates _ _ _).symm
    · simp
  exact (inner_onePrefix_timeCut U g T s hU).1

/-- Actual fixed-initial-state linear observation paired with the true
Brownian coordinate. The deterministic mean term vanishes by Brownian centering. -/
theorem linear_brownian_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (X : ℝ≥0 → VectorBrownian.Space N → State N)
    (T s : ℝ≥0) (a : State N) (j : Fin N)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i k z => noiseColumn z k i) (fun _ => x) X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) :
    (∫ ω,⟪a,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω ∂VectorBrownian.law N)=
    ∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,
      ⟪a,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-r))
        (X r ω) (noiseColumn (X r ω) j)⟫_ℝ
          ∂VectorBrownian.law N ∂nonnegativeLebesgueMeasure := by
  have he := linear_innovation_pairing hN β R hR hNR J X T s a j hX hSphere
  have hmX := ShiftedRandomSDE.waiting_state_memLp X hX.2.1 hSphere T
  have hmB := (VectorBrownian.coordinate_isPreBrownian j).isGaussianProcess.hasGaussianLaw_eval s |>.memLp_two
  have hi : Integrable (fun ω => ⟪a,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω) (VectorBrownian.law N) := by
    have hh := ((innerSL ℝ a).comp_memLp' hmX).integrable_mul hmB
    change Integrable (fun ω => ⟪a,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω)
      (VectorBrownian.law N) at hh
    exact hh
  have hiC := ((VectorBrownian.coordinate_isPreBrownian j).integrable_eval s).const_mul
    ⟪a,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J T x⟫_ℝ
  simp_rw [sub_mul] at he
  rw [integral_sub hi hiC,integral_const_mul,(VectorBrownian.coordinate_isPreBrownian j).integral_eval,
    mul_zero,sub_zero] at he
  exact he

/-- Product-time integrability yields an honest time-integrable expected
kernel on the same prefix. -/
lemma timeIntegral_integrableOn_of_timeCut_integrable
    (g : ℝ≥0 → VectorBrownian.Space N → ℝ) (H : ℝ≥0)
    (hg : Integrable (FourPapersCommon.continuousAdaptedTimeCut g H)
      (nonnegativeLebesgueMeasure.prod (VectorBrownian.law N))) :
    IntegrableOn (fun r => ∫ ω,g r ω ∂VectorBrownian.law N)
      (Ioc (0 : ℝ≥0) H) nonnegativeLebesgueMeasure := by
  have hi := hg.integral_prod_left
  have he : (fun r => ∫ ω,FourPapersCommon.continuousAdaptedTimeCut g H (r,ω)
      ∂VectorBrownian.law N)=
      (Ioc (0 : ℝ≥0) H).indicator (fun r => ∫ ω,g r ω ∂VectorBrownian.law N) := by
    funext r
    by_cases hr : r∈Ioc (0 : ℝ≥0) H
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,if_pos hr,indicator_of_mem hr]
    · simp only [FourPapersCommon.continuousAdaptedTimeCut,if_neg hr,integral_zero,indicator_of_notMem hr]
  rw [he] at hi
  exact (integrable_indicator_iff measurableSet_Ioc).mp hi

/-- At each actual sphere time, every projected mean derivative column
is integrable. This follows from continuity and sphere compactness. -/
lemma projected_kernel_integrable (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0 → VectorBrownian.Space N → State N)
    (hXa : StronglyAdapted (NullAugmentation.augment (VectorBrownian.filtration N)
      (VectorBrownian.law N)) X)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    (τ r : ℝ≥0) (a : State N) (j : Fin N) :
    Integrable (fun ω => ⟪a,fderiv ℝ (mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ)
      (X r ω) (projection (X r ω) (basisVector j))⟫_ℝ) (VectorBrownian.law N) := by
  let g : State N → ℝ := fun y => ⟪a,fderiv ℝ (mean
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ) y
      (projection y (basisVector j))⟫_ℝ
  have hcD : Continuous (fun y : State N => fderiv ℝ (mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J τ) y) :=
    (ActualSphereMeanJointSpatialContinuity.mean_fderiv_joint_continuous
      (VectorBrownian.driver N) β J R hR).comp (continuous_const.prodMk continuous_id)
  have hcP : Continuous (fun y : State N => projection y (basisVector j)) :=
    contDiff_projection_pair.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hgc : Continuous g := continuous_const.inner (hcD.clm_apply hcP)
  obtain ⟨C,hC⟩ := ActualSphereTimeLipschitz.observable_bound_onSphere g hgc R hR hNR
  have hm : MemLp (fun ω => g (X r ω)) 2 (VectorBrownian.law N) :=
    MemLp.of_bound (hgc.comp_stronglyMeasurable ((hXa r).mono
      ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le r))).aestronglyMeasurable
      C (hSphere.mono (fun ω h => hC _ (h r)))
  exact hm.integrable (by norm_num)

/-- The expected projected backward column is genuinely time integrable. -/
theorem projected_kernel_time_integrable (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T s : ℝ≥0) (a : State N) (j : Fin N)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i k z => noiseColumn z k i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) :
    IntegrableOn (fun r => ∫ ω,⟪a,fderiv ℝ (mean
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (T-r))
      (X r ω) (projection (X r ω) (basisVector j))⟫_ℝ ∂VectorBrownian.law N)
      (Ioc (0 : ℝ≥0) (min T s)) nonnegativeLebesgueMeasure := by
  have hi := timeIntegral_integrableOn_of_timeCut_integrable _ _
    (backward_kernel_integrable hN β R hR hNR J X T s j hX hSphere
      (f := fun y => ⟪a,y⟫_ℝ) (innerSL ℝ a).contDiff
      (ActualSphereLinearRegularity.linear_spatialC2Transition β R hR J a))
  simp only [fderiv_transition_inner,noiseColumn,map_smul,real_inner_smul_right,smul_eq_mul,integral_const_mul] at hi
  exact (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ)<2)).ne') _).mp hi

/-- Exact physical vector Brownian pairing. The kernel is the actual
backward mean Jacobian trace on the tangent space; no response or Gaussian
integration-by-parts identity is assumed. -/
theorem brownian_trace_pairing (hN : N≠0) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    (x : State N) (X : ℝ≥0 → VectorBrownian.Space N → State N) (T s : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i k z => noiseColumn z k i) (fun _ => x) X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω)) :
    (∫ ω,⟪X T ω,WithLp.toLp 2 (fun j => VectorBrownian.coordinate j s ω)⟫_ℝ
      ∂VectorBrownian.law N)=
    Real.sqrt 2*(∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,∑ j : Fin N,
      ⟪basisVector j,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J (T-r)) (X r ω) (projection (X r ω) (basisVector j))⟫_ℝ
          ∂VectorBrownian.law N ∂nonnegativeLebesgueMeasure) := by
  let P₀ := VectorBrownian.law N
  let g (j : Fin N) (r : ℝ≥0) (ω : VectorBrownian.Space N) :=
    ⟪basisVector j,fderiv ℝ (mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J (T-r)) (X r ω) (projection (X r ω) (basisVector j))⟫_ℝ
  have hmX := ShiftedRandomSDE.waiting_state_memLp X hX.2.1 hSphere T
  have hi (j : Fin N) : Integrable
      (fun ω => ⟪basisVector j,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω) P₀ := by
    have hh := ((innerSL ℝ (basisVector j)).comp_memLp' hmX).integrable_mul
      ((VectorBrownian.coordinate_isPreBrownian j).isGaussianProcess.hasGaussianLaw_eval s).memLp_two
    change Integrable (fun ω => ⟪basisVector j,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω) P₀ at hh
    exact hh
  have hgt (j : Fin N) : IntegrableOn (fun r => ∫ ω,g j r ω ∂P₀)
      (Ioc (0 : ℝ≥0) (min T s)) nonnegativeLebesgueMeasure :=
    projected_kernel_time_integrable hN β R hR hNR J X T s (basisVector j) j hX hSphere
  have hg (r : ℝ≥0) (j : Fin N) : Integrable (g j r) P₀ :=
    projected_kernel_integrable β R hR hNR J X hX.2.1 hSphere (T-r) r (basisVector j) j
  have he (j : Fin N) := linear_brownian_pairing hN β R hR hNR J x X T s (basisVector j) j hX hSphere
  simp only [noiseColumn,map_smul,real_inner_smul_right,smul_eq_mul,integral_const_mul] at he
  calc
    _ = ∫ ω,∑ j : Fin N,⟪basisVector j,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω ∂P₀ := by
      apply integral_congr_ae
      exact .of_forall (fun ω => by
        have hcoords (j : Fin N) : ⟪basisVector j,X T ω⟫_ℝ=(X T ω) j := by
          rw [real_inner_comm,basis_inner]
        simp_rw [hcoords]
        simp only [PiLp.inner_apply,RCLike.inner_apply,PiLp.toLp_apply,starRingEnd_apply,star_trivial]
        apply Finset.sum_congr rfl
        intro j hj
        ring)
    _ = ∑ j : Fin N,∫ ω,⟪basisVector j,X T ω⟫_ℝ*VectorBrownian.coordinate j s ω ∂P₀ :=
      integral_finsetSum _ (fun j _ => hi j)
    _ = ∑ j : Fin N,Real.sqrt 2*(∫ r in Ioc (0 : ℝ≥0) (min T s),∫ ω,g j r ω ∂P₀
        ∂nonnegativeLebesgueMeasure) := Finset.sum_congr rfl (fun j _ => he j)
    _ = Real.sqrt 2*(∫ r in Ioc (0 : ℝ≥0) (min T s),∑ j : Fin N,∫ ω,g j r ω ∂P₀
        ∂nonnegativeLebesgueMeasure) := by
      rw [integral_finsetSum _ (fun j _ => hgt j),Finset.mul_sum]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      exact .of_forall (fun r => (integral_finsetSum _ (fun j _ => hg r j)).symm)

end SphericalAging.ActualSphereBrownianPairing
