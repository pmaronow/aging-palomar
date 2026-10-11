module

public import SphericalAging.WienerPairingFunctional
public import Mathlib.Topology.MetricSpace.UniformConvergence

public section

/-! Weighted Wiener observables from unweighted prefix observables. This
module exposes the exact preceding Brownian-response primitive convergence
as an input, and proves the extension to all actual trunk L² weights. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
namespace SphericalAging.WeightedWienerExtension
open WienerVectorGaussian WienerTrunkWeight WienerPairingFunctional FiniteModel VectorBrownian

@[expose] def cutoffLp (T : ℝ≥0) (k : TimeL2) : TimeL2 :=
  ((Lp.memLp k).indicator measurableSet_Ioc).toLp ((Ioc (0:ℝ≥0) T).indicator k)

theorem cutoffLp_coe (T : ℝ≥0) (k : TimeL2) :
    (cutoffLp T k : ℝ≥0→ℝ)=ᵐ[nonnegativeLebesgueMeasure] (Ioc (0:ℝ≥0) T).indicator k :=
  ((Lp.memLp k).indicator measurableSet_Ioc).coeFn_toLp

theorem cutoffLp_norm_le (T : ℝ≥0) (k : TimeL2) : ‖cutoffLp T k‖≤‖k‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [cutoffLp_coe T k] with u hu
  rw [hu]
  by_cases h : u∈Ioc (0:ℝ≥0) T
  · simp [indicator_of_mem h]
  · simp [indicator_of_notMem h]

@[expose] def cutoffLinear (T : ℝ≥0) : TimeL2 →ₗ[ℝ] TimeL2 where
  toFun := cutoffLp T
  map_add' k l := by
    apply Lp.ext
    filter_upwards [cutoffLp_coe T (k+l),cutoffLp_coe T k,cutoffLp_coe T l,
      Lp.coeFn_add k l,Lp.coeFn_add (cutoffLp T k) (cutoffLp T l)] with u h1 h2 h3 h4 h5
    by_cases hu : u∈Ioc (0:ℝ≥0) T
    · simp only [h1,h5,h2,h3,indicator_of_mem hu,Pi.add_apply,h4]
    · simp only [h1,h5,h2,h3,indicator_of_notMem hu,Pi.add_apply,add_zero]
  map_smul' c k := by
    change cutoffLp T (c • k)=c • cutoffLp T k
    apply Lp.ext
    filter_upwards [cutoffLp_coe T (c • k),cutoffLp_coe T k,
      Lp.coeFn_smul c k,Lp.coeFn_smul c (cutoffLp T k)] with u h1 h2 h3 h4
    by_cases hu : u∈Ioc (0:ℝ≥0) T
    · simp only [h1,h2,h4,indicator_of_mem hu,Pi.smul_apply,h3]
    · simp only [h1,h2,h4,indicator_of_notMem hu,Pi.smul_apply,smul_zero]

@[expose] def cutoff (T : ℝ≥0) : TimeL2 →L[ℝ] TimeL2 :=
  (cutoffLinear T).mkContinuous 1 (fun k => by simpa [cutoffLinear] using cutoffLp_norm_le T k)

theorem cutoff_intervalIndicator (T u : ℝ≥0) :
    cutoff T (intervalIndicator u)=intervalIndicator (min u T) := by
  apply Lp.ext
  filter_upwards [cutoffLp_coe T (intervalIndicator u),
    indicatorConstLp_coeFn (μ:=nonnegativeLebesgueMeasure) (p:=2) (hs:=measurableSet_Ioc)
      (hμs:=nonnegativeLebesgueMeasure_Ioc_ne_top 0 u) (c:=(1:ℝ)),
    indicatorConstLp_coeFn (μ:=nonnegativeLebesgueMeasure) (p:=2) (hs:=measurableSet_Ioc)
      (hμs:=nonnegativeLebesgueMeasure_Ioc_ne_top 0 (min u T)) (c:=(1:ℝ))] with v h1 h2 h3
  change cutoffLp T (intervalIndicator u) v=intervalIndicator (min u T) v
  rw [h1]
  unfold intervalIndicator
  rw [h3]
  by_cases hvT : v∈Ioc (0:ℝ≥0) T
  · rw [indicator_of_mem hvT,h2]
    by_cases hvu : v∈Ioc (0:ℝ≥0) u
    · have hvmin : v∈Ioc (0:ℝ≥0) (min u T) := ⟨hvu.1,le_min hvu.2 hvT.2⟩
      simp only [indicator_of_mem hvu,indicator_of_mem hvmin]
    · rw [indicator_of_notMem hvu,indicator_of_notMem]
      exact fun hv => hvu ⟨hv.1,hv.2.trans (min_le_left _ _)⟩
  · rw [indicator_of_notMem hvT,indicator_of_notMem]
    exact fun hv => hvT ⟨hv.1,hv.2.trans (min_le_right _ _)⟩

theorem cutoff_weight {k : ℝ→ℝ} {T : ℝ≥0} (hk : ContinuousOn k (Icc 0 (T:ℝ))) :
    cutoff T (weight k T hk)=weight k T hk := by
  apply Lp.ext
  filter_upwards [cutoffLp_coe T (weight k T hk),weight_coe hk] with u h1 h2
  change cutoffLp T (weight k T hk) u=weight k T hk u
  rw [h1]
  by_cases hu : u∈Ioc (0:ℝ≥0) T
  · simp only [indicator_of_mem hu]
  · rw [indicator_of_notMem hu,h2]
    simp only [cutWeight,indicator_of_notMem hu]

theorem tendsto_of_prefix {ι : Type*} {l : Filter ι}
    (F : ι→TimeL2→L[ℝ]ℝ) (G : TimeL2→L[ℝ]ℝ)
    (hbound : ∀ i,‖F i‖≤1)
    (hprefix : ∀ t : ℝ≥0,Tendsto (fun i => F i (intervalIndicator t)) l
      (𝓝 (G (intervalIndicator t)))) (k : TimeL2) :
    Tendsto (fun i => F i k) l (𝓝 (G k)) := by
  have hequi : Equicontinuous (fun i k => F i k) :=
    (LipschitzWith.uniformEquicontinuous (fun i k => F i k) 1
      (fun i => (F i).lipschitzWith.weaken (show ‖F i‖₊≤1 from hbound i))).equicontinuous
  apply denseRange_stepToLp.induction_on
    (p:=fun k => Tendsto (fun i => F i k) l (𝓝 (G k))) k
    (hequi.isClosed_setOfPred_tendsto G.continuous)
  intro v
  have hh := tendsto_finset_sum v.support
    (fun t _ => (hprefix t).const_smul (v t))
  simpa only [stepToLp,Finsupp.linearCombination_apply,Finsupp.sum,
    map_sum,map_smul,Finset.sum_apply] using hh

theorem cutoff_norm_le (T : ℝ≥0) : ‖cutoff T‖≤1 := by
  apply (cutoff T).opNorm_le_bound (by norm_num)
  intro k
  change ‖cutoffLp T k‖≤1*‖k‖
  simpa only [one_mul] using cutoffLp_norm_le T k

theorem weight_inner {f g : ℝ→ℝ} {T : ℝ≥0}
    (hf : ContinuousOn f (Icc 0 (T:ℝ))) (hg : ContinuousOn g (Icc 0 (T:ℝ))) :
    ⟪weight f T hf,weight g T hg⟫_ℝ=∫u in (0:ℝ)..(T:ℝ),f u*g u := by
  rw [L2.inner_def]
  calc
    _ = ∫u in Ioc (0:ℝ≥0) T,clampedWeight f T u*clampedWeight g T u
        ∂nonnegativeLebesgueMeasure := by
      rw [←integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      filter_upwards [weight_coe hf,weight_coe hg] with u h1 h2
      by_cases hu : u∈Ioc (0:ℝ≥0) T
      · simp [h1,h2,cutWeight,hu,RCLike.inner_apply,mul_comm]
      · simp [h1,h2,cutWeight,hu,RCLike.inner_apply]
    _ = ∫u in Ioc (0:ℝ≥0) T,f u*g u ∂nonnegativeLebesgueMeasure := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only [clampedWeight]
      rw [min_eq_left (show (u:ℝ)≤T by exact_mod_cast hu.2)]
    _ = _ := nnreal_interval_integral T (fun u => f u*g u)

@[expose] def responseFunctional (r : ℝ→ℝ) (T : ℝ≥0) (hr : ContinuousOn r (Icc 0 (T:ℝ))) :
    TimeL2→L[ℝ]ℝ := Real.sqrt 2 • innerSL ℝ (weight r T hr)

theorem responseFunctional_weight {r k : ℝ→ℝ} {T : ℝ≥0}
    (hr : ContinuousOn r (Icc 0 (T:ℝ))) (hk : ContinuousOn k (Icc 0 (T:ℝ))) :
    responseFunctional r T hr (weight k T hk)=Real.sqrt 2 *
      ∫u in (0:ℝ)..(T:ℝ),k u*r u := by
  simp only [responseFunctional,ContinuousLinearMap.smul_apply,innerSL_apply_apply,smul_eq_mul,
    weight_inner hr hk]
  congr 1
  apply intervalIntegral.integral_congr
  intro u _
  exact mul_comm _ _

theorem responseFunctional_prefix {r : ℝ→ℝ} {T : ℝ≥0}
    (hr : ContinuousOn r (Icc 0 (T:ℝ))) {u : ℝ≥0} (hu : u≤T) :
    responseFunctional r T hr (intervalIndicator u)=Real.sqrt 2 *
      ∫v in (0:ℝ)..(u:ℝ),r v := by
  simp only [responseFunctional,ContinuousLinearMap.smul_apply,innerSL_apply_apply,smul_eq_mul]
  congr 1
  rw [real_inner_comm,intervalIndicator,L2.inner_indicatorConstLp_one measurableSet_Ioc
    (nonnegativeLebesgueMeasure_Ioc_ne_top 0 u)]
  calc
    _ = ∫v in Ioc (0:ℝ≥0) u,r v ∂nonnegativeLebesgueMeasure := by
      apply integral_congr_ae
      filter_upwards [(weight_coe hr).restrict (s:=Ioc (0:ℝ≥0) u),
        ae_restrict_mem measurableSet_Ioc] with v hv hvu
      have hvT : v∈Ioc (0:ℝ≥0) T := ⟨hvu.1,hvu.2.trans hu⟩
      rw [hv,cutWeight,indicator_of_mem hvT]
      dsimp only [clampedWeight]
      rw [min_eq_left (show (v:ℝ)≤T by exact_mod_cast hvu.2.trans hu)]
    _ = _ := nnreal_interval_integral u r

/-- The preceding input is only convergence of the actual unweighted prefix
observables. Uniform norm control and genuine L² density prove the weighted
limit; no weighted convergence is assumed. -/
theorem weighted_from_unweighted {ι : Type*} {l : Filter ι}
    (F : ι→TimeL2→L[ℝ]ℝ) (hbound : ∀ i,‖F i‖≤1)
    {r k : ℝ→ℝ} {T : ℝ≥0}
    (hr : ContinuousOn r (Icc 0 (T:ℝ))) (hk : ContinuousOn k (Icc 0 (T:ℝ)))
    (hprefix : ∀ u : ℝ≥0,u≤T→Tendsto (fun i => F i (intervalIndicator u)) l
      (𝓝 (Real.sqrt 2 * ∫v in (0:ℝ)..(u:ℝ),r v))) :
    Tendsto (fun i => F i (weight k T hk)) l
      (𝓝 (Real.sqrt 2 * ∫u in (0:ℝ)..(T:ℝ),k u*r u)) := by
  let G := responseFunctional r T hr
  have hb (i : ι) : ‖(F i).comp (cutoff T)‖≤1 := by
    calc
      _ ≤ ‖F i‖*‖cutoff T‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1*1 := mul_le_mul (hbound i) (cutoff_norm_le T) (norm_nonneg _) (by norm_num)
      _ = _ := by norm_num
  have hp (u : ℝ≥0) :
      Tendsto (fun i => ((F i).comp (cutoff T)) (intervalIndicator u)) l
        (𝓝 ((G.comp (cutoff T)) (intervalIndicator u))) := by
    simp only [ContinuousLinearMap.comp_apply,cutoff_intervalIndicator]
    rw [show G (intervalIndicator (min u T))=Real.sqrt 2 *
      ∫v in (0:ℝ)..(min u T:ℝ≥0),r v from responseFunctional_prefix hr (min_le_right _ _)]
    exact hprefix (min u T) (min_le_right _ _)
  have hh := tendsto_of_prefix (fun i => (F i).comp (cutoff T)) (G.comp (cutoff T)) hb hp
    (weight k T hk)
  simpa only [ContinuousLinearMap.comp_apply,cutoff_weight hk,G,responseFunctional_weight hr hk] using hh

end SphericalAging.WeightedWienerExtension
