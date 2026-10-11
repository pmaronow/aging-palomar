module

public import SphericalAging.SecondVariationFourthMoment

public section

/-! Genuine predictable cubic derivative forcing. Its actual L² class
uses the proved fourth/eighth response moments, rather than a forcing premise. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SphericalAging.CubicVariationalSource
open HardSphereDynamics LinearSDETimeFourthMoment
set_option maxHeartbeats 1800000
set_option synthInstance.maxSize 1024
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

@[expose] def cubicField (g : State N→ℝ) (X U V W : ℝ≥0→Ω→State N)
    (t : ℝ≥0) (omega : Ω) : ℝ :=
  fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (X t omega) (U t omega) (V t omega) (W t omega)

lemma third_fderiv_continuous (g : State N→ℝ) (hg : ContDiff ℝ ∞ g) :
    Continuous (fderiv ℝ (fderiv ℝ (fderiv ℝ g))) :=
  ((hg.fderiv_right (m:=∞) (by simp)).fderiv_right (m:=∞) (by simp)).continuous_fderiv (by simp)

lemma cubicField_adapted (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (X U V W : ℝ≥0→Ω→State N)
    (hXa : StronglyAdapted F X) (hUa : StronglyAdapted F U)
    (hVa : StronglyAdapted F V) (hWa : StronglyAdapted F W) :
    StronglyAdapted F (cubicField g X U V W) := by
  intro t
  exact isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
    ((isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
      ((isBoundedBilinearMap_apply.continuous.comp_stronglyMeasurable
        (((third_fderiv_continuous g hg).comp_stronglyMeasurable (hXa t)).prodMk (hUa t))).prodMk
          (hVa t))).prodMk (hWa t))

lemma cubicField_continuous (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (X U V W : ℝ≥0→Ω→State N)
    (hXc : ∀ᵐomega∂P,Continuous (fun t => X t omega))
    (hUc : ∀ᵐomega∂P,Continuous (fun t => U t omega))
    (hVc : ∀ᵐomega∂P,Continuous (fun t => V t omega))
    (hWc : ∀ᵐomega∂P,Continuous (fun t => W t omega)) :
    ∀ᵐomega∂P,Continuous (fun t => cubicField g X U V W t omega) := by
  filter_upwards [hXc,hUc,hVc,hWc] with omega hx hu hv hw
  exact ((((third_fderiv_continuous g hg).comp hx).clm_apply hu).clm_apply hv).clm_apply hw

lemma cubicField_bound {g : State N→ℝ} {M : ℝ≥0}
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (X U V W : ℝ≥0→Ω→State N) (t : ℝ≥0) (omega : Ω) :
    ‖cubicField g X U V W t omega‖≤(M:ℝ)*‖U t omega‖*‖V t omega‖*‖W t omega‖ := by
  have hD : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (X t omega)‖≤(M:ℝ) :=
    norm_fderiv_le_of_lipschitz ℝ hM
  have h0 : ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (X t omega) (U t omega)‖≤(M:ℝ)*‖U t omega‖ :=
    ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (X t omega)).le_opNorm (U t omega)).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg _))
  have h1 := ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (X t omega) (U t omega)).le_opNorm
    (V t omega)).trans (mul_le_mul_of_nonneg_right h0 (norm_nonneg _))
  exact ((fderiv ℝ (fderiv ℝ (fderiv ℝ g)) (X t omega) (U t omega) (V t omega)).le_opNorm
    (W t omega)).trans (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))

section Source
variable (g : State N→ℝ) (hg : ContDiff ℝ ∞ g) {M : ℝ≥0}
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (X U V W : ℝ≥0→Ω→State N)
  (hXa : StronglyAdapted F X) (hUa : StronglyAdapted F U)
  (hVa : StronglyAdapted F V) (hWa : StronglyAdapted F W)
  (hXc : ∀ᵐomega∂P,Continuous (fun t => X t omega))
  (hUc : ∀ᵐomega∂P,Continuous (fun t => U t omega))
  (hVc : ∀ᵐomega∂P,Continuous (fun t => V t omega))
  (hWc : ∀ᵐomega∂P,Continuous (fun t => W t omega)) (T : ℝ≥0)
  (hU4 : MemLp (stateTimeCut U T) 4 (nonnegativeLebesgueMeasure.prod P))
  (hV8 : MemLp (stateTimeCut V T) 8 (nonnegativeLebesgueMeasure.prod P))
  (hW8 : MemLp (stateTimeCut W T) 8 (nonnegativeLebesgueMeasure.prod P))

include hg hXa hUa hVa hWa hXc hUc hVc hWc in
lemma cubicCut_predictable : AEStronglyMeasurable[F.predictable]
    (FourPapersCommon.continuousAdaptedTimeCut (cubicField g X U V W) T)
    (nonnegativeLebesgueMeasure.prod P) :=
  FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F _
    (cubicField_adapted g hg X U V W hXa hUa hVa hWa)
    (cubicField_continuous g hg X U V W hXc hUc hVc hWc) T

include hg hM hXa hUa hVa hWa hXc hUc hVc hWc hU4 hV8 hW8 in
lemma cubicCut_memLp : MemLp
    (FourPapersCommon.continuousAdaptedTimeCut (cubicField g X U V W) T) 2
    (nonnegativeLebesgueMeasure.prod P) := by
  have hvw : MemLp (fun q => ‖stateTimeCut V T q‖*‖stateTimeCut W T q‖) 4
      (nonnegativeLebesgueMeasure.prod P) := hV8.norm.fun_mul hW8.norm
  have hp : MemLp (fun q => ‖stateTimeCut U T q‖*(‖stateTimeCut V T q‖*‖stateTimeCut W T q‖)) 2
      (nonnegativeLebesgueMeasure.prod P) := hU4.norm.fun_mul hvw
  apply hp.of_le_mul (c:=(M:ℝ))
    ((cubicCut_predictable g hg X U V W hXa hUa hVa hWa hXc hUc hVc hWc T).mono (predictable_le_prod F))
  filter_upwards [] with q
  by_cases hq : q.1∈Ioc (0:ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,hq,ite_true,
      Real.norm_of_nonneg (by positivity : 0≤‖U q.1 q.2‖*(‖V q.1 q.2‖*‖W q.1 q.2‖))]
    simpa only [mul_assoc] using cubicField_bound hM X U V W q.1 q.2
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,hq,ite_false,
      norm_zero,mul_zero,zero_mul,le_refl]

@[expose] def source : PredictableProcessL2 F P :=
  ⟨(cubicCut_memLp g hg hM X U V W hXa hUa hVa hWa hXc hUc hVc hWc T hU4 hV8 hW8).toLp _,
    (cubicCut_predictable g hg X U V W hXa hUa hVa hWa hXc hUc hVc hWc T).congr
      (cubicCut_memLp g hg hM X U V W hXa hUa hVa hWa hXc hUc hVc hWc T hU4 hV8 hW8).coeFn_toLp.symm⟩

lemma source_coe : (source g hg hM X U V W hXa hUa hVa hWa hXc hUc hVc hWc T hU4 hV8 hW8 : TimeProcessL2 P)
    =ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (cubicField g X U V W) T :=
  (cubicCut_memLp g hg hM X U V W hXa hUa hVa hWa hXc hUc hVc hWc T hU4 hV8 hW8).coeFn_toLp
end Source
end SphericalAging.CubicVariationalSource
