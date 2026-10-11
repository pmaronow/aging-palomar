module

public import SphericalAging.WienerVectorGaussian
public import StochasticCalculus.QuadraticVariationDensity
public import SphericalAging.ProjectedTreeDrift

public section

/-! The actual L² trunk weight of a continuous deterministic source weight,
with exact normalization under the real interval integral. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory ProbabilityTheory StochasticCalculus
open scoped Topology ENNReal NNReal
namespace SphericalAging.WienerTrunkWeight
open WienerVectorGaussian FiniteModel VectorBrownian

lemma nnreal_interval_integral (T : ℝ≥0) (f : ℝ → ℝ) :
    (∫ u in Ioc (0:ℝ≥0) T,f u ∂nonnegativeLebesgueMeasure)=∫ u in (0:ℝ)..(T:ℝ),f u := by
  rw [intervalIntegral.integral_of_le T.coe_nonneg,←map_nonnegativeLebesgueMeasure_restrict_Ioc T]
  exact measurableEmbedding_nnrealCoe_iterated.integral_map f |>.symm

@[expose] def clampedWeight (k : ℝ → ℝ) (T : ℝ≥0) (u : ℝ≥0) : ℝ := k (min (u:ℝ) T)

theorem clampedWeight_continuous {k : ℝ → ℝ} {T : ℝ≥0}
    (hk : ContinuousOn k (Icc 0 (T:ℝ))) : Continuous (clampedWeight k T) :=
  hk.comp_continuous (NNReal.continuous_coe.min continuous_const)
    (fun u => ⟨le_min u.coe_nonneg T.coe_nonneg,min_le_right _ _⟩)

@[expose] def cutWeight (k : ℝ → ℝ) (T : ℝ≥0) : ℝ≥0 → ℝ :=
  (Ioc (0:ℝ≥0) T).indicator (clampedWeight k T)

theorem cutWeight_memLp {k : ℝ → ℝ} {T : ℝ≥0}
    (hk : ContinuousOn k (Icc 0 (T:ℝ))) : MemLp (cutWeight k T) 2 nonnegativeLebesgueMeasure := by
  rw [cutWeight,memLp_indicator_iff_restrict measurableSet_Ioc]
  letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0:ℝ≥0) T)) :=
    ⟨by rw [Measure.restrict_apply_univ];exact lt_top_iff_ne_top.mpr (nonnegativeLebesgueMeasure_Ioc_ne_top 0 T)⟩
  obtain ⟨C,hC⟩ := isCompact_Icc.bddAbove_image (clampedWeight_continuous hk).norm.continuousOn
    (K:=Icc (0:ℝ≥0) T)
  apply MemLp.of_bound ((clampedWeight_continuous hk).aestronglyMeasurable) C
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  exact hC ⟨u,⟨hu.1.le,hu.2⟩,rfl⟩

@[expose] def weight (k : ℝ → ℝ) (T : ℝ≥0) (hk : ContinuousOn k (Icc 0 (T:ℝ))) : TimeL2 :=
  (cutWeight_memLp hk).toLp (cutWeight k T)

theorem weight_coe {k : ℝ → ℝ} {T : ℝ≥0} (hk : ContinuousOn k (Icc 0 (T:ℝ))) :
    (weight k T hk : ℝ≥0 → ℝ)=ᵐ[nonnegativeLebesgueMeasure] cutWeight k T :=
  (cutWeight_memLp hk).coeFn_toLp

theorem weight_norm_sq {k : ℝ → ℝ} {T : ℝ≥0} (hk : ContinuousOn k (Icc 0 (T:ℝ))) :
    ‖weight k T hk‖^2=∫u in (0:ℝ)..(T:ℝ),(k u)^2 := by
  rw [weight,ProjectedTreeDrift.toLp_norm_sq]
  calc
    _ = ∫u in Ioc (0:ℝ≥0) T,(clampedWeight k T u)^2 ∂nonnegativeLebesgueMeasure := by
      unfold cutWeight
      rw [←integral_indicator measurableSet_Ioc]
      apply integral_congr_ae
      exact Eventually.of_forall (fun u => by
        by_cases hu : u∈Ioc (0:ℝ≥0) T
        · simp only [indicator_of_mem hu]
        · simp only [indicator_of_notMem hu,zero_pow (by decide : (2:ℕ)≠0)])
    _ = ∫u in Ioc (0:ℝ≥0) T,(k u)^2 ∂nonnegativeLebesgueMeasure := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro u hu
      dsimp only [clampedWeight]
      rw [min_eq_left (show (u:ℝ)≤T by exact_mod_cast hu.2)]
    _ = _ := nnreal_interval_integral T (fun u => (k u)^2)

theorem source_gaussian_trunk {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {k : ℝ → ℝ} {T : ℝ≥0}
    (hk : ContinuousOn k (Icc 0 (T:ℝ))) (hunit : (∫u in (0:ℝ)..(T:ℝ),(k u)^2)=1) :
    HasLaw (fun ω : Ω×Space N => vectorIntegral (weight k T hk) ω.2)
      (stdGaussian (Vector N)) (P.prod (law N)) ∧
    IndepFun (fun ω : Ω×Space N => vectorIntegral (weight k T hk) ω.2) Prod.fst (P.prod (law N)) := by
  have hn : ‖weight k T hk‖=1 := by
    have hh := weight_norm_sq hk
    rw [hunit] at hh
    nlinarith [norm_nonneg (weight k T hk)]
  exact ⟨vectorIntegral_augmented_law P _ hn,vectorIntegral_independent P _⟩

end SphericalAging.WienerTrunkWeight
