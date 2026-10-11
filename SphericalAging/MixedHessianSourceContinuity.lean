module

public import SphericalAging.SecondResponseDifferenceLpBounds
public import SphericalAging.HessianThirdSourceLittleO

public section

/-! Actual mixed Hessian/second-response forcing is spatially continuous
in L². The second-response difference is paired with its fixed first
response through the proved truncation argument. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.MixedHessianSourceContinuity
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FlowVariationEighthMoment FlowLinearizationLpBounds SecondVariationTimeFourthBounds
open LpThreeProductBounds LpProductBounds
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
section Flow
variable (D : BrownianDriver N P F) {Kb Ks Lb Ls L M : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
  (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
  (hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[F 0] S)
  (x y : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hL : LipschitzWith L (fderiv ℝ g)) (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
  (u v w : State N)

 include hM in
 theorem source_difference_bound :
    ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
      ‖((ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull y T g hg hL u v w-
        ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w :
          PredictableProcessL2 F P) : TimeProcessL2 P) q‖≤
      (M:ℝ)*‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T q‖*
        ‖stateTimeCut (increment D hb hs x y T) T q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T q‖+
      (L:ℝ)*‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w q‖*
        ‖stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T q‖+
      (L:ℝ)*‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T w) T q‖ := by
  let S := fun z => ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull z T g hg hL u v w
  filter_upwards [Lp.coeFn_sub (S y : TimeProcessL2 P) (S x),
    ThirdVariationalSources.mixedSource_coe D hbg hsg hb hs hbd hsd hnull y T g hg hL u v w,
    ThirdVariationalSources.mixedSource_coe D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w]
    with q he hy hx
  change ‖((S y : TimeProcessL2 P)-(S x : TimeProcessL2 P)) q‖≤_
  rw [he,Pi.sub_apply,hy,hx]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ThirdVariationalSources.mixedField,
      HessianQuadraticSource.hessianField,stateTimeCut,increment,
      FirstVariationDifferenceLpBounds.differenceCut,SecondResponseDifferenceLpBounds.differenceCut,ht,ite_true]
    rw [((hg.contDiffAt (x:=GlobalSDE.horizonProcess D hb hs y T q.1 q.2)).isSymmSndFDerivAt (by simp)).eq
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs y T w q.1 q.2),
      ((hg.contDiffAt (x:=GlobalSDE.horizonProcess D hb hs x T q.1 q.2)).isSymmSndFDerivAt (by simp)).eq
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T w q.1 q.2)]
    have hh := HessianSourceDifference.hessian_difference_bound hL hM
      (GlobalSDE.horizonProcess D hb hs x T q.1 q.2) (GlobalSDE.horizonProcess D hb hs y T q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs y T w q.1 q.2)
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v q.1 q.2)
      (ConstructedFirstVariation.process D hbg hsg hb hs x T w q.1 q.2)
      (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull x T u v q.1 q.2)
    convert hh using 1 <;> ring
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,
      FirstVariationDifferenceLpBounds.differenceCut,SecondResponseDifferenceLpBounds.differenceCut,
      ht,ite_false,sub_self,norm_zero,mul_zero,zero_mul,zero_add,le_refl]

 include hM in
 theorem source_difference_norm_le
    (hI : MemLp (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hDY : MemLp (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w) 4
      (nonnegativeLebesgueMeasure.prod P)) :
    ‖ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull y T g hg hL u v w-
      ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w‖≤
      (M:ℝ)*lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4
        (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8
          (nonnegativeLebesgueMeasure.prod P)+
      (L:ℝ)*lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w) 4
        (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4
          (nonnegativeLebesgueMeasure.prod P)+
      (L:ℝ)*lpNorm (fun q =>
        ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖*
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T w) T q‖) 2
          (nonnegativeLebesgueMeasure.prod P) := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let Q := stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T
  let I := stateTimeCut (increment D hb hs x y T) T
  let Y := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T
  let DY := FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w
  let DQ := SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v
  let X := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T w) T
  let R := ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull y T g hg hL u v w-
    ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w
  let A : ℝ≥0×Ω→ℝ := fun q => (M:ℝ)*(‖Q q‖*‖I q‖*‖Y q‖)
  let B : ℝ≥0×Ω→ℝ := fun q => (L:ℝ)*(‖DY q‖*‖Q q‖)
  let C : ℝ≥0×Ω→ℝ := fun q => (L:ℝ)*(‖DQ q‖*‖X q‖)
  have hQ := SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull y T u v
  have hY := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull w
  have hX := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull w).1
  have hDQ := SecondResponseDifferenceLpBounds.differenceCut_memLp_four D hbg hsg hb hs hbd hsd hnull x y T u v
  have hIY : MemLp (fun q => ‖I q‖*‖Y q‖) 4 μ := hI.norm.fun_mul hY.1.norm
  have hA : MemLp A 2 μ := by simpa only [A,mul_assoc] using (hQ.norm.fun_mul hIY).const_mul M
  have hB : MemLp B 2 μ := (hDY.norm.fun_mul hQ.norm).const_mul L
  have hC : MemLp C 2 μ := (hDQ.norm.fun_mul hX.norm).const_mul L
  have hn := lpNorm_dominated_sum_le (R : TimeProcessL2 P) A B C (Lp.memLp _) hA hB hC
    (fun q => by dsimp [A,B,C];positivity)
    (by simpa only [A,B,C,mul_assoc] using source_difference_bound D hbg hsg hb hs hbd hsd hnull x y T g hg hL hM u v w)
  have hnA : lpNorm A 2 μ≤(M:ℝ)*lpNorm Q 4 μ*lpNorm I 8 μ*lpNorm Y 8 μ := by
    dsimp [A];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hQ hI hY.1) M.coe_nonneg
  have hnB : lpNorm B 2 μ≤(L:ℝ)*lpNorm DY 4 μ*lpNorm Q 4 μ := by
    dsimp [B];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg L.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hDY hQ) L.coe_nonneg
  have hnC : lpNorm C 2 μ=(L:ℝ)*lpNorm (fun q => ‖DQ q‖*‖X q‖) 2 μ := by
    dsimp [C];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg L.coe_nonneg]
  change ‖(R : TimeProcessL2 P)‖≤_
  rw [Lp.norm_def]
  exact hn.trans (add_le_add (add_le_add hnA hnB) hnC.le)
end Flow

 theorem mixedSource_continuous (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms L M : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hL : LipschitzWith L (fderiv ℝ g)) (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (u v w : State N) : Continuous (fun x => ThirdVariationalSources.mixedSource (NullAugmentation.driver D₀)
      hbg hsg hb hs hbd hsd (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x T g hg hL u v w) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let μ := nonnegativeLebesgueMeasure.prod P
  let Z := eighthNormConstant N Kb Ks T
  let E := normCeiling N Kb Ks Lb Ls T
  have hZ : 0≤Z := Real.rpow_nonneg (eighthConstant_nonneg N Kb Ks T) _
  have hE : 0≤E := Real.rpow_nonneg (mul_nonneg T.coe_nonneg
    (SecondVariationFourthBounds.momentCeiling_nonneg N Kb Ks Lb Ls T)) _
  let C := ((M:ℝ)*E*Z^2+(L:ℝ)*E^2)*‖u‖*‖v‖*‖w‖
  rw [continuous_iff_continuousAt]
  intro x
  let σ := fun y => lpNorm (fun q =>
    ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖*
    ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T w) T q‖) 2 μ
  have hσ : Tendsto σ (𝓝 x) (𝓝 0) := SecondResponseDifferenceLpBounds.actual_mixed_difference_tendsto D₀ hbg hsg hb hs
    hbd hsd hbd2 hsd2 x T hT u v _ (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull w).1
  have hbound (y : State N) :
      ‖ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull y T g hg hL u v w-
        ThirdVariationalSources.mixedSource D hbg hsg hb hs hbd hsd hnull x T g hg hL u v w‖≤C*‖y-x‖+(L:ℝ)*σ y := by
    have hI := increment_time_eighthMoment D₀ hbg hsg hb hs x y T hT
    have hY := first_variation_time_eighthMoment D hbg hsg hb hs y T hnull w
    have hDY := FirstVariationFourthLipschitz.difference_four_linear_bound D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x y T hT w
    have hIn := LpMomentBounds.lpNorm_eight_le_of_moment hI.1 (eighthConstant_nonneg N Kb Ks T) hI.2
    have hYn := LpMomentBounds.lpNorm_eight_le_of_moment hY.1 (eighthConstant_nonneg N Kb Ks T) hY.2
    have hQn : lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4 μ≤E*‖u‖*‖v‖ := by
      have he := SecondVariationalSDE.process_timeCut D hbg hsg hb hs hbd hsd hnull y T u v
      have hb' := responseClass_lpNorm_four_le D hbg hsg hb hs hbd hsd hnull y T u v
      simpa only [μ,E,lpNorm,eLpNorm_congr_ae he] using hb'
    have hn := source_difference_norm_le D hbg hsg hb hs hbd hsd hnull x y T g hg hL hM u v w hI.1 hDY.1
    have hc : (M:ℝ)*lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4 μ*
        lpNorm (stateTimeCut (increment D hb hs x y T) T) 8 μ*
        lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8 μ+
      (L:ℝ)*lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w) 4 μ*
        lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4 μ≤C*‖y-x‖ := by
      calc
        _≤(M:ℝ)*(E*‖u‖*‖v‖)*(Z*‖y-x‖)*(Z*‖w‖)+(L:ℝ)*(E*‖y-x‖*‖w‖)*(E*‖u‖*‖v‖) := by
          gcongr <;> first | exact lpNorm_nonneg | exact hQn | exact hIn | exact hYn | exact hDY.2
        _=_ := by dsimp [C];ring
    exact hn.trans (add_le_add hc (le_refl _))
  have hn : Tendsto (fun y : State N => ‖y-x‖) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : State N => ‖y-x‖) := (continuous_id.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto x
  have ht : Tendsto (fun y => C*‖y-x‖+(L:ℝ)*σ y) (𝓝 x) (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hn.const_mul C).add (hσ.const_mul (L:ℝ))
  rw [ContinuousAt,tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound ht

end SphericalAging.MixedHessianSourceContinuity
