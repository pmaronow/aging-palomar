module

public import SphericalAging.MixedHessianSourceContinuity
public import SphericalAging.LpFourProductBounds

public section

/-! True spatial continuity of the cubic first-response source, using
four actual eighth moments and fourth-moment first-response differences. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.CubicSourceContinuity
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open FlowVariationEighthMoment FlowLinearizationLpBounds SecondVariationTimeFourthBounds
open LpThreeProductBounds LpProductBounds LpFourProductBounds ThirdVariationPointwiseError
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N→L[ℝ] ℝ) := inferInstance

theorem cubic_difference_bound {g : State N→ℝ} {M A : ℝ≥0}
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g))))
    (x y ux uy vx vy wx wy : State N) :
    ‖fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y uy vy wy-
      fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x ux vx wx‖≤
      (A:ℝ)*‖y-x‖*‖uy‖*‖vy‖*‖wy‖+
      (M:ℝ)*‖uy-ux‖*‖vy‖*‖wy‖+
      (M:ℝ)*‖vy-vx‖*‖ux‖*‖wy‖+
      (M:ℝ)*‖wy-wx‖*‖ux‖*‖vx‖ := by
  let H := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) x
  let B := fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y-H
  have hH : ‖H‖≤(M:ℝ) := norm_fderiv_le_of_lipschitz ℝ hM
  have hB : ‖B‖≤(A:ℝ)*‖y-x‖ := by simpa only [B,H,dist_eq_norm] using hA.dist_le_mul y x
  have he : fderiv ℝ (fderiv ℝ (fderiv ℝ g)) y uy vy wy-H ux vx wx=
      B uy vy wy+H (uy-ux) vy wy+H ux (vy-vx) wy+H ux vx (wy-wx) := by
    dsimp [B];simp only [map_sub,ContinuousLinearMap.sub_apply];ring
  rw [he]
  have ht : ‖B uy vy wy+H (uy-ux) vy wy+H ux (vy-vx) wy+H ux vx (wy-wx)‖≤
      ‖B uy vy wy‖+‖H (uy-ux) vy wy‖+‖H ux (vy-vx) wy‖+‖H ux vx (wy-wx)‖ := by
    exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (norm_add_le _ _) (le_refl _))) (le_refl _))
  exact ht.trans (add_le_add (add_le_add (add_le_add
    (by simpa only [mul_assoc] using trilinear_bound B hB uy vy wy)
    (trilinear_bound H hH (uy-ux) vy wy))
    (by convert trilinear_bound H hH ux (vy-vx) wy using 1 <;> ring))
    (by convert trilinear_bound H hH ux vx (wy-wx) using 1 <;> ring))

section Flow
variable (D : BrownianDriver N P F) {Kb Ks M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[F 0] S)
  (x y : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
  (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g)))
  (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ (fderiv ℝ g)))) (u v w : State N)

include hA in
 theorem source_difference_bound : ∀ᵐq∂nonnegativeLebesgueMeasure.prod P,
    ‖((ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull y T g hg hM u v w-
      ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull x T g hg hM u v w :
        PredictableProcessL2 F P) : TimeProcessL2 P) q‖≤
    (A:ℝ)*‖stateTimeCut (increment D hb hs x y T) T q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T u) T q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T q‖+
    (M:ℝ)*‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T u q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T q‖+
    (M:ℝ)*‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T q‖+
    (M:ℝ)*‖FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T q‖*
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T q‖ := by
  let S := fun z => ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull z T g hg hM u v w
  filter_upwards [Lp.coeFn_sub (S y : TimeProcessL2 P) (S x),
    ThirdVariationalSources.cubicSource_coe D hbg hsg hb hs hnull y T g hg hM u v w,
    ThirdVariationalSources.cubicSource_coe D hbg hsg hb hs hnull x T g hg hM u v w] with q he hy hx
  change ‖((S y : TimeProcessL2 P)-(S x : TimeProcessL2 P)) q‖≤_
  rw [he,Pi.sub_apply,hy,hx]
  by_cases ht : q.1∈Ioc (0:ℝ≥0) T
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,ThirdVariationalSources.cubicField,
      CubicVariationalSource.cubicField,stateTimeCut,increment,FirstVariationDifferenceLpBounds.differenceCut,ht,ite_true]
    exact cubic_difference_bound hM hA _ _ _ _ _ _ _ _
  · simp only [FourPapersCommon.continuousAdaptedTimeCut,stateTimeCut,
      FirstVariationDifferenceLpBounds.differenceCut,ht,ite_false,sub_self,norm_zero,mul_zero,zero_mul,zero_add,le_refl]

include hA in
 theorem source_difference_norm_le
    (hI : MemLp (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hDU : MemLp (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T u) 4 (nonnegativeLebesgueMeasure.prod P))
    (hDV : MemLp (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v) 4 (nonnegativeLebesgueMeasure.prod P))
    (hDW : MemLp (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w) 4 (nonnegativeLebesgueMeasure.prod P)) :
    ‖ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull y T g hg hM u v w-
      ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull x T g hg hM u v w‖≤
    (A:ℝ)*lpNorm (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T u) T) 8 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 8 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8 (nonnegativeLebesgueMeasure.prod P)+
    (M:ℝ)*lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T u) 4 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T) 8 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8 (nonnegativeLebesgueMeasure.prod P)+
    (M:ℝ)*lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v) 4 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T) 8 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T) 8 (nonnegativeLebesgueMeasure.prod P)+
    (M:ℝ)*lpNorm (FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w) 4 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T) 8 (nonnegativeLebesgueMeasure.prod P)*
      lpNorm (stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T) 8 (nonnegativeLebesgueMeasure.prod P) := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let I := stateTimeCut (increment D hb hs x y T) T
  let U := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T u) T
  let V := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T v) T
  let W := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs y T w) T
  let X := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T u) T
  let Y := stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T v) T
  let DU := FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T u
  let DV := FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T v
  let DW := FirstVariationDifferenceLpBounds.differenceCut D hbg hsg hb hs x y T w
  let R := ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull y T g hg hM u v w-
    ThirdVariationalSources.cubicSource D hbg hsg hb hs hnull x T g hg hM u v w
  let A₁ : ℝ≥0×Ω→ℝ := fun q => (A:ℝ)*(‖I q‖*‖U q‖*‖V q‖*‖W q‖)
  let A₂ : ℝ≥0×Ω→ℝ := fun q => (M:ℝ)*(‖DU q‖*‖V q‖*‖W q‖)
  let A₃ : ℝ≥0×Ω→ℝ := fun q => (M:ℝ)*(‖DV q‖*‖X q‖*‖W q‖)
  let A₄ : ℝ≥0×Ω→ℝ := fun q => (M:ℝ)*(‖DW q‖*‖X q‖*‖Y q‖)
  have hU := (first_variation_time_eighthMoment D hbg hsg hb hs y T hnull u).1
  have hV := (first_variation_time_eighthMoment D hbg hsg hb hs y T hnull v).1
  have hW := (first_variation_time_eighthMoment D hbg hsg hb hs y T hnull w).1
  have hX := (first_variation_time_eighthMoment D hbg hsg hb hs x T hnull u).1
  have hY := (first_variation_time_eighthMoment D hbg hsg hb hs x T hnull v).1
  have hVW : MemLp (fun q => ‖V q‖*‖W q‖) 4 μ := hV.norm.fun_mul hW.norm
  have hXW : MemLp (fun q => ‖X q‖*‖W q‖) 4 μ := hX.norm.fun_mul hW.norm
  have hXY : MemLp (fun q => ‖X q‖*‖Y q‖) 4 μ := hX.norm.fun_mul hY.norm
  have h₁ : MemLp A₁ 2 μ := (four_memLp hI hU hV hW).const_mul A
  have h₂ : MemLp A₂ 2 μ := by simpa only [A₂,mul_assoc] using (hDU.norm.fun_mul hVW).const_mul M
  have h₃ : MemLp A₃ 2 μ := by simpa only [A₃,mul_assoc] using (hDV.norm.fun_mul hXW).const_mul M
  have h₄ : MemLp A₄ 2 μ := by simpa only [A₄,mul_assoc] using (hDW.norm.fun_mul hXY).const_mul M
  have hn := lpNorm_dominated_sum_le (R : TimeProcessL2 P) (A₁+A₂) A₃ A₄ (Lp.memLp _) (h₁.add h₂) h₃ h₄
    (fun q => by dsimp [A₁,A₂,A₃,A₄];positivity)
    (by simpa only [A₁,A₂,A₃,A₄,Pi.add_apply,mul_assoc] using source_difference_bound D hbg hsg hb hs hnull x y T g hg hM hA u v w)
  have hn₁ : lpNorm A₁ 2 μ≤(A:ℝ)*lpNorm I 8 μ*lpNorm U 8 μ*lpNorm V 8 μ*lpNorm W 8 μ := by
    dsimp [A₁];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg A.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_four_product_le hI hU hV hW) A.coe_nonneg
  have hn₂ : lpNorm A₂ 2 μ≤(M:ℝ)*lpNorm DU 4 μ*lpNorm V 8 μ*lpNorm W 8 μ := by
    dsimp [A₂];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hDU hV hW) M.coe_nonneg
  have hn₃ : lpNorm A₃ 2 μ≤(M:ℝ)*lpNorm DV 4 μ*lpNorm X 8 μ*lpNorm W 8 μ := by
    dsimp [A₃];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hDV hX hW) M.coe_nonneg
  have hn₄ : lpNorm A₄ 2 μ≤(M:ℝ)*lpNorm DW 4 μ*lpNorm X 8 μ*lpNorm Y 8 μ := by
    dsimp [A₄];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_triple_le hDW hX hY) M.coe_nonneg
  change ‖(R : TimeProcessL2 P)‖≤_
  rw [Lp.norm_def]
  exact hn.trans (add_le_add (add_le_add ((lpNorm_add_le h₁ (by norm_num)).trans (add_le_add hn₁ hn₂)) hn₃) hn₄)
end Flow

end SphericalAging.CubicSourceContinuity
