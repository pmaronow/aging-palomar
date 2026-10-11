module

public import SphericalAging.ThirdCoefficientSourceError

public section

/-! Literal L² bound for the actual third coefficient forcing error. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdCoefficientSourceNorm
open HardSphereDynamics LocalSDE LinearSDETimeFourthMoment NonlinearIncrementFourthMoment
open ThirdCoefficientSourceError LpProductBounds LpThreeProductBounds
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem sourceError_norm_le (D : BrownianDriver N P F) {Kb Ks Lb Ls K L M : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[F 0] S)
    (x y : State N) (T : ℝ≥0) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (u v : State N)
    (hI : MemLp (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P))
    (hE : MemLp (FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T) 4
      (nonnegativeLebesgueMeasure.prod P)) :
    ‖sourceError D hbg hsg hb hs hbd hsd hnull x y T g hg hK hL u v‖≤
      (M:ℝ)*(lpNorm (stateTimeCut (increment D hb hs x y T) T) 8 (nonnegativeLebesgueMeasure.prod P))^2*
        lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4
          (nonnegativeLebesgueMeasure.prod P)+
      (L:ℝ)*lpNorm (FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T) 4
        (nonnegativeLebesgueMeasure.prod P)*
        lpNorm (stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T) 4
          (nonnegativeLebesgueMeasure.prod P)+
      (L:ℝ)*lpNorm (fun q =>
        ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
        ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖) 2
          (nonnegativeLebesgueMeasure.prod P) := by
  let μ := nonnegativeLebesgueMeasure.prod P
  let I := stateTimeCut (increment D hb hs x y T) T
  let E := FlowLinearizationLpBounds.remainderCut D hbg hsg hb hs x y T
  let Y := stateTimeCut (SecondVariationalSDE.process D hbg hsg hb hs hbd hsd hnull y T u v) T
  let A : ℝ≥0×Ω→ℝ := fun q => (M:ℝ)*(‖I q‖^2*‖Y q‖)
  let B : ℝ≥0×Ω→ℝ := fun q => (L:ℝ)*(‖E q‖*‖Y q‖)
  let C : ℝ≥0×Ω→ℝ := fun q => (L:ℝ)*(
    ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
    ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖)
  let R := sourceError D hbg hsg hb hs hbd hsd hnull x y T g hg hK hL u v
  have hY := SecondVariationFourthMoment.process_time_memLp_fourth D hbg hsg hb hs hbd hsd hnull y T u v
  have hA : MemLp A 2 μ := ((squared_memLp_four hI).fun_mul hY.norm).const_mul M
  have hB : MemLp B 2 μ := (hE.norm.fun_mul hY.norm).const_mul L
  have hD := (ConstructedFirstVariation.process_time_fourthMoment D hbg hsg hb hs x T hnull (y-x)).1
  have hQ := SecondResponseDifferenceLpBounds.differenceCut_memLp_four D hbg hsg hb hs hbd hsd hnull x y T u v
  have hC : MemLp C 2 μ := (hD.norm.fun_mul hQ.norm).const_mul L
  have hn := lpNorm_dominated_sum_le (R : TimeProcessL2 P) A B C (Lp.memLp _) hA hB hC
    (fun q => by dsimp [A,B,C];positivity)
    (by simpa only [A,B,C,mul_assoc] using sourceError_bound D hbg hsg hb hs hbd hsd hnull x y T g hg hK hL u v hM)
  have hnA : lpNorm A 2 μ≤(M:ℝ)*(lpNorm I 8 μ)^2*lpNorm Y 4 μ := by
    dsimp [A];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_squared_product_le hI hY) M.coe_nonneg
  have hnB : lpNorm B 2 μ≤(L:ℝ)*lpNorm E 4 μ*lpNorm Y 4 μ := by
    dsimp [B];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg L.coe_nonneg]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hE hY) L.coe_nonneg
  have hnC : lpNorm C 2 μ=(L:ℝ)*lpNorm (fun q =>
      ‖stateTimeCut (ConstructedFirstVariation.process D hbg hsg hb hs x T (y-x)) T q‖*
      ‖SecondResponseDifferenceLpBounds.differenceCut D hbg hsg hb hs hbd hsd hnull x y T u v q‖) 2 μ := by
    dsimp [C];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg L.coe_nonneg]
  change ‖(R : TimeProcessL2 P)‖≤_
  rw [Lp.norm_def]
  exact hn.trans (add_le_add (add_le_add hnA hnB) hnC.le)

end SphericalAging.ThirdCoefficientSourceNorm
