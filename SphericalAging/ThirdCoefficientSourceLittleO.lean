module

public import SphericalAging.ThirdCoefficientSourceActualBound
public import SphericalAging.ActualFirstSecondMixedBasis

public section

/-! The genuine coefficient variation contribution to the third flow
Taylor remainder is little-o in the actual predictable L² space. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.ThirdCoefficientSourceLittleO
open HardSphereDynamics LocalSDE ThirdCoefficientSourceError ActualFirstSecondMixedBasis
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem sourceError_isLittleO (D₀ : BrownianDriver N P F) {Kb Ks Lb Ls Mb Ms K L M : ℝ≥0}
    {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
    (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
    (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
    (hbd : ∀i,LipschitzWith Lb (fderiv ℝ (b i)))
    (hsd : ∀i j,LipschitzWith Ls (fderiv ℝ (s i j)))
    (hbd2 : ∀i,LipschitzWith Mb (fderiv ℝ (fderiv ℝ (b i))))
    (hsd2 : ∀i j,LipschitzWith Ms (fderiv ℝ (fderiv ℝ (s i j))))
    (x : State N) (T : ℝ≥0) (hT : 0<T) (g : State N→ℝ) (hg : ContDiff ℝ ∞ g)
    (hK : LipschitzWith K g) (hL : LipschitzWith L (fderiv ℝ g))
    (hM : LipschitzWith M (fderiv ℝ (fderiv ℝ g))) (u v : State N) :
    (fun y => sourceError (NullAugmentation.driver D₀) hbg hsg hb hs hbd hsd
      (fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz) x y T g hg hK hL u v)
        =o[𝓝 x] (fun y => y-x) := by
  let D := NullAugmentation.driver D₀
  have hnull : ∀S : Set Ω,MeasurableSet S→P S=0→MeasurableSet[NullAugmentation.augment F P 0] S :=
    fun _ hm hz => NullAugmentation.augment_null_known_zero F hm hz
  let σ := basisCeiling D hbg hsg hb hs hbd hsd hnull x T u v
  have hσ : Tendsto σ (𝓝 x) (𝓝 0) :=
    basisCeiling_tendsto D₀ hbg hsg hb hs hbd hsd hbd2 hsd2 x T hT u v
  obtain ⟨C,hC,hbound⟩ := ThirdCoefficientSourceActualBound.sourceError_actual_bound D₀ hbg hsg hb hs
    hbd hsd hbd2 hsd2 x T hT g hg hK hL hM u v
  have hn : Tendsto (fun y : State N => ‖y-x‖) (𝓝 x) (𝓝 0) := by
    have hc : Continuous (fun y : State N => ‖y-x‖) := (continuous_id.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto x
  have hsmall : Tendsto (fun y => C*‖y-x‖+(L:ℝ)*σ y) (𝓝 x) (𝓝 0) := by
    simpa only [mul_zero,zero_add] using (hn.const_mul C).add (hσ.const_mul (L:ℝ))
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  filter_upwards [hsmall.eventually (gt_mem_nhds hε)] with y hy
  have hp := mixed_norm_le_basis D hbg hsg hb hs hbd hsd hnull x T u v y
  have hh := (hbound y).trans (add_le_add (le_refl (C*‖y-x‖^2))
    (mul_le_mul_of_nonneg_left hp L.coe_nonneg))
  have he : C*‖y-x‖^2+(L:ℝ)*(‖y-x‖*σ y)=(C*‖y-x‖+(L:ℝ)*σ y)*‖y-x‖ := by ring
  rw [he] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right hy.le (norm_nonneg _))

end SphericalAging.ThirdCoefficientSourceLittleO
