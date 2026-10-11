module

public import SphericalAging.RandomLpHessianSource
public import SphericalAging.BoundedLpComposition
public import SphericalAging.LpClassInterpolationContinuity
public import SphericalAging.LpThreeProductBounds

public section

/-! True continuity of bounded random Hessian products in L². Fourth
norm convergence of the directions and bounded eighth moments give the
literal product estimates; coefficients are composed with actual L² states. -/
noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.RandomLpHessianSourceContinuity
open HardSphereDynamics RandomLpHessianSource LpClassMomentAlgebra LpThreeProductBounds LpProductBounds
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance

@[expose]  def fieldSource (H : State N→State N→L[ℝ] State N→L[ℝ] State N) (hH : Continuous H)
    (M : ℝ≥0) (hM : ∀x,‖H x‖≤M) (X U V : Lp (State N) 2 P)
    (hU : MemLp U 4 P) (hV : MemLp V 4 P) : Lp (State N) 2 P :=
  source (fun q => H (X q)) (hH.comp_aestronglyMeasurable (Lp.aestronglyMeasurable X)) M
    (.of_forall (fun q => hM (X q))) U V hU hV

lemma fieldSource_coe (H : State N→State N→L[ℝ] State N→L[ℝ] State N) (hH : Continuous H)
    (M : ℝ≥0) (hM : ∀x,‖H x‖≤M) (X U V : Lp (State N) 2 P)
    (hU : MemLp U 4 P) (hV : MemLp V 4 P) :
    fieldSource H hH M hM X U V hU hV=ᵐ[P] (fun q => H (X q) (U q) (V q)) :=
  source_coe _ _ _ _ _ _ _ _

 theorem fieldSource_tendsto (H : State N→State N→L[ℝ] State N→L[ℝ] State N)
    (hH : UniformContinuous H) (M : ℝ≥0) (hM : ∀x,‖H x‖≤M)
    {l : Filter ι} (X U V : ι→Lp (State N) 2 P) (X₀ U₀ V₀ : Lp (State N) 2 P)
    (hU : ∀i,MemLp (U i : Ω→State N) 4 P) (hV : ∀i,MemLp (V i : Ω→State N) 4 P)
    (hU₀ : MemLp (U₀ : Ω→State N) 8 P) (hV₀ : MemLp (V₀ : Ω→State N) 8 P)
    (hX : Tendsto X l (𝓝 X₀))
    (hUt : Tendsto (fun i => lpNorm (U i-U₀ : Lp (State N) 2 P) 4 P) l (𝓝 0))
    (hVt : Tendsto (fun i => lpNorm (V i-V₀ : Lp (State N) 2 P) 4 P) l (𝓝 0))
    (B : ℝ) (hB : ∀i,lpNorm (V i : Ω→State N) 4 P≤B) :
    Tendsto (fun i => fieldSource H hH.continuous M hM (X i) (U i) (V i) (hU i) (hV i)) l
      (𝓝 (fieldSource H hH.continuous M hM X₀ U₀ V₀ (hU₀.mono_exponent (by norm_num)) (hV₀.mono_exponent (by norm_num)))) := by
  let C := fun i => BoundedLpComposition.composition H hH.continuous M hM (X i)
  let C₀ := BoundedLpComposition.composition H hH.continuous M hM X₀
  let A := fun i => C i-C₀
  have hAe (i) : A i=ᵐ[P] (fun q => H (X i q)-H (X₀ q)) := by
    filter_upwards [Lp.coeFn_sub (C i) C₀,
      BoundedLpComposition.composition_coeFn H hH.continuous M hM (X i),
      BoundedLpComposition.composition_coeFn H hH.continuous M hM X₀] with q hs hy hx
    exact hs.trans (by rw [Pi.sub_apply,hy,hx])
  have hAb (i) : ∀ᵐq∂P,‖A i q‖≤2*(M:ℝ) := by
    filter_upwards [hAe i] with q he
    rw [he]
    exact (norm_sub_le _ _).trans ((add_le_add (hM _) (hM _)).trans_eq (by ring))
  have hA8 (i) : MemLp (A i) 8 P := MemLp.of_bound (Lp.aestronglyMeasurable _) _ (hAb i)
  have hAn (i) : lpNorm (A i) 8 P≤2*(M:ℝ) := by
    have hh := eLpNorm_le_of_ae_bound (p:=(8:ℝ≥0∞)) (Lp.aestronglyMeasurable (A i)) (hAb i)
    simp only [measure_univ,ENNReal.one_rpow,one_mul] at hh
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hh).trans_eq (ENNReal.toReal_ofReal (by positivity))
  have hA2 : Tendsto (fun i => ‖A i‖) l (𝓝 0) := by
    have hc := (BoundedLpComposition.composition_continuous H hH M hM).tendsto X₀ |>.comp hX
    simpa only [C,C₀,A,Function.comp_def,sub_self,norm_zero] using
      (hc.sub (tendsto_const_nhds (x:=C₀))).norm
  have hAt := LpClassInterpolationContinuity.lpNorm_four_tendsto_zero (.of_forall hA8) (.of_forall hAn) hA2
  have hU₄ : MemLp U₀ 4 P := hU₀.mono_exponent (by norm_num)
  have hV₄ : MemLp V₀ 4 P := hV₀.mono_exponent (by norm_num)
  let S := fun i => fieldSource H hH.continuous M hM (X i) (U i) (V i) (hU i) (hV i)
  let S₀ := fieldSource H hH.continuous M hM X₀ U₀ V₀ hU₄ hV₄
  have hn (i) : ‖S i-S₀‖≤(M:ℝ)*B*lpNorm (U i-U₀ : Lp (State N) 2 P) 4 P+
      (M:ℝ)*lpNorm U₀ 4 P*lpNorm (V i-V₀ : Lp (State N) 2 P) 4 P+
      lpNorm (A i) 4 P*lpNorm U₀ 8 P*lpNorm V₀ 8 P := by
    let R := (S i-S₀ : Lp (State N) 2 P)
    let DU := (U i-U₀ : Lp (State N) 2 P)
    let DV := (V i-V₀ : Lp (State N) 2 P)
    let A₁ := fun q => (M:ℝ)*(‖DU q‖*‖V i q‖)
    let A₂ := fun q => (M:ℝ)*(‖U₀ q‖*‖DV q‖)
    let A₃ := fun q => ‖A i q‖*‖U₀ q‖*‖V₀ q‖
    have hDU := memLp_sub_coe (U i) U₀ (hU i) hU₄
    have hDV := memLp_sub_coe (V i) V₀ (hV i) hV₄
    have hA₄ : MemLp (A i) 4 P := (hA8 i).mono_exponent (by norm_num)
    have h₁ : MemLp A₁ 2 P := (hDU.norm.fun_mul (hV i).norm).const_mul M
    have h₂ : MemLp A₂ 2 P := (hU₄.norm.fun_mul hDV.norm).const_mul M
    have hUV : MemLp (fun q => ‖U₀ q‖*‖V₀ q‖) 4 P := hU₀.norm.fun_mul hV₀.norm
    have h₃ : MemLp A₃ 2 P := by simpa only [A₃,mul_assoc] using hA₄.norm.fun_mul hUV
    have hb : ∀ᵐq∂P,‖R q‖≤A₁ q+A₂ q+A₃ q := by
      filter_upwards [Lp.coeFn_sub (S i) S₀,fieldSource_coe H hH.continuous M hM (X i) (U i) (V i) (hU i) (hV i),
        fieldSource_coe H hH.continuous M hM X₀ U₀ V₀ hU₄ hV₄,
        Lp.coeFn_sub (U i) U₀,Lp.coeFn_sub (V i) V₀,hAe i] with q hr hy hx hu hv ha
      change ‖(S i-S₀ : Lp (State N) 2 P) q‖≤_
      rw [hr,Pi.sub_apply,hy,hx]
      have he : H (X i q) (U i q) (V i q)-H (X₀ q) (U₀ q) (V₀ q)=
          H (X i q) (U i q-U₀ q) (V i q)+H (X i q) (U₀ q) (V i q-V₀ q)+
          (H (X i q)-H (X₀ q)) (U₀ q) (V₀ q) := by
        simp only [map_sub,ContinuousLinearMap.sub_apply];abel
      rw [he]
      apply ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) (le_refl _))).trans
      dsimp only [A₁,A₂,A₃,DU,DV]
      rw [hu,hv,Pi.sub_apply,Pi.sub_apply,ha]
      exact add_le_add (add_le_add (by simpa only [mul_assoc] using bilinear_bound (H (X i q)) (hM _) _ _)
        (by simpa only [mul_assoc] using bilinear_bound (H (X i q)) (hM _) _ _))
        (bilinear_bound (H (X i q)-H (X₀ q)) (le_refl _) _ _)
    have hsum := lpNorm_dominated_sum_le (fun q => ‖R q‖) A₁ A₂ A₃ (Lp.memLp R).norm h₁ h₂ h₃
      (fun q => by dsimp [A₁,A₂,A₃];positivity) (by simpa only [Real.norm_of_nonneg (norm_nonneg _)] using hb)
    rw [lpNorm_norm (Lp.aestronglyMeasurable R)] at hsum
    change ‖R‖≤lpNorm A₁ 2 P+lpNorm A₂ 2 P+lpNorm A₃ 2 P at hsum
    have hn₁ : lpNorm A₁ 2 P≤(M:ℝ)*B*lpNorm DU 4 P := by
      dsimp [A₁];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
      apply (mul_le_mul_of_nonneg_left (lpNorm_product_le hDU (hV i)) M.coe_nonneg).trans
      have hh := mul_le_mul_of_nonneg_left (hB i) (mul_nonneg M.coe_nonneg (lpNorm_nonneg : 0≤lpNorm DU 4 P))
      convert hh using 1 <;> ring
    have hn₂ : lpNorm A₂ 2 P≤(M:ℝ)*lpNorm U₀ 4 P*lpNorm DV 4 P := by
      dsimp [A₂];rw [LpMultiplierTruncation.lpNorm_const_mul,abs_of_nonneg M.coe_nonneg]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (lpNorm_product_le hU₄ hDV) M.coe_nonneg
    have hn₃ : lpNorm A₃ 2 P≤lpNorm (A i) 4 P*lpNorm U₀ 8 P*lpNorm V₀ 8 P := by
      have hh := lpNorm_triple_le hA₄.norm hU₀.norm hV₀.norm
      rw [lpNorm_norm hA₄.aestronglyMeasurable,lpNorm_norm hU₀.aestronglyMeasurable,
        lpNorm_norm hV₀.aestronglyMeasurable] at hh
      simpa only [A₃,Real.norm_of_nonneg (norm_nonneg _)] using hh
    exact hsum.trans (add_le_add (add_le_add hn₁ hn₂) hn₃)
  have ht : Tendsto (fun i => (M:ℝ)*B*lpNorm (U i-U₀ : Lp (State N) 2 P) 4 P+
      (M:ℝ)*lpNorm U₀ 4 P*lpNorm (V i-V₀ : Lp (State N) 2 P) 4 P+
      lpNorm (A i) 4 P*lpNorm U₀ 8 P*lpNorm V₀ 8 P) l (𝓝 0) := by
    simpa only [mul_zero,zero_mul,zero_add] using ((hUt.const_mul ((M:ℝ)*B)).add
      (hVt.const_mul ((M:ℝ)*lpNorm U₀ 4 P))).add ((hAt.mul_const (lpNorm U₀ 8 P)).mul_const (lpNorm V₀ 8 P))
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (squeeze_zero (fun _ => norm_nonneg _) hn ht)
end SphericalAging.RandomLpHessianSourceContinuity
