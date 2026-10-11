module

public import SphericalAging.LpMultiplierTruncation
public import SphericalAging.LpProductBounds
public import Mathlib.Analysis.Normed.Operator.Asymptotics

public section

/-! A uniformly L⁴-bounded family that vanishes in L² can be multiplied
by a fixed L⁴ field with convergence in L². The underlying measure can
have infinite mass. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.LpFourthMultiplierTruncation
open LpMultiplierTruncation
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {α E U V ι : Type*} [MeasurableSpace α]
  [NormedAddCommGroup E] [NormedAddCommGroup U] [NormedAddCommGroup V]
  {μ : Measure α}

lemma tail_memLp_four {W : α→E} (hW : MemLp W 4 μ) (n : ℕ) :
    MemLp (tail W n) 4 μ := by
  have hh : AEStronglyMeasurable (tail W n) μ :=
    ((continuous_const.max (continuous_id.sub continuous_const)).comp_aestronglyMeasurable hW.aestronglyMeasurable.norm)
  apply hW.norm.of_le hh
  exact Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (tail_nonnegative W n x),abs_of_nonneg (norm_nonneg _)] using tail_le W n x)

theorem tail_lpNorm_four_tendsto {W : α→E} (hW : MemLp W 4 μ) :
    Tendsto (fun n => lpNorm (tail W n) 4 μ) atTop (𝓝 0) := by
  have hdom : Integrable (fun x => ‖W x‖^4) μ := hW.integrable_norm_pow (by norm_num)
  have hi : Tendsto (fun n => ∫x,(tail W n x)^4 ∂μ) atTop (𝓝 (0:ℝ)) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (l:=(atTop : Filter ℕ)) (μ:=μ)
      (bound:=fun x => ‖W x‖^4) (F:=fun n x => (tail W n x)^4) (f:=fun _ => (0:ℝ))
      (Eventually.of_forall (fun n => ((tail_memLp_four hW n).aestronglyMeasurable.pow 4)))
      (Eventually.of_forall (fun n => Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (tail_nonnegative W n x) 4)]
        exact pow_le_pow_left₀ (tail_nonnegative W n x) (tail_le W n x) 4))) hdom ?_
    · simpa only [integral_zero] using hh
    · exact Eventually.of_forall (fun x => by
        apply tendsto_const_nhds.congr'
        filter_upwards [tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖W x‖)] with n hn
        simp only [tail,max_eq_left (sub_nonpos.mpr hn),zero_pow (by decide : (4:ℕ)≠0)])
  have he (n : ℕ) : lpNorm (tail W n) 4 μ=(∫x,(tail W n x)^4 ∂μ)^((1:ℝ)/4) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num : (4:ℝ≥0∞)≠0) (by finiteness)
      (tail_memLp_four hW n).aestronglyMeasurable]
    norm_num only [ENNReal.toReal_ofNat,Real.rpow_ofNat,one_div]
    congr 1
    apply integral_congr_ae
    exact Eventually.of_forall (fun x => by dsimp only; rw [Real.norm_eq_abs,abs_of_nonneg (tail_nonnegative W n x)])
  have hh := (Real.continuous_rpow_const (by norm_num : 0≤(1:ℝ)/4)).tendsto (0:ℝ) |>.comp hi
  simpa only [Function.comp_def,he,Real.zero_rpow (by norm_num : (1:ℝ)/4≠0)] using hh

lemma lpNorm_norm_four {f : α→U} (hf : MemLp f 4 μ) :
    lpNorm (fun x => ‖f x‖) 4 μ=lpNorm f 4 μ := by
  simpa only [toReal_eLpNorm] using congrArg ENNReal.toReal (eLpNorm_norm f hf.aestronglyMeasurable (p:=4))

theorem quantitative_bound {W : α→E} {f : α→U} {g : α→V}
    (hW : MemLp W 4 μ) (hf2 : MemLp f 2 μ) (hf4 : MemLp f 4 μ)
    (hg : AEStronglyMeasurable g μ) {L : ℝ} (hL : 0≤L)
    (hb : ∀ᵐx∂μ,‖g x‖≤L*‖f x‖*‖W x‖) (n : ℕ) :
    MemLp g 2 μ ∧ lpNorm g 2 μ≤L*(n:ℝ)*lpNorm f 2 μ+
      L*lpNorm f 4 μ*lpNorm (tail W n) 4 μ := by
  have hG : MemLp g 2 μ := by
    apply ((hf4.norm.fun_mul hW.norm).const_mul L).of_le hg
    filter_upwards [hb] with x hx
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤L*(‖f x‖*‖W x‖)),mul_assoc] using hx
  let A : α→ℝ := fun x => L*(n:ℝ)*‖f x‖
  let B : α→ℝ := fun x => L*(‖f x‖*tail W n x)
  have hA : MemLp A 2 μ := hf2.norm.const_mul (L*n)
  have hB : MemLp B 2 μ := (hf4.norm.fun_mul (tail_memLp_four hW n)).const_mul L
  have hAB : MemLp (A+B) 2 μ := hA.add hB
  have hn : lpNorm g 2 μ≤lpNorm (A+B) 2 μ := by
    apply ENNReal.toReal_mono hAB.eLpNorm_ne_top
    apply eLpNorm_mono_ae hg
    filter_upwards [hb] with x hx
    simp only [Pi.add_apply,A,B]
    have htail := tail_nonnegative W n x
    rw [Real.norm_of_nonneg (by positivity : 0≤L*(n:ℝ)*‖f x‖+L*(‖f x‖*tail W n x))]
    have ht : ‖W x‖≤(n:ℝ)+tail W n x := by dsimp [tail]; have := le_max_right 0 (‖W x‖-(n:ℝ)); linarith
    have hh := hx.trans (mul_le_mul_of_nonneg_left ht (mul_nonneg hL (norm_nonneg _)))
    nlinarith
  apply And.intro hG (hn.trans ?_)
  apply (lpNorm_add_le hA (by norm_num)).trans
  dsimp [A,B]
  rw [lpNorm_const_mul,lpNorm_const_mul,abs_of_nonneg (by positivity : 0≤L*(n:ℝ)),abs_of_nonneg hL,lpNorm_norm hf2]
  have hp := LpProductBounds.lpNorm_product_le hf4 (tail_memLp_four hW n)
  simp only [Real.norm_of_nonneg (tail_nonnegative W n _)] at hp
  calc
    _ ≤ L*(n:ℝ)*lpNorm f 2 μ+L*(lpNorm f 4 μ*lpNorm (tail W n) 4 μ) :=
      add_le_add (le_refl _) (mul_le_mul_of_nonneg_left hp hL)
    _ = _ := by ring

theorem lpNorm_two_tendsto_zero {W : α→E} (hW : MemLp W 4 μ)
    {l : Filter ι} {f : ι→α→U} {g : ι→α→V} {L C : ℝ}
    (hL : 0≤L) (hC : 0≤C)
    (hf2 : ∀ᶠi in l,MemLp (f i) 2 μ) (hf4 : ∀ᶠi in l,MemLp (f i) 4 μ)
    (hg : ∀ᶠi in l,AEStronglyMeasurable (g i) μ)
    (hb : ∀ᶠi in l,∀ᵐx∂μ,‖g i x‖≤L*‖f i x‖*‖W x‖)
    (hfour : ∀ᶠi in l,lpNorm (f i) 4 μ≤C)
    (hzero : Tendsto (fun i => lpNorm (f i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => lpNorm (g i) 2 μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htail := (tail_lpNorm_four_tendsto hW).const_mul (L*C)
  simp only [mul_zero] at htail
  obtain ⟨n,hn⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))).exists
  have hnear := (hzero.const_mul (L*(n:ℝ))).eventually
    (gt_mem_nhds (by simpa only [mul_zero] using (show (0:ℝ)<ε/2 by positivity)))
  filter_upwards [hf2,hf4,hg,hb,hfour,hnear] with i hf2 hf4 hg hb hfour hnear
  have hh := (quantitative_bound hW hf2 hf4 hg hL hb n).2
  have hp : L*lpNorm (f i) 4 μ*lpNorm (tail W n) 4 μ≤L*C*lpNorm (tail W n) 4 μ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfour hL) lpNorm_nonneg
  rw [Real.dist_eq,sub_zero,abs_of_nonneg lpNorm_nonneg]
  linarith

/-- Quadratic L² and linear L⁴ bounds suffice for the genuine mixed
Taylor remainder, even without L⁴ differentiability of the family. -/
theorem isLittleO_of_quadratic_two_linear_four
    {X : Type*} [NormedAddCommGroup X] (x : X)
    {W : α→E} (hW : MemLp W 4 μ) {f : X→α→U} {g : X→α→V}
    {L A B : ℝ} (hL : 0≤L) (hA : 0≤A) (hB : 0≤B)
    (hf2 : ∀y,MemLp (f y) 2 μ) (hf4 : ∀y,MemLp (f y) 4 μ)
    (hg : ∀y,AEStronglyMeasurable (g y) μ)
    (hb : ∀y,∀ᵐz∂μ,‖g y z‖≤L*‖f y z‖*‖W z‖)
    (htwo : ∀y,lpNorm (f y) 2 μ≤A*‖y-x‖^2)
    (hfour : ∀y,lpNorm (f y) 4 μ≤B*‖y-x‖) :
    (fun y => lpNorm (g y) 2 μ)=o[𝓝 x] (fun y => y-x) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have htail := (tail_lpNorm_four_tendsto hW).const_mul (L*B)
  simp only [mul_zero] at htail
  obtain ⟨n,hn⟩ := (htail.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))).exists
  have hnear : ∀ᶠy in 𝓝 x,L*(n:ℝ)*A*‖y-x‖<ε/2 := by
    have hh : Tendsto (fun y : X => L*(n:ℝ)*A*‖y-x‖) (𝓝 x) (𝓝 0) := by
      have hc := (((continuous_id.sub continuous_const).norm : Continuous (fun y : X => ‖y-x‖)).const_mul (L*(n:ℝ)*A)).tendsto x
      simpa only [Pi.sub_apply,id_eq,sub_self,norm_zero,mul_zero] using hc
    exact hh.eventually (gt_mem_nhds (by positivity : (0:ℝ)<ε/2))
  filter_upwards [hnear] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg lpNorm_nonneg]
  have hh := (quantitative_bound hW (hf2 y) (hf4 y) (hg y) hL (hb y) n).2
  have hh' : lpNorm (g y) 2 μ≤
      L*(n:ℝ)*(A*‖y-x‖^2)+L*(B*‖y-x‖)*lpNorm (tail W n) 4 μ := hh.trans
    (add_le_add (mul_le_mul_of_nonneg_left (htwo y) (by positivity))
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hfour y) hL) lpNorm_nonneg))
  have he : L*(n:ℝ)*(A*‖y-x‖^2)+L*(B*‖y-x‖)*lpNorm (tail W n) 4 μ=
      (L*(n:ℝ)*A*‖y-x‖+L*B*lpNorm (tail W n) 4 μ)*‖y-x‖ := by ring
  rw [he] at hh'
  exact hh'.trans (mul_le_mul_of_nonneg_right (by linarith :
    L*(n:ℝ)*A*‖y-x‖+L*B*lpNorm (tail W n) 4 μ≤ε) (norm_nonneg _))

end SphericalAging.LpFourthMultiplierTruncation
