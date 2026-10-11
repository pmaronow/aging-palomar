module

public import SphericalAging.StrongResponseConsequences
public import SphericalAging.ThermalRowConvergence

public section

/-! Actual old-row squared response vanishes along arbitrary diverging lags.
The input is the preceding genuine whole half-line L2 row convergence. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.OldResponseL2
open CKSpecification GreenCovariance WhitePrefixResponse BackwardRowL2 BackwardRowResidual
open StrongResponseConsequences ThermalRowConvergence

theorem old_response_square_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    {L t : ℝ} (hL : 0≤L) (hLt : L≤t) :
    remoteTail d t L≤2*(rowError d r t)^2+2*(∫v in Ioi L,(r v)^2) := by
  let μ : Measure ℝ := volume.restrict (Ioi L)
  have hμ : μ≤rayMeasure := Measure.restrict_mono (Ioi_subset_Ioi hL) le_rfl
  have hf := (responseRow_memLp_two h t).mono_measure hμ
  have hrμ := hr.mono_measure hμ
  let F : Lp ℝ 2 μ := hf.toLp (responseRow d t)
  let G : Lp ℝ 2 μ := hrμ.toLp r
  have hn : ‖F‖≤rowError d r t+‖G‖ := by
    have hh := norm_le_norm_sub_add F G
    have hdiff := (responseRow_memLp_two h t).sub hr
    have hm := ENNReal.toReal_mono hdiff.eLpNorm_ne_top
      (eLpNorm_mono_measure (fun v => responseRow d t v-r v) hμ (p := 2))
    have he : ‖F-G‖=(eLpNorm (fun v => responseRow d t v-r v) 2 μ).toReal := by
      rw [←hf.toLp_sub hrμ,Lp.norm_toLp]
      rfl
    rw [he] at hh
    exact hh.trans (add_le_add hm le_rfl)
  have hF : ‖F‖^2=remoteTail d t L :=
    (ProjectedTreeDrift.toLp_norm_sq hf).trans (response_tail_row_square h hL hLt)
  have hG : ‖G‖^2=∫v in Ioi L,(r v)^2 := ProjectedTreeDrift.toLp_norm_sq hrμ
  rw [←hF,←hG]
  have he0 : 0≤rowError d r t := ENNReal.toReal_nonneg
  nlinarith [sq_nonneg (rowError d r t-‖G‖),norm_nonneg F,norm_nonneg G]

/-- Source equation geometry-old-row-l2: terminal time and lag may diverge
at arbitrary rates, provided the old integration interval is causal. -/
theorem old_response_square_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0))
    (t L : ℕ→ℝ) (ht : Tendsto t atTop atTop) (hL : Tendsto L atTop atTop)
    (hLt : ∀n,L n≤t n) :
    Tendsto (fun n => remoteTail d (t n) (L n)) atTop (𝓝 0) := by
  have htail : Tendsto (fun n => ∫v in Ioi (L n),(r v)^2) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero hL
  have he : Tendsto (fun n => 2*(rowError d r (t n))^2+
      2*(∫v in Ioi (L n),(r v)^2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,zero_add] using
      ((hrow.comp ht).pow 2).const_mul 2 |>.add (htail.const_mul 2)
  apply squeeze_zero' (Eventually.of_forall (fun n => remoteTail_nonneg d _ _)) _ he
  filter_upwards [hL.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
  exact old_response_square_bound h hr hn (hLt n)

end SphericalAging.OldResponseL2
