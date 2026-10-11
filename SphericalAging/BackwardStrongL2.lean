module

public import SphericalAging.BackwardRowResidual
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

/-! Actual strong backward-row convergence from the genuine Fisher majorant,
fixed-wait forgetting and the preceding actual response-row localization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.BackwardStrongL2
open CKSpecification EarlierCovariance GreenCovariance StrongBackwardDefect EarlierSmoothing
open BackwardRowL2 BackwardRowResidual

theorem response_full_energy_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : ContinuousOn r (Ici 0))
    (hi : IntegrableOn (fun v => (r v)^2) (Ioi 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ v : ℝ,(responseRow d t v-r v)^2 ∂rayMeasure) atTop (𝓝 0) := by
  have htail : Tendsto (fun t : ℝ => ∫ v in Ioi t,(r v)^2) atTop (𝓝 0) :=
    tendsto_integral_Ioi_zero tendsto_id
  have he := hrow.add htail
  simp only [zero_add] at he
  apply he.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  exact (response_row_residual_energy h hr hi ht).symm

/-- Every row residual really lies in L2; its squared norm vanishes by the
true triangle estimate on the actual causal derivative and response. -/
theorem backward_full_energy_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) {r : ℝ→ℝ}
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn (fun v => (r v)^2) (Ioi 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (𝓝 0)) :
    Tendsto (fun t => ∫ v : ℝ,(earlierRow p β d t v-r v)^2 ∂rayMeasure) atTop (𝓝 0) := by
  have hback : Tendsto (backwardErrorEnergy p β d) atTop (𝓝 0) :=
    squared_backward_defect_tendsto h hb hforget ha
  have hresp := response_full_energy_tendsto h hr hi hrow
  have hupper := (hback.const_mul 2).add (hresp.const_mul 2)
  simp only [mul_zero,zero_add] at hupper
  have hmr := profile_memLp_two hr hi
  apply squeeze_zero' (Eventually.of_forall (fun t => integral_nonneg (fun _ => sq_nonneg _))) _ hupper
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  have hma := earlierRow_memLp_two h t
  have hmb := responseRow_memLp_two h t
  have hleft := (memLp_two_iff_integrable_sq (hma.sub hmr).aestronglyMeasurable).mp (hma.sub hmr)
  have ha2 := (memLp_two_iff_integrable_sq (hma.sub hmb).aestronglyMeasurable).mp (hma.sub hmb)
  have hb2 := (memLp_two_iff_integrable_sq (hmb.sub hmr).aestronglyMeasurable).mp (hmb.sub hmr)
  have he := integral_mono_ae hleft ((ha2.const_mul 2).add (hb2.const_mul 2))
    (ae_of_all _ (fun v => show (earlierRow p β d t v-r v)^2≤
      2*(earlierRow p β d t v-responseRow d t v)^2+2*(responseRow d t v-r v)^2 from by
        nlinarith [sq_nonneg (earlierRow p β d t v-2*responseRow d t v+r v)]))
  simp only [Pi.add_apply] at he
  rw [integral_add (ha2.const_mul 2) (hb2.const_mul 2)] at he
  simp only [Pi.sub_apply,integral_const_mul] at he
  rw [defect_row_square ht] at he
  exact he

theorem backward_full_L2_tendsto {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) {r : ℝ→ℝ}
    (hr : ContinuousOn r (Ici 0)) (hi : IntegrableOn (fun v => (r v)^2) (Ioi 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (𝓝 0)) :
    Tendsto (fun t => (eLpNorm (fun v => earlierRow p β d t v-r v) 2 rayMeasure).toReal)
      atTop (𝓝 0) := by
  have he := (backward_full_energy_tendsto h hb hforget ha hr hi hrow).sqrt
  simp only [Real.sqrt_zero] at he
  apply he.congr
  intro t
  exact (lpNorm_two_eq_sqrt ((earlierRow_memLp_two h t).sub (profile_memLp_two hr hi))).symm

end SphericalAging.BackwardStrongL2
