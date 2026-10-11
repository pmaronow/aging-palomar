module

public import SphericalAging.IntervalL2Bounds
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper

public section

/-! Actual finite-window earlier smoothing. The response strong-row convergence
and Fisher clock are explicit preceding inputs; the window estimate is proved. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.EarlierSmoothing
open CKSpecification GreenCovariance EarlierCovariance StrongBackwardDefect IntervalL2Bounds

@[expose] def responseErrorEnergy (d : CKData) (r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (d.R t u-r (t-u))^2

@[expose] def backwardErrorEnergy (p : ℕ) (β : ℝ) (d : CKData) (t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, (backwardDefect p β d t u)^2

@[expose] def responseTail (r : ℝ → ℝ) (D : ℝ) : ℝ := ∫ v in Ici D, (r v)^2

theorem subinterval_energy_bound {f : ℝ → ℝ} (hf : Continuous f)
    {a b t : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hbt : b ≤ t) :
    (∫ u in a..b, (f u)^2) ≤ ∫ u in (0 : ℝ)..t, (f u)^2 := by
  exact intervalIntegral.integral_mono_interval ha hab hbt
    (ae_of_all _ (fun _ => sq_nonneg _)) ((hf.pow 2).intervalIntegrable 0 t)

/-- The actual response profile restricted to a remote window is bounded by
its genuine squared tail integral, after the true reflection change of variable. -/
theorem profile_window_energy_bound {r : ℝ → ℝ} {D s t : ℝ}
    (hD : 0 < D) (ht : s+D ≤ t)
    (hr : IntegrableOn (fun v => (r v)^2) (Ici D)) :
    (∫ u in s-D..s, (r (t-u))^2) ≤ responseTail r D := by
  rw [intervalIntegral.integral_comp_sub_left (fun v => (r v)^2) t]
  have hab : t-s ≤ t-(s-D) := by linarith
  rw [intervalIntegral.integral_of_le hab]
  exact setIntegral_mono_set hr (ae_of_all _ (fun _ => sq_nonneg _))
    (Eventually.of_forall (fun v hv => show v ∈ Ici D from by change D ≤ v; linarith [hv.1]))

/-- Genuine finite-window estimate, in terms of actual whole-row residual
energies. Every integral and square-root bound is proved from finite L² Cauchy–Schwarz. -/
theorem earlier_window_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ → ℝ}
    (hr : ContinuousOn r (Ici 0)) {D s t : ℝ} (hD : 0 < D)
    (hs : D ≤ s) (ht : s+D ≤ t)
    (hri : IntegrableOn (fun v => (r v)^2) (Ici D)) :
    (∫ u in s-D..s, |earlierSlope p β d t u|) ≤
      Real.sqrt D*(Real.sqrt (backwardErrorEnergy p β d t)+
        Real.sqrt (responseErrorEnergy d r t)+Real.sqrt (responseTail r D)) := by
  have hs0 : 0 ≤ s := hD.le.trans hs
  have ht0 : 0 ≤ t := by linarith
  have hst : s ≤ t := by linarith
  have ha : 0 ≤ s-D := sub_nonneg.mpr hs
  have hab : s-D ≤ s := by linarith
  let rp : ℝ → ℝ := fun x => r (max 0 x)
  have hrp : Continuous rp := hr.comp_continuous (continuous_const.max continuous_id)
    (fun x => le_max_left 0 x)
  let f : ℝ → ℝ := clampedEarlierSlope p β d t
  let R : ℝ → ℝ := clampedResponse d t
  let q : ℝ → ℝ := fun u => rp (t-u)
  have hf : Continuous f := (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hR : Continuous R := (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hq : Continuous q := hrp.comp (continuous_const.sub continuous_id)
  have he1 : (∫ u in (0 : ℝ)..t, (f u-R u)^2) = backwardErrorEnergy p β d t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht0] at hu
    dsimp only [f,R,backwardErrorEnergy,backwardDefect]
    rw [clampedEarlierSlope_eq hu.1 hu.2,clampedResponse_eq hu.1 hu.2]
  have he2 : (∫ u in (0 : ℝ)..t, (R u-q u)^2) = responseErrorEnergy d r t := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht0] at hu
    dsimp only [R,q,rp,responseErrorEnergy]
    rw [clampedResponse_eq hu.1 hu.2,max_eq_right (sub_nonneg.mpr hu.2)]
  have he3 : (∫ u in s-D..s, (q u)^2) ≤ responseTail r D := by
    have hid : (∫ u in s-D..s, (q u)^2) = ∫ u in s-D..s, (r (t-u))^2 := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hab] at hu
      dsimp only [q,rp]
      rw [max_eq_right (by linarith [hu.2] : 0 ≤ t-u)]
    rw [hid]
    exact profile_window_energy_bound hD ht hri
  have hb1 := integral_abs_le_sqrt (hf.sub hR) hab
  have hb2 := integral_abs_le_sqrt (hR.sub hq) hab
  have hb3 := integral_abs_le_sqrt hq hab
  have hlen : s-(s-D)=D := by ring
  rw [hlen] at hb1 hb2 hb3
  have hi1 := (subinterval_energy_bound (hf.sub hR) ha hab hst)
  have hi2 := (subinterval_energy_bound (hR.sub hq) ha hab hst)
  simp only [Pi.sub_apply] at hi1 hi2 hb1 hb2
  rw [he1] at hi1
  rw [he2] at hi2
  have hg1 := hb1.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi1) (Real.sqrt_nonneg D))
  have hg2 := hb2.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi2) (Real.sqrt_nonneg D))
  have hg3 := hb3.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt he3) (Real.sqrt_nonneg D))
  have hit : (∫ u in s-D..s, |f u|) ≤
      (∫ u in s-D..s, |f u-R u|)+(∫ u in s-D..s, |R u-q u|)+(∫ u in s-D..s, |q u|) := by
    have hm := intervalIntegral.integral_mono_on (μ := volume) hab (hf.abs.intervalIntegrable (s-D) s)
      (((hf.sub hR).abs.add ((hR.sub hq).abs)).add hq.abs |>.intervalIntegrable (s-D) s)
      (fun u hu => by
        change |f u| ≤ |f u-R u|+|R u-q u|+|q u|
        have h1 := abs_sub_le (f u) (R u) 0
        have h2 := abs_sub_le (R u) (q u) 0
        simp only [sub_zero] at h1 h2
        linarith)
    simp only [Pi.add_apply,Pi.sub_apply] at hm
    have hi1 : IntervalIntegrable (fun u => |f u-R u|) volume (s-D) s :=
      (hf.sub hR).abs.intervalIntegrable (s-D) s
    have hi2 : IntervalIntegrable (fun u => |R u-q u|) volume (s-D) s :=
      (hR.sub hq).abs.intervalIntegrable (s-D) s
    have hi3 : IntervalIntegrable (fun u => |q u|) volume (s-D) s :=
      hq.abs.intervalIntegrable (s-D) s
    rw [intervalIntegral.integral_add (hi1.add hi2) hi3,
      intervalIntegral.integral_add hi1 hi2] at hm
    exact hm
  have hid : (∫ u in s-D..s, |earlierSlope p β d t u|) = ∫ u in s-D..s, |f u| := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    dsimp only [f]
    rw [clampedEarlierSlope_eq (ha.trans hu.1) (hu.2.trans hst)]
  rw [hid]
  nlinarith

/-- Exact source earlier-smoothing limsup estimate in uniform eventual form.
The strong response row is supplied as the preceding actual whole-row energy limit. -/
theorem earlier_smoothing {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) {r : ℝ → ℝ}
    (hr : ContinuousOn r (Ici 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (nhds 0))
    {D : ℝ} (hD : 0 < D) (hri : IntegrableOn (fun v => (r v)^2) (Ici D))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, ∀ s t : ℝ, S+D ≤ s → s+D ≤ t →
      (∫ u in s-D..s, |earlierSlope p β d t u|) ≤
        Real.sqrt D*Real.sqrt (responseTail r D)+ε := by
  have hE : Tendsto (backwardErrorEnergy p β d) atTop (nhds 0) :=
    squared_backward_defect_tendsto h hb hforget ha
  have he := ((hE.sqrt.add hrow.sqrt).const_mul (Real.sqrt D))
  simp only [Real.sqrt_zero,zero_add,mul_zero] at he
  have hsmall := he.eventually (gt_mem_nhds hε)
  obtain ⟨U,hU⟩ := eventually_atTop.mp hsmall
  filter_upwards [eventually_ge_atTop (max U 0)] with S hS
  intro s t hs ht
  have hS0 : 0 ≤ S := (le_max_right U 0).trans hS
  have hst := earlier_window_bound h hr hD (by linarith) ht hri
  have hsmallt := hU t (by linarith [le_max_left U 0])
  nlinarith

end SphericalAging.EarlierSmoothing
