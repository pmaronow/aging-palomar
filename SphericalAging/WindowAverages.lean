module

public import SphericalAging.TriangleUniqueness
public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

public section

/-! Actual Hilbert window averages and the exact symmetric lag-coordinate formula. -/
noncomputable section
open scoped InnerProductSpace Topology
open Set MeasureTheory
namespace SphericalAging.WindowAverages

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem inner_integral (x : E) {f : ℝ→E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    inner ℝ x (∫ u in a..b,f u)=(∫ u in a..b,inner ℝ x (f u)) :=
  ((innerSL ℝ x).intervalIntegral_comp_comm hf).symm

theorem integral_inner (x : E) {f : ℝ→E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b) :
    inner ℝ (∫ u in a..b,f u) x=(∫ u in a..b,inner ℝ (f u) x) := by
  rw [real_inner_comm,inner_integral x hf]
  apply intervalIntegral.integral_congr
  intro u _
  exact real_inner_comm _ _

@[expose] def average (f : ℝ→E) (T D : ℝ) : E := D⁻¹ • ∫ u in (0:ℝ)..D,f (T+u)

theorem average_inner (f g : ℝ→E) (hf : Continuous f) (hg : Continuous g) (T S D : ℝ) :
    inner ℝ (average f T D) (average g S D)=
      (D⁻¹)^2*(∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,inner ℝ (f (T+u)) (g (S+v))) := by
  have hf' : IntervalIntegrable (fun u=>f (T+u)) volume 0 D :=
    (hf.comp (continuous_const.add continuous_id)).intervalIntegrable 0 D
  have hg' : IntervalIntegrable (fun v=>g (S+v)) volume 0 D :=
    (hg.comp (continuous_const.add continuous_id)).intervalIntegrable 0 D
  rw [average,average,real_inner_smul_left,real_inner_smul_right,integral_inner _ hf']
  simp_rw [inner_integral _ hg']
  simp only [inv_pow]
  ring

theorem average_norm_le_one (f : ℝ→E) {T D : ℝ} (hD : 0<D)
    (hb : ∀ u ∈ Icc 0 D,‖f (T+u)‖≤1) : ‖average f T D‖≤1 := by
  have hi : ‖∫ u in (0:ℝ)..D,f (T+u)‖≤D := by
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a:=0) (b:=D)
      (C:=1) (f:=fun u=>f (T+u)) (fun u hu=>hb u ⟨(uIoc_of_le hD.le ▸ hu).1.le,(uIoc_of_le hD.le ▸ hu).2⟩)
    simpa only [sub_zero,abs_of_pos hD,one_mul] using hh
  rw [average,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hD]
  calc
    D⁻¹*‖∫ u in (0:ℝ)..D,f (T+u)‖≤D⁻¹*D := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hD.le)
    _=1 := inv_mul_cancel₀ hD.ne'

end Hilbert

/-- Exact decomposition of a symmetric stationary correlation row. -/
theorem abs_lag_row (c : ℝ→ℝ) (hc : Continuous c) {D u : ℝ} (hu : u ∈ Icc 0 D) :
    (∫ v in (0:ℝ)..D,c |u-v|)=(∫ τ in (0:ℝ)..u,c τ)+(∫ τ in (0:ℝ)..D-u,c τ) := by
  have hf : Continuous (fun v=>c |u-v|) := hc.comp ((continuous_const.sub continuous_id).abs)
  rw [←intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable 0 u) (hf.intervalIntegrable u D)]
  congr 1
  · have hs := intervalIntegral.integral_comp_sub_left c (a:=0) (b:=u) u
    rw [sub_zero,sub_self] at hs
    calc
      (∫ v in (0:ℝ)..u,c |u-v|)=(∫ v in (0:ℝ)..u,c (u-v)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hu.1] at hv
        dsimp only
        rw [abs_of_nonneg (sub_nonneg.mpr hv.2)]
      _=_ := by simpa only [neg_neg] using hs
  · calc
      (∫ v in u..D,c |u-v|)=(∫ v in u..D,c (v-u)) := by
        apply intervalIntegral.integral_congr
        intro v hv
        rw [uIcc_of_le hu.2] at hv
        dsimp only
        rw [abs_of_nonpos (sub_nonpos.mpr hv.1),neg_sub]
      _=_ := by
        simpa only [sub_self] using intervalIntegral.integral_comp_sub_right c u (a:=u) (b:=D)

/-- The true square-to-lag reduction, derived using compact triangle Fubini. -/
theorem square_abs_lag (c : ℝ→ℝ) (hc : Continuous c) {D : ℝ} (hD : 0≤D) :
    (∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,c |u-v|)=
      2*(∫ τ in (0:ℝ)..D,(D-τ)*c τ) := by
  have hp : Continuous (fun u=>∫ τ in (0:ℝ)..u,c τ) :=
    continuous_iff_continuousAt.mpr (fun u=>
      (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 u)
        hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).continuousAt)
  calc
    _=(∫ u in (0:ℝ)..D,(∫ τ in (0:ℝ)..u,c τ)+(∫ τ in (0:ℝ)..D-u,c τ)) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le hD] at hu
      exact abs_lag_row c hc hu
    _=(∫ u in (0:ℝ)..D,∫ τ in (0:ℝ)..u,c τ)+
        (∫ u in (0:ℝ)..D,∫ τ in (0:ℝ)..D-u,c τ) :=
      intervalIntegral.integral_add (hp.intervalIntegrable 0 D)
        ((hp.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 D)
    _=2*(∫ u in (0:ℝ)..D,∫ τ in (0:ℝ)..u,c τ) := by
      have hs := intervalIntegral.integral_comp_sub_left (fun u=>∫ τ in (0:ℝ)..u,c τ)
        (a:=0) (b:=D) D
      rw [sub_zero,sub_self] at hs
      rw [hs]
      ring
    _=_ := by
      rw [TriangleUniqueness.standard_triangle_integral_swap
        (F:=fun _ τ=>c τ) (hc.comp continuous_snd) hD]
      congr 1
      apply intervalIntegral.integral_congr
      intro τ _
      simp only [intervalIntegral.integral_const,smul_eq_mul]

end SphericalAging.WindowAverages
