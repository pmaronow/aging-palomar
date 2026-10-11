module

public import SphericalAging.CKUniformLateEstimates
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

public section

/-! The genuine Fisher squared increment estimate yields local absolute
continuity and the almost-everywhere derivative estimate. Local boundedness
of the constructed Fisher clock is the only additional analytic property. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.FisherIncrementRegularity
open Set Filter MeasureTheory CKUniformLateEstimates
open scoped Topology NNReal

theorem ordered_increment_bound {a f : ℝ→ℝ} {B M T u v : ℝ}
    (hc : IncrementControl a f B) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B) (hM : 0≤M)
    (hb : ∀s∈Icc 0 T,a s≤M) (hu : 0≤u) (huv : u≤v) (hvT : v≤T) :
    |f v-f u|≤(B*Real.sqrt M)*(v-u) := by
  have hAI : IntervalIntegrable a volume u v :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr
      (hi.mono_set fun s hs => hu.trans_lt hs.1)
  have hInt := intervalIntegral.integral_mono_on (μ := volume) huv hAI
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) volume u v)
    (fun s hs => hb s ⟨hu.trans hs.1,hs.2.trans hvT⟩)
  rw [intervalIntegral.integral_const,smul_eq_mul] at hInt
  have hh := (hc u v hu huv).trans
    (mul_le_mul_of_nonneg_left hInt (mul_nonneg (sq_nonneg B) (sub_nonneg.mpr huv)))
  have hs := Real.sq_sqrt hM
  have hp : 0≤(B*Real.sqrt M)*(v-u) :=
    mul_nonneg (mul_nonneg hB (Real.sqrt_nonneg _)) (sub_nonneg.mpr huv)
  have he : (B*Real.sqrt M*(v-u))^2=B^2*(v-u)*((v-u)*M) := by
    rw [mul_pow,mul_pow,hs]
    ring
  rw [← he] at hh
  exact (sq_le_sq₀ (abs_nonneg _) hp).mp (by simpa only [sq_abs] using hh)

theorem absolutelyContinuous_of_increment_control {a f : ℝ→ℝ} {B T : ℝ}
    (hc : IncrementControl a f B) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B) (hT : 0≤T)
    (hb : ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M) :
    AbsolutelyContinuousOnInterval f 0 T := by
  obtain ⟨M,hM,hbound⟩ := hb
  let K : ℝ≥0 := ⟨B*Real.sqrt M,mul_nonneg hB (Real.sqrt_nonneg _)⟩
  have hLip : LipschitzOnWith K f (uIcc 0 T) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    change dist (f x) (f y)≤(B*Real.sqrt M)*dist x y
    rw [uIcc_of_le hT] at hx hy
    rcases le_total y x with hyx | hxy
    · simpa only [Real.dist_eq,abs_of_nonneg (sub_nonneg.mpr hyx)] using
        ordered_increment_bound hc hi hB hM hbound hy.1 hyx hx.2
    · have hh := ordered_increment_bound hc hi hB hM hbound hx.1 hxy hy.2
      simpa only [Real.dist_eq,abs_sub_comm (f x) (f y),abs_sub_comm x y,
        abs_of_nonneg (sub_nonneg.mpr hxy)] using hh
  exact hLip.absolutelyContinuousOnInterval

theorem derivative_square_le_of_increment_control {a f : ℝ→ℝ} {B s : ℝ}
    (hc : IncrementControl a f B) (ham : StronglyMeasurable a)
    (hac : ContinuousWithinAt a (Ici s) s) (hs : 0≤s) (hd : DifferentiableAt ℝ f s) :
    (deriv f s)^2≤B^2*a s := by
  have hm : StronglyMeasurable (fun u => B^2*a u) := stronglyMeasurable_const.mul ham
  have hfc : ContinuousWithinAt (fun u => B^2*a u) (Ici s) s := continuousWithinAt_const.mul hac
  apply FisherIntervalTransfer.derivative_square_le_of_interval_bound
    (show s<s+1 by linarith) hd.hasDerivAt hm hfc
  intro v hsv _
  rw [intervalIntegral.integral_const_mul]
  convert hc s v hs hsv.le using 1 <;> ring

theorem ae_derivative_bound_of_increment_control {a f : ℝ→ℝ} {B : ℝ}
    (hc : IncrementControl a f B) (hi : IntegrableOn a (Ioi 0)) (hB : 0≤B)
    (hb : ∀T : ℝ,0≤T → ∃M : ℝ,0≤M ∧ ∀s∈Icc 0 T,a s≤M)
    (ham : StronglyMeasurable a) (hac : ∀s,ContinuousWithinAt a (Ici s) s) :
    (∀T : ℝ,0≤T → AbsolutelyContinuousOnInterval f 0 T) ∧
      (∀ᵐ s ∂volume.restrict (Ioi 0),DifferentiableAt ℝ f s ∧ (deriv f s)^2≤B^2*a s) := by
  have hAC T hT := absolutelyContinuous_of_increment_control hc hi hB hT (hb T hT)
  have hdiff : ∀ᵐ s ∂volume,∀n : ℕ,s∈uIcc (0:ℝ) ((n:ℝ)+1) → DifferentiableAt ℝ f s := by
    apply ae_all_iff.mpr
    intro n
    exact (hAC ((n:ℝ)+1) (by positivity)).ae_differentiableAt
  refine ⟨hAC,?_⟩
  filter_upwards [ae_restrict_of_ae hdiff,ae_restrict_mem measurableSet_Ioi] with s hs hs0
  obtain ⟨n,hn⟩ := exists_nat_gt s
  have hd := hs n (by rw [uIcc_of_le (by positivity : (0:ℝ)≤(n:ℝ)+1)];exact ⟨hs0.le,by linarith⟩)
  exact ⟨hd,derivative_square_le_of_increment_control hc ham (hac s) hs0.le hd⟩

end SphericalAging.FisherIncrementRegularity
