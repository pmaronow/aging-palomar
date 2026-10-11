module

public import SphericalAging.FisherIncrementRegularity

public section

/-! Actual CK earlier rows are absolutely continuous, including endpoints.
Their exact FTC defect is dominated by the integral of √a_F. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.CKFisherRows
open Set Filter MeasureTheory CKSpecification EarlierCovariance GreenCovariance
open StrongBackwardDefect SphereCKFisherMajorant
open scoped Topology

theorem row_increment_integral {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {u v t : ℝ} (hu : 0≤u) (huv : u≤v) (hvt : v≤t) :
    d.C t v-d.C t u=∫ s in u..v,clampedEarlierSlope p β d t s := by
  have hc : ContinuousOn (fun s => d.C t s) (Icc u v) := by
    apply ((clampedCorrelation_continuous h).comp (continuous_const.prodMk continuous_id)).continuousOn.congr
    intro s hs
    exact (clampedCorrelation_eq (hu.trans (huv.trans hvt)) (hu.trans hs.1)).symm
  have hd : Continuous (fun s => clampedEarlierSlope p β d t s) :=
    (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le huv hc (fun s hs => by
    rw [clampedEarlierSlope_eq (hu.trans hs.1.le) (hs.2.le.trans hvt)]
    exact correlation_earlier_hasDerivAt h (hu.trans_lt hs.1) (hs.2.trans_le hvt))
    (hd.intervalIntegrable u v)).symm

theorem row_absolutelyContinuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0≤t) :
    AbsolutelyContinuousOnInterval (fun s => d.C t s) 0 t := by
  have hd : Continuous (fun s => clampedEarlierSlope p β d t s) :=
    (clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)
  have hp := (hd.intervalIntegrable 0 t).absolutelyContinuousOnInterval_intervalIntegral
    (by rw [uIcc_of_le ht];exact ⟨le_rfl,ht⟩ : (0:ℝ)∈uIcc 0 t)
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => d.C t 0) 0 t :=
    (contDiff_const.contDiffOn : ContDiffOn ℝ 1 (fun _ : ℝ => d.C t 0) (uIcc 0 t)).absolutelyContinuousOnInterval
  apply (hp.add hc).congr
  intro s hs
  rw [uIcc_of_le ht] at hs
  dsimp only [Pi.add_apply]
  rw [← row_increment_integral h le_rfl hs.1 hs.2]
  ring

theorem sqrt_intervalIntegrable {a : ℝ→ℝ} (han : ∀s,0≤a s)
    (hi : IntegrableOn a (Ioi 0)) (ham : StronglyMeasurable a)
    {u v : ℝ} (hu : 0≤u) (huv : u≤v) :
    IntervalIntegrable (fun s => Real.sqrt (a s)) volume u v := by
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le huv).mpr
  have ha : IntegrableOn a (Ioc u v) := hi.mono_set fun s hs => hu.trans_lt hs.1
  have hdom : IntegrableOn (fun s => 1+a s) (Ioc u v) := (integrable_const 1).add ha
  apply hdom.mono'
    ((Real.continuous_sqrt.comp_stronglyMeasurable ham).aestronglyMeasurable)
  exact ae_of_all _ fun s => by
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith [Real.sq_sqrt (han s),Real.sqrt_nonneg (a s),han s]

theorem row_integral_sqrt_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {a : ℝ→ℝ} (ha : FisherMajorant p β d a)
    (han : ∀s,0≤a s) (ham : StronglyMeasurable a)
    {u v t : ℝ} (hu : 0≤u) (huv : u≤v) (hvt : v≤t) :
    |d.C t v-d.C t u-(∫ s in u..v,d.R t s)|≤∫ s in u..v,Real.sqrt (a s) := by
  let D : ℝ→ℝ := fun s => clampedEarlierSlope p β d t s-clampedResponse d t s
  have hD : Continuous D :=
    ((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).sub
      ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id))
  have hR : IntervalIntegrable (fun s => d.R t s) volume u v := by
    have hc : ContinuousOn (fun s => d.R t s) (Icc u v) := by
      apply ((clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)).continuousOn.congr
      intro s hs
      exact (clampedResponse_eq (hu.trans hs.1) (hs.2.trans hvt)).symm
    exact hc.intervalIntegrable_of_Icc huv
  have hsI : IntervalIntegrable (fun s => clampedEarlierSlope p β d t s) volume u v :=
    ((clampedEarlierSlope_continuous h).comp (continuous_const.prodMk continuous_id)).intervalIntegrable u v
  have he : d.C t v-d.C t u-(∫ s in u..v,d.R t s)=∫ s in u..v,D s := by
    rw [row_increment_integral h hu huv hvt]
    rw [← intervalIntegral.integral_sub hsI hR]
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le huv] at hs
    dsimp only [D]
    rw [clampedResponse_eq (hu.trans hs.1) (hs.2.trans hvt)]
  rw [he]
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo (μ := volume) huv
    (hD.abs.intervalIntegrable u v) (sqrt_intervalIntegrable han ha.integrable ham hu huv)
    (fun s hs => by
      have hh := ha.dominates t s (hu.trans_lt hs.1) (hs.2.trans_le hvt)
      change |clampedEarlierSlope p β d t s-clampedResponse d t s|≤Real.sqrt (a s)
      rw [clampedEarlierSlope_eq (hu.trans hs.1.le) (hs.2.le.trans hvt),
        clampedResponse_eq (hu.trans hs.1.le) (hs.2.le.trans hvt)]
      exact (Real.le_sqrt (abs_nonneg _) (han s)).mpr (by simpa only [sq_abs,backwardDefect] using hh))
  exact (intervalIntegral.abs_integral_le_integral_abs huv).trans hb

end SphericalAging.CKFisherRows
