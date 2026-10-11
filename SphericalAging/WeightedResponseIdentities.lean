module

public import SphericalAging.CubicQuarticThresholdInputs

public section

/-! Exact finite-age stationary weighted FDT and finite-time actual CK
weighted signed-defect identities, proved by the fundamental theorem of calculus. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.WeightedResponseIdentities
open CKSpecification CKPhysicalConsequences ProfileCenterEnergy EarlierCovariance
  StrongBackwardDefect GreenCovariance

theorem profile_weighted_mass {p : ℕ} {c r : ℝ → ℝ} {q A : ℝ}
    (hp : 1≤p) (H : Profile c r q) (hA : 0≤A) :
    (p:ℝ)*(∫ u in (0:ℝ)..A,c u^(p-1)*r u)=1-c A^p := by
  have hi : IntervalIntegrable (fun u => -(p:ℝ)*(c u^(p-1)*r u)) volume 0 A :=
    (((H.continuous_c.pow (p-1)).mul H.continuous_r).mono
      (show Icc 0 A⊆Ici 0 from fun _ hu => hu.1)).const_mul (-(p:ℝ))
      |>.intervalIntegrable_of_Icc hA
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hA
    ((H.continuous_c.pow p).mono (show Icc 0 A⊆Ici 0 from fun _ hu => hu.1))
    (fun u hu => by
      convert (H.fdt u hu.1).pow p using 1 <;> ring) hi
  simp only [intervalIntegral.integral_const_mul,Pi.pow_apply,H.initial,one_pow] at he
  linarith

theorem correlation_row_continuous {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) (ht : 0≤t) : ContinuousOn (d.C t) (Icc 0 t) := by
  apply (((clampedCorrelation_continuous h).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr)
  intro s hs
  exact (clampedCorrelation_eq ht hs.1).symm

theorem response_row_continuous {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) : ContinuousOn (d.R t) (Icc 0 t) := by
  apply (((clampedResponse_continuous h).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr)
  intro s hs
  exact (clampedResponse_eq hs.1 hs.2).symm

theorem slope_row_continuous {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) : ContinuousOn (earlierSlope p β d t) (Icc 0 t) := by
  apply (((clampedEarlierSlope_continuous h).comp
    (continuous_const.prodMk continuous_id)).continuousOn.congr)
  intro s hs
  exact (clampedEarlierSlope_eq hs.1 hs.2).symm

theorem row_power_identity {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) (ht : 0≤t) :
    (p:ℝ)*(∫ u in (0:ℝ)..t,d.C t u^(p-1)*earlierSlope p β d t u)=1-d.C t 0^p := by
  have hc := correlation_row_continuous h ht
  have hi := ((hc.pow (p-1)).mul (slope_row_continuous h)).const_mul (p:ℝ)
    |>.intervalIntegrable_of_Icc (μ:=volume) ht
  dsimp only [Pi.mul_apply,Pi.pow_apply] at hi
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht (hc.pow p)
    (fun u hu => by
      convert (correlation_earlier_hasDerivAt h hu.1 hu.2).pow p using 1 <;>
        (try simp only [Pi.mul_apply,Pi.pow_apply]) <;> ring) hi
  simp only [intervalIntegral.integral_const_mul,Pi.pow_apply,h.correlation_diagonal t ht,one_pow] at he
  exact he

theorem weighted_response_energy {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    (p:ℝ)*(∫ u in (0:ℝ)..t,d.C t u^(p-1)*d.R t u)=energy p β d t/β := by
  have he : (∫ u in (0:ℝ)..t,d.C t u^(p-1)*d.R t u)=memoryMass p d t := by
    apply intervalIntegral.integral_congr
    intro u _
    rfl
  rw [he,energy]
  field_simp [h.beta_pos.ne']

theorem weighted_defect_identity {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) (ht : 0≤t) :
    (p:ℝ)*(∫ u in (0:ℝ)..t,d.C t u^(p-1)*backwardDefect p β d t u)=
      1-d.C t 0^p-energy p β d t/β := by
  have hc := correlation_row_continuous h ht
  have hs : IntervalIntegrable (fun u => d.C t u^(p-1)*earlierSlope p β d t u) volume 0 t :=
    ((hc.pow (p-1)).mul (slope_row_continuous h)).intervalIntegrable_of_Icc (μ:=volume) ht
  have hr : IntervalIntegrable (fun u => d.C t u^(p-1)*d.R t u) volume 0 t :=
    ((hc.pow (p-1)).mul (response_row_continuous h)).intervalIntegrable_of_Icc (μ:=volume) ht
  simp only [backwardDefect,mul_sub]
  rw [intervalIntegral.integral_sub hs hr,mul_sub,row_power_identity h ht,
    weighted_response_energy h]

end SphericalAging.WeightedResponseIdentities
