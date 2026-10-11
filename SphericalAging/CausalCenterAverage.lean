module

public import SphericalAging.WindowAverages
public import SphericalAging.StationaryPrefixConsequences

public section

/-! Genuine causal centers and their local Bochner averages. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace Topology NNReal
open Set Filter MeasureTheory
namespace SphericalAging.CausalCenterAverage
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization PrefixReflection
open GreenCovariance CKKernelBounds WindowAverages

@[expose] def localAverage {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (T D : ℝ) : Space (p-1) :=
  WindowAverages.average (fun t=>ckTreeState h (max 0 t)) T D

@[expose] def localCenter {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (T D : ℝ) : Space (p-1) :=
  prefixVector h T (T+D)

theorem localAverage_norm_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hD : 0<D) : ‖localAverage h T D‖≤1 := by
  apply average_norm_le_one _ hD
  intro u _
  exact (ckTreeState_norm h (physical_bounds_of_equations h) (le_max_left 0 (T+u))).le

theorem localAverage_norm_sq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hT : 0≤T) (hD : 0≤D) :
    ‖localAverage h T D‖^2=(D⁻¹)^2*
      (∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,d.C (T+u) (T+v)) := by
  rw [←real_inner_self_eq_norm_sq]
  unfold localAverage
  rw [average_inner _ _ (ckTreeState_clamped_continuous h (physical_bounds_of_equations h))
    (ckTreeState_clamped_continuous h (physical_bounds_of_equations h))]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hD] at hu
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hD] at hv
  dsimp only
  have hTu : 0≤T+u := add_nonneg hT hu.1
  have hTv : 0≤T+v := add_nonneg hT hv.1
  rw [max_eq_right hTu,max_eq_right hTv,ckTreeState_gram h (physical_bounds_of_equations h) hTu hTv]

theorem center_state_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D a : ℝ} (hT : 0≤T) (hD : 0≤D) (ha : 0≤a) :
    inner ℝ (localCenter h T D) (ckTreeState h (max 0 (T+a)))=futureKernel h T D a := by
  rw [max_eq_right (add_nonneg hT ha)]
  unfold localCenter futureKernel prefixKernel prefixVector
  have hh := timePrefix_selfAdjoint T (timePrefix T (ckTreeState h (T+D))) (ckTreeState h (T+a))
  rw [timePrefix_idempotent] at hh
  exact hh

theorem localCenter_average_inner {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hT : 0≤T) (hD : 0≤D) :
    inner ℝ (localCenter h T D) (localAverage h T D)=
      D⁻¹*(∫ a in (0:ℝ)..D,futureKernel h T D a) := by
  unfold localAverage WindowAverages.average
  have hi : IntervalIntegrable (fun a=>ckTreeState h (max 0 (T+a))) volume 0 D :=
    ((ckTreeState_clamped_continuous h (physical_bounds_of_equations h)).comp
      (continuous_const.add continuous_id)).intervalIntegrable 0 D
  rw [real_inner_smul_right,WindowAverages.inner_integral _ hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro a ha
  rw [uIcc_of_le hD] at ha
  exact center_state_inner h hT hD ha.1

/-- Exact finite-time squared error, before any asymptotic input. -/
theorem localCenter_average_error {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hT : 0≤T) (hD : 0≤D) :
    ‖localCenter h T D-localAverage h T D‖^2=‖localCenter h T D‖^2+
      (D⁻¹)^2*(∫ u in (0:ℝ)..D,∫ v in (0:ℝ)..D,d.C (T+u) (T+v))-
      2*D⁻¹*(∫ a in (0:ℝ)..D,futureKernel h T D a) := by
  rw [norm_sub_sq_real,localAverage_norm_sq h hT hD,localCenter_average_inner h hT hD]
  ring

/-- Literal original-time window representation of the constructed average. -/
theorem localAverage_eq_window {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T D : ℝ) :
    localAverage h T D=D⁻¹ • (∫ u in T..T+D,ckTreeState h (max 0 u)) := by
  unfold localAverage WindowAverages.average
  congr 1
  simpa only [add_zero] using intervalIntegral.integral_comp_add_left
    (fun u=>ckTreeState h (max 0 u)) T (a:=0) (b:=D)

theorem localAverage_eq_original_window {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T D : ℝ} (hT : 0≤T) (hD : 0≤D) :
    localAverage h T D=D⁻¹ • (∫ u in T..T+D,ckTreeState h u) := by
  rw [localAverage_eq_window]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le (le_add_of_nonneg_right hD)] at hu
  dsimp only
  rw [max_eq_right (hT.trans hu.1)]

theorem localCenter_terminal_age {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s D : ℝ) :
    localCenter h (s-D) D=timePrefix (s-D) (ckTreeState h s) := by
  unfold localCenter prefixVector
  rw [sub_add_cancel]

end SphericalAging.CausalCenterAverage
