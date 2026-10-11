module

public import SphericalAging.FisherPhysicalResponse
public import SphericalAging.ActualProductFromSelected

public section

/-! Actual response-side limit of source15.3. The multiplier error is
uniformly small over each late window by the selected multiplier limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherResponseLimit
open CKSpecification CKPhysicalConsequences StrongBackwardDefect FisherPhysicalWindow
  FisherPhysicalResponse FisherPhysicalMemory CubicResponseLocalization UniformResponseRows StrongResponseRows

theorem memory_bounds {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s t : ℝ} (hs : 0≤s) (hst : s≤t) :
    0≤memoryIntegral d s t ∧ memoryIntegral d s t≤susceptibility d t s := by
  have hR := response_continuousOn h hs hst
  have hC := correlation_first_continuousOn h (t := t) hs
  have hi : IntervalIntegrable (fun u => (1-d.C u s^2)*d.R t u) volume s t :=
    ((continuousOn_const.sub (hC.pow 2)).mul hR).intervalIntegrable_of_Icc hst
  have hb := physical_bounds_of_equations h
  have hfactor (u : ℝ) (hu : u∈Icc s t) : 0≤1-d.C u s^2 ∧ 1-d.C u s^2≤1 := by
    have hh := hb.1 u s (hs.trans hu.1) hs
    constructor
    · nlinarith [hh.1,hh.2]
    · linarith [sq_nonneg (d.C u s)]
  refine ⟨intervalIntegral.integral_nonneg hst (fun u hu => mul_nonneg
    (hfactor u hu).1 (hb.2 t u (hs.trans hu.1) hu.2)),?_⟩
  exact intervalIntegral.integral_mono_on hst hi (hR.intervalIntegrable_of_Icc hst)
    (fun u hu => mul_le_of_le_one_left (hb.2 t u (hs.trans hu.1) hu.2) (hfactor u hu).2)

theorem response_limit_upper {β q z ε I : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r a : ℝ → ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z))
    (he : Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 ε))
    (hε : 0≤ε) (hI : Tendsto (fun n => memoryIntegral d (s n) (t n)) atTop (𝓝 I)) :
    1-PlateauAlgebra.multiplier 3 β q*(1-z)+3*β^2*I≤
      (PlateauAlgebra.multiplier 3 β q+6*β^2*(1+ε))*ε := by
  let ell := PlateauAlgebra.multiplier 3 β q
  have hell : 0<ell := by
    unfold ell PlateauAlgebra.multiplier
    have hp : 0<1/(1-q) := one_div_pos.mpr (sub_pos.mpr H.plateau_lt_one)
    have hq := H.q_positive
    have hq1 := H.plateau_lt_one
    have hfactor : 0≤1-q^2 := by nlinarith
    norm_num only [Nat.cast_ofNat,Nat.reduceSub]
    exact add_pos_of_pos_of_nonneg hp (mul_nonneg
      (mul_nonneg (sq_nonneg β) (by norm_num)) hfactor)
  have hrb := profile_bounds_of_translation h H.translated_response
  have hrzero := profile_response_tendsto_zero H.response_continuous H.response_integrable
    hrb (cubic_response_antitone H)
  have hR := remote_response_sequences h hrb hrzero
    (cubic_positive_plateau_uniform_rows H hf) hs hgap
  have hleft : Tendsto (fun n => 1-ell*(1-d.C (t n) (s n))+3*β^2*memoryIntegral d (s n) (t n))
      atTop (𝓝 (1-ell*(1-z)+3*β^2*I)) :=
    ((tendsto_const_nhds (x := (1:ℝ))).sub
      (((tendsto_const_nhds (x := (1:ℝ))).sub hC).const_mul ell)).add (hI.const_mul (3*β^2))
  apply le_of_forall_pos_le_add
  intro δ hδ
  let η := δ/(1+ε)
  have hη : 0<η := div_pos hδ (by linarith)
  have hηeq : η*(1+ε)=δ := div_mul_cancel₀ δ (by linarith : 1+ε≠0)
  have hLambda : ∀ᶠ n in atTop,∀u∈Icc (s n) (t n),|d.multiplier u-ell|≤η := by
    have hh := H.multiplier_limit.eventually (Metric.ball_mem_nhds _ hη)
    obtain ⟨S,hS⟩ := eventually_atTop.mp hh
    filter_upwards [hs.eventually (eventually_ge_atTop S)] with n hn
    intro u hu
    have hh := hS u (hn.trans hu.1)
    exact (by simpa only [Metric.mem_ball,Real.dist_eq,abs_sub_comm] using hh.le)
  have hright : Tendsto (fun n => d.R (t n) (s n)+η*(1+windowError a (s n) (t n))+
      (ell+6*β^2*(1+windowError a (s n) (t n)))*windowError a (s n) (t n))
      atTop (𝓝 (η*(1+ε)+(ell+6*β^2*(1+ε))*ε)) := by
    convert (hR.add (((tendsto_const_nhds (x := (1:ℝ))).add he).const_mul η)).add
      (((tendsto_const_nhds (x := ell)).add
        (((tendsto_const_nhds (x := (1:ℝ))).add he).const_mul (6*β^2))).mul he) using 1
    simp
  have hineq := le_of_tendsto_of_tendsto hleft hright (by
    filter_upwards [hs.eventually (eventually_gt_atTop (0:ℝ)),
      hgap.eventually (eventually_ge_atTop (0:ℝ)),hLambda] with n hsn hgn hln
    exact (le_abs_self _).trans (primitive_error h ha hsn (by linarith) hell.le hη.le hln))
  rw [hηeq] at hineq
  linarith

end SphericalAging.FisherResponseLimit
