module

public import SphericalAging.StationaryResponseComposition
public import SphericalAging.ReflectionFiniteFubini
public import SphericalAging.PrefixRectangleLimit

public section

/-! Actual stationary reflection from finite response composition, FDT and
compact Fubini. No Laplace transform or reflected-overlap premise is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryReflection
open ScalarConstraints StationaryResponseComposition ReflectionFiniteFubini
open PrefixRectangleLimit PrefixRectangleStability CKSpecification PrefixReflection

/-- Actual stationary self-energy, the negative derivative of B*c^(n+1). -/
@[expose] def stationaryMemoryKernel (n : ℕ) (B : ℝ) (c r : ℝ → ℝ) (t : ℝ) :=
  B*((n : ℝ)+1)*c t^n*r t

theorem stationaryMemoryKernel_continuousOn {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) :
    ContinuousOn (stationaryMemoryKernel n B c r) (Ici 0) :=
  ((h.continuous_c.pow n).const_mul (B*((n : ℝ)+1))).mul h.continuous_r

/-- The response composition input is derived from the genuine stationary
response equation, not added as a property of the cluster. -/
theorem stationary_response_input {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) : ResponseInput ell r (stationaryMemoryKernel n B c r) := by
  refine ⟨h.continuous_r,stationaryMemoryKernel_continuousOn h,h.initial_r,?_⟩
  intro t ht
  have he : StationaryNormalization.causalConvolution (stationaryMemoryKernel n B c r) r t=
      B*((n : ℝ)+1)*causalMemory n c r t := by
    unfold StationaryNormalization.causalConvolution causalMemory stationaryMemoryKernel
    rw [←intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  rw [he]
  exact h.response_derivative t ht

/-- FTC on the actual FDT power gives the exact integrated self-energy. -/
theorem stationaryMemoryKernel_integral {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (∫ z in x..y,stationaryMemoryKernel n B c r z)=B*(c x^(n+1)-c y^(n+1)) := by
  have hc := (h.continuous_c.pow (n+1)).const_mul B
  have hsig := stationaryMemoryKernel_continuousOn h
  have hi : IntervalIntegrable (fun z => -stationaryMemoryKernel n B c r z) volume x y :=
    ((hsig.neg.mono (fun z hz => hx.trans hz.1)).intervalIntegrable_of_Icc hxy)
  have hd (z : ℝ) (hz : z ∈ Ioo x y) :
      HasDerivAt (fun z => B*c z^(n+1)) (-stationaryMemoryKernel n B c r z) z := by
    have hh := ((h.correlation_derivative z (hx.trans hz.1.le)).pow (n+1)).const_mul B
    have hp := hh.hasDerivAt (Ici_mem_nhds (hx.trans_lt hz.1))
    convert hp using 1
    simp only [stationaryMemoryKernel,Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hxy
    (hc.mono (fun z hz => hx.trans hz.1)) hd hi
  rw [intervalIntegral.integral_neg] at hFTC
  simp only [Pi.pow_apply] at hFTC
  nlinarith only [hFTC]

theorem sum_sub_two_min (a b : ℝ) : a+b-2*min a b=|a-b| := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab,abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · rw [min_eq_right (not_le.mp hab).le,abs_of_nonneg (sub_nonneg.mpr (not_le.mp hab).le)]
    ring

/-- The reflected FDT increment is an actual integral of the response. -/
theorem correlation_reflected_increment {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c |a-b|-c (a+b)=2*(∫ w in (0 : ℝ)..min a b,r (a+b-2*w)) := by
  have hm := le_min ha hb
  have hmap : MapsTo (fun w : ℝ => a+b-2*w) (Icc 0 (min a b)) (Ici 0) := by
    intro w hw
    change 0 ≤ a+b-2*w
    linarith [hw.2.trans (min_le_left a b),hw.2.trans (min_le_right a b)]
  have hc : ContinuousOn (fun w => c (a+b-2*w)) (Icc 0 (min a b)) :=
    h.continuous_c.comp (by fun_prop) hmap
  have hi : IntervalIntegrable (fun w => 2*r (a+b-2*w)) volume 0 (min a b) :=
    ((h.continuous_r.comp (by fun_prop) hmap).const_mul 2).intervalIntegrable_of_Icc hm
  have hd (w : ℝ) (hw : w ∈ Ioo 0 (min a b)) :
      HasDerivAt (fun w => c (a+b-2*w)) (2*r (a+b-2*w)) w := by
    have harg : 0 < a+b-2*w := by
      linarith [hw.2.trans_le (min_le_left a b),hw.2.trans_le (min_le_right a b)]
    have hh := ((h.correlation_derivative _ harg.le).hasDerivAt (Ici_mem_nhds harg)).comp w
      (((hasDerivAt_id w).const_mul 2).const_sub (a+b))
    convert hh using 1
    · rfl
    · ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hm hc hd hi
  rw [intervalIntegral.integral_const_mul,sum_sub_two_min] at hFTC
  simp only [mul_zero,sub_zero] at hFTC
  exact hFTC.symm

/-- Actual resolvent composition integrated along a reflected diagonal. -/
theorem stationary_reflection_difference {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c |a-b|-c (a+b)=2*(∫ u in (0 : ℝ)..min a b,r (a-u)*r (b-u))+
      B*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,
        r (a-u)*r (b-v)*(c |u-v|^(n+1)-c (u+v)^(n+1))) := by
  let sigma := stationaryMemoryKernel n B c r
  have hsigma : ContinuousOn sigma (Ici 0) := stationaryMemoryKernel_continuousOn h
  have hinput : ResponseInput ell r sigma := stationary_response_input h
  have hm := le_min ha hb
  have hargs (w : ℝ) (hw : w ∈ Icc 0 (min a b)) : 0 ≤ a-w ∧ 0 ≤ b-w :=
    ⟨sub_nonneg.mpr (hw.2.trans (min_le_left _ _)),sub_nonneg.mpr (hw.2.trans (min_le_right _ _))⟩
  have hcomp (w : ℝ) (hw : w ∈ Icc 0 (min a b)) : r (a+b-2*w)=r (a-w)*r (b-w)+
      ∫ u in (0 : ℝ)..a-w,∫ v in (0 : ℝ)..b-w,r (a-w-u)*r (b-w-v)*sigma (u+v) := by
    have hh := response_composition hinput (hargs w hw).1 (hargs w hw).2
    rw [show (a-w)+(b-w)=a+b-2*w by ring] at hh
    exact hh
  have hmapa : MapsTo (fun w : ℝ => a-w) (Icc 0 (min a b)) (Ici 0) := fun w hw => (hargs w hw).1
  have hmapb : MapsTo (fun w : ℝ => b-w) (Icc 0 (min a b)) (Ici 0) := fun w hw => (hargs w hw).2
  have hmaps : MapsTo (fun w : ℝ => a+b-2*w) (Icc 0 (min a b)) (Ici 0) := by
    intro w hw
    change 0 ≤ a+b-2*w
    linarith [(hargs w hw).1,(hargs w hw).2]
  have hnoise := (h.continuous_r.comp (by fun_prop) hmapa).mul
    (h.continuous_r.comp (by fun_prop) hmapb)
  have hsum := h.continuous_r.comp (by fun_prop) hmaps
  have hmem : IntervalIntegrable (fun w => ∫ u in (0 : ℝ)..a-w,∫ v in (0 : ℝ)..b-w,
      r (a-w-u)*r (b-w-v)*sigma (u+v)) volume 0 (min a b) := by
    have hc : ContinuousOn (fun w => ∫ u in (0 : ℝ)..a-w,∫ v in (0 : ℝ)..b-w,
        r (a-w-u)*r (b-w-v)*sigma (u+v)) (Icc 0 (min a b)) :=
      (hsum.sub hnoise).congr (fun w hw => by
        change _=r (a+b-2*w)-r (a-w)*r (b-w)
        have hh := hcomp w hw
        linarith only [hh])
    exact hc.intervalIntegrable_of_Icc hm
  have hsplit : (∫ w in (0 : ℝ)..min a b,r (a+b-2*w))=
      (∫ w in (0 : ℝ)..min a b,r (a-w)*r (b-w))+
      (∫ w in (0 : ℝ)..min a b,∫ u in (0 : ℝ)..a-w,∫ v in (0 : ℝ)..b-w,
        r (a-w-u)*r (b-w-v)*sigma (u+v)) := by
    rw [←intervalIntegral.integral_add
      (f := fun w => r (a-w)*r (b-w))
      (g := fun w => ∫ u in (0 : ℝ)..a-w,∫ v in (0 : ℝ)..b-w,r (a-w-u)*r (b-w-v)*sigma (u+v))
      (hnoise.intervalIntegrable_of_Icc hm) hmem]
    apply intervalIntegral.integral_congr
    intro w hw
    rw [uIcc_of_le hm] at hw
    exact hcomp w hw
  rw [correlation_reflected_increment h ha hb,hsplit,mul_add,
    reflected_memory_rearrangement_on_ray h.continuous_r hsigma ha hb]
  congr 1
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ha] at hu
  dsimp only
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hb] at hv
  dsimp only
  have horder : |u-v| ≤ u+v := (abs_le.mpr ⟨by linarith [hu.1,hv.1],by linarith [hu.1,hv.1]⟩)
  change r (a-u)*r (b-v)*(∫ z in |u-v|..u+v,stationaryMemoryKernel n B c r z)=_
  rw [stationaryMemoryKernel_integral h (abs_nonneg (u-v)) horder]
  ring

/-- The reflected candidate satisfies the exact limiting rectangle. -/
theorem stationary_reflection_rectangle {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    c (a+b)=c |a-b|-2*(∫ u in (0 : ℝ)..min a b,r (a-u)*r (b-u))-
      B*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,
        r (a-u)*r (b-v)*(c |u-v|^(n+1)-c (u+v)^(n+1))) := by
  have hh := stationary_reflection_difference h ha hb
  linarith only [hh]

/-- A globally continuous harmless extension of the genuine reflected kernel. -/
@[expose] def reflectedCandidate (c : ℝ → ℝ) (a b : ℝ) := c (max 0 (a+b))

theorem reflectedCandidate_continuous {c : ℝ → ℝ} (hc : ContinuousOn c (Ici 0)) :
    Continuous (Function.uncurry (reflectedCandidate c)) := by
  exact hc.comp_continuous (show Continuous (fun z : ℝ × ℝ => max 0 (z.1+z.2)) by fun_prop)
    (fun z => le_max_left 0 (z.1+z.2))

theorem reflectedCandidate_eq (c : ℝ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    reflectedCandidate c a b=c (a+b) := by simp only [reflectedCandidate,max_eq_right (add_nonneg ha hb)]

theorem stationary_correlation_unit {n : ℕ} {B ell : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) {t : ℝ} (ht : 0 ≤ t) : |c t| ≤ 1 := by
  rw [abs_of_nonneg (h.correlation_nonnegative t ht)]
  have hh := stationary_integral_response n B ell c r h t ht
  have hi := intervalIntegral.integral_nonneg (μ := volume) ht (fun u hu => h.response_nonnegative u hu.1)
  linarith only [hh,hi]

/-- Candidate verification uses only actual stationary FDT and response equations. -/
theorem reflectedCandidate_equation {n : ℕ} {B ell A : ℝ} {c r : ℝ → ℝ}
    (h : StationaryInputs n B ell c r) :
    RectangleEquation (n+1) B A (stationaryCorrelation c) (stationaryResponse r) (reflectedCandidate c) := by
  intro a ha b hb
  rw [reflectedCandidate_eq c ha.1 hb.1]
  unfold rectangleOperator stationaryCorrelation
  have hN : (∫ u in (0 : ℝ)..min a b,stationaryResponse r a u*stationaryResponse r b u)=
      ∫ u in (0 : ℝ)..min a b,r (a-u)*r (b-u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (le_min ha.1 hb.1)] at hu
    dsimp only [stationaryResponse]
    rw [max_eq_right (sub_nonneg.mpr (hu.2.trans (min_le_left _ _))),
      max_eq_right (sub_nonneg.mpr (hu.2.trans (min_le_right _ _)))]
  have hM : (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,
      stationaryResponse r a u*stationaryResponse r b v*(c |u-v|^(n+1)-reflectedCandidate c u v^(n+1)))=
      ∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,r (a-u)*r (b-v)*(c |u-v|^(n+1)-c (u+v)^(n+1)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ha.1] at hu
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le hb.1] at hv
    dsimp only [stationaryResponse]
    rw [max_eq_right (sub_nonneg.mpr hu.2),max_eq_right (sub_nonneg.mpr hv.2),reflectedCandidate_eq c hu.1 hv.1]
  rw [hN,hM]
  exact stationary_reflection_rectangle h ha.1 hb.1

/-- The actual prefix kernels converge uniformly to the reflected stationary
correlation. The candidate equation, existence and uniqueness are all proved. -/
theorem prefix_reflection_uniform {p : ℕ} {β ell A : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (hS : StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r)
    (hA : 0 ≤ A) (hT : ∀ n,0 ≤ T n)
    (hC : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) atTop (square A) := by
  obtain ⟨q,hq,heq,hQ,huniq⟩ := prefix_rectangle_limit_exists h hA hT hS.continuous_c hS.continuous_r hC hR
  have hcand : UnitData A (stationaryCorrelation c) (stationaryResponse r) (reflectedCandidate c) :=
    ⟨hq.correlation_continuous,hq.response_continuous,reflectedCandidate_continuous hS.continuous_c,
      hq.correlation_bound,hq.response_bound,fun a ha b hb => by
        rw [reflectedCandidate_eq c ha.1 hb.1]
        exact stationary_correlation_unit hS (add_nonneg ha.1 hb.1)⟩
  have hexp : p-2+1=p-1 := by have hp := h.spin_ge_three; omega
  have hcandeq : RectangleEquation (p-1) (β^2*(p : ℝ)) A
      (stationaryCorrelation c) (stationaryResponse r) (reflectedCandidate c) := by
    simpa only [hexp] using (reflectedCandidate_equation (A := A) hS)
  have hsame := huniq _ hcand hcandeq
  exact hQ.congr_right (fun z hz => by
    change q z.1 z.2=c (z.1+z.2)
    rw [←hsame z.1 hz.1 z.2 hz.2,reflectedCandidate_eq c hz.1.1 hz.2.1])

/-- Only eventual physical translation times are required. -/
theorem prefix_reflection_uniform_eventually {p : ℕ} {β ell A : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (hS : StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r)
    (hA : 0 ≤ A) (hT : ∀ᶠ n in atTop,0 ≤ T n)
    (hC : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) atTop (square A) := by
  let T' n := max 0 (T n)
  have hc' : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T' n+z.1) (T' n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A) := hC.congr (by
    filter_upwards [hT] with n hn z hz
    simp only [T',max_eq_right hn])
  have hr' : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.R (T' n+z.1) (T' n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A) := hR.congr (by
    filter_upwards [hT] with n hn z hz
    simp only [T',max_eq_right hn])
  have hQ := prefix_reflection_uniform h hS hA (fun n => le_max_left _ _) hc' hr'
  exact hQ.congr (by
    filter_upwards [hT] with n hn z hz
    simp only [max_eq_right hn])

/-- The source hypothesis T_n→infinity supplies eventual physical times. -/
theorem prefix_reflection_uniform_late {p : ℕ} {β ell A : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (hS : StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r)
    (hA : 0 ≤ A) (hT : Tendsto T atTop atTop)
    (hC : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : TendstoUniformlyOn (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) atTop (square A) :=
  prefix_reflection_uniform_eventually h hS hA (hT.eventually (eventually_ge_atTop 0)) hC hR

end SphericalAging.StationaryReflection
