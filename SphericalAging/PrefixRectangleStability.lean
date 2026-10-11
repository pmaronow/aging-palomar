module

public import SphericalAging.CKStability
public import SphericalAging.CovarianceIteration

public section

/-! Actual rectangular Volterra stability. The integral inequality is derived
from the rectangle equation and its coefficients; the limiting equation is
obtained by uniform convergence, rather than supplied as a conclusion. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology
namespace SphericalAging.PrefixRectangleStability
open TriangleUniqueness CKStability CKFiniteUniqueness CovarianceIteration

/-- The physical offset square. -/
@[expose] def square (A : ℝ) : Set (ℝ × ℝ) := Icc 0 A ×ˢ Icc 0 A

/-- The physical response triangle. -/
@[expose] def triangle (A : ℝ) : Set (ℝ × ℝ) := {z | z.1 ∈ Icc 0 A ∧ z.2 ∈ Icc 0 z.1}

/-- The actual finite-future rectangle operator, with arbitrary coefficients. -/
@[expose] def rectangleOperator (m : ℕ) (B : ℝ) (C R Q : ℝ → ℝ → ℝ) (a b : ℝ) : ℝ :=
  C a b-2*(∫ u in (0 : ℝ)..min a b,R a u*R b u)-
    B*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R a u*R b v*(C u v^m-Q u v^m))

/-- A faithful local equation, containing no uniqueness or reflection field. -/
@[expose] def RectangleEquation (m : ℕ) (B A : ℝ) (C R Q : ℝ → ℝ → ℝ) : Prop :=
  ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,Q a b=rectangleOperator m B C R Q a b

/-- The norm of a genuine double integral is bounded by its integrated norm. -/
theorem rectangle_abs_integral_le {F : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    |∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,F u v| ≤
      ∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|F u v| := by
  have hi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hF 0 b
  have habs := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) (f := fun u v => |F u v|) hF.abs 0 b
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume)
    (f := fun u => ∫ v in (0 : ℝ)..b,F u v) ha
  have hm := intervalIntegral.integral_mono_on ha (hi.norm.intervalIntegrable (μ := volume) 0 a)
    (habs.intervalIntegrable (μ := volume) 0 a) (fun u _ => by
      simpa only [Real.norm_eq_abs] using
        (intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := fun v => F u v) hb))
  simpa only [Real.norm_eq_abs] using hn.trans hm

/-- The running square norm at either argument dominates the two-variable
error. No symmetry of the error is needed. -/
theorem error_le_sum_runningNorm {D : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    |D u v| ≤ runningNorm D u+runningNorm D v := by
  by_cases huv : u ≤ v
  · have hd := runningNorm_dominate hD hv ⟨hu,huv⟩ ⟨hv,le_refl v⟩
    linarith [runningNorm_nonneg hD hu]
  · have hd := runningNorm_dominate hD hu ⟨hu,le_refl u⟩ ⟨hv,(not_le.mp huv).le⟩
    linarith [runningNorm_nonneg hD hv]

/-- Rectangular memory is reduced to an actual one-variable primitive. -/
theorem rectangle_error_running_bound {D : ℝ → ℝ → ℝ}
    (hD : Continuous (Function.uncurry D)) {A t a b : ℝ}
    (ht : t ∈ Icc 0 A) (ha : a ∈ Icc 0 t) (hb : b ∈ Icc 0 t) :
    (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|D u v|) ≤
      2*A*∫ u in (0 : ℝ)..t,runningNorm D u := by
  have hw := runningNorm_continuous hD
  have hm := rectangle_integral_mono (F := fun u v => |D u v|) (G := fun u v => runningNorm D u+runningNorm D v) hD.abs
    ((hw.comp continuous_fst).add (hw.comp continuous_snd)) ha.1 hb.1
    (fun u hu v hv => error_le_sum_runningNorm hD hu.1 hv.1)
  have he : (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,runningNorm D u+runningNorm D v)=
      b*(∫ u in (0 : ℝ)..a,runningNorm D u)+a*(∫ v in (0 : ℝ)..b,runningNorm D v) := by
    simp_rw [intervalIntegral.integral_add (intervalIntegrable_const)
      (hw.intervalIntegrable (μ := volume) 0 b),intervalIntegral.integral_const,sub_zero,smul_eq_mul]
    rw [intervalIntegral.integral_add ((hw.const_mul b).intervalIntegrable 0 a)
      intervalIntegrable_const,intervalIntegral.integral_const_mul,intervalIntegral.integral_const]
    simp only [sub_zero,smul_eq_mul]
  rw [he] at hm
  have hinc (x : ℝ) (hx : x ∈ Icc 0 t) :
      (∫ u in (0 : ℝ)..x,runningNorm D u) ≤ ∫ u in (0 : ℝ)..t,runningNorm D u := by
    exact intervalIntegral.integral_mono_interval (le_refl 0) hx.1 hx.2
      (ae_restrict_mem measurableSet_Ioc |>.mono (fun u hu => runningNorm_nonneg hD hu.1.le))
      (hw.intervalIntegrable 0 t)
  have hn : 0 ≤ ∫ u in (0 : ℝ)..t,runningNorm D u :=
    intervalIntegral.integral_nonneg ht.1 (fun u hu => runningNorm_nonneg hD hu.1)
  have h1 := mul_le_mul_of_nonneg_left (hinc a ha) hb.1
  have h2 := mul_le_mul_of_nonneg_left (hinc b hb) ha.1
  have h3 := mul_le_mul_of_nonneg_right (ha.2.trans ht.2) hn
  have h4 := mul_le_mul_of_nonneg_right (hb.2.trans ht.2) hn
  linarith only [hm,h1,h2,h3,h4]

/-- The source's exponential stability factor follows from the true
rectangular Volterra inequality via a continuous running supremum. -/
theorem rectangle_volterra_stability {D : ℝ → ℝ → ℝ} {A ε K : ℝ}
    (hD : Continuous (Function.uncurry D)) (hA : 0 ≤ A) (_hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hbound : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,
      |D a b| ≤ ε+K*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|D u v|)) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|D a b| ≤ ε*Real.exp (2*K*A^2) := by
  have hw := runningNorm_continuous hD
  have hrun (t : ℝ) (ht : t ∈ Icc 0 A) :
      runningNorm D t ≤ ε+(2*K*A)*(∫ u in (0 : ℝ)..t,runningNorm D u) := by
    unfold runningNorm
    apply csSup_le
    · exact unitSquare_nonempty.image _
    · intro x hx
      obtain ⟨z,hz,rfl⟩ := hx
      have hu : t*z.1 ∈ Icc 0 t := ⟨mul_nonneg ht.1 hz.1.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.1.2 ht.1⟩
      have hv : t*z.2 ∈ Icc 0 t := ⟨mul_nonneg ht.1 hz.2.1,by simpa only [mul_one] using mul_le_mul_of_nonneg_left hz.2.2 ht.1⟩
      have hh := hbound _ ⟨hu.1,hu.2.trans ht.2⟩ _ ⟨hv.1,hv.2.trans ht.2⟩
      have hm := mul_le_mul_of_nonneg_left (rectangle_error_running_bound hD ht hu hv) hK
      change |D (t*z.1) (t*z.2)| ≤ ε+(2*K*A)*(∫ u in (0 : ℝ)..t,runningNorm D u)
      nlinarith only [hh,hm]
  have hg := continuous_integral_gronwall hw (by positivity : 0 ≤ 2*K*A) hrun A ⟨hA,le_refl A⟩
  intro a ha b hb
  have hh := (runningNorm_dominate hD hA ha hb).trans hg
  simpa only [pow_two,mul_assoc] using hh

/-- Zero-source rectangular Volterra uniqueness, without a zero-error premise. -/
theorem rectangle_volterra_unique {D : ℝ → ℝ → ℝ} {A K : ℝ}
    (hD : Continuous (Function.uncurry D)) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hbound : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,
      |D a b| ≤ K*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|D u v|)) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,D a b=0 := by
  have hh := rectangle_volterra_stability hD hA (le_refl 0) hK
    (by simpa only [zero_add] using hbound)
  intro a ha b hb
  exact abs_eq_zero.mp (le_antisymm (by simpa using hh a ha b hb) (abs_nonneg _))

/-- Uniformly bounded powers are Lipschitz with their actual integer degree. -/
theorem unit_power_difference {x y : ℝ} (hx : |x| ≤ 1) (hy : |y| ≤ 1) (m : ℕ) :
    |x^m-y^m| ≤ (m : ℝ)*|x-y| := by
  simpa only [powerLip,one_pow,mul_one] using
    power_difference_le (by norm_num : (0 : ℝ) ≤ 1) (abs_nonneg (x-y)) hx hy (le_refl _) m

/-- Coefficient errors and solution errors are separated before integration. -/
theorem unit_product_power_difference {r s r' s' x y δ : ℝ} (hδ : 0 ≤ δ)
    (hr : |r| ≤ 1) (hs : |s| ≤ 1) (hr' : |r'| ≤ 1) (hs' : |s'| ≤ 1)
    (hx : |x| ≤ 1) (hy : |y| ≤ 1) (hrr : |r-r'| ≤ δ) (hss : |s-s'| ≤ δ) (m : ℕ) :
    |r*s*x^m-r'*s'*y^m| ≤ 2*δ+(m : ℝ)*|x-y| := by
  have hcoef : |r*s-r'*s'| ≤ 2*δ := by
    have hh := power_triple_difference_le (by norm_num : (0 : ℝ) ≤ 1) hδ
      (by norm_num : |(1 : ℝ)| ≤ 1) (by norm_num : |(1 : ℝ)| ≤ 1)
      hr hr' hs hs' (by simpa using hδ) hrr hss 0
    simpa only [pow_zero,one_mul,tripleLip,powerLip,one_pow,Nat.cast_zero,zero_mul,zero_add,mul_one] using hh
  have hpow := unit_power_difference hx hy m
  have hxpow : |x^m| ≤ 1 := by simpa only [abs_pow,one_pow] using pow_le_pow_left₀ (abs_nonneg x) hx m
  have hrs : |r'*s'| ≤ 1 := by rw [abs_mul]; nlinarith [abs_nonneg r',abs_nonneg s']
  have he : r*s*x^m-r'*s'*y^m=(r*s-r'*s')*x^m+r'*s'*(x^m-y^m) := by ring
  rw [he]
  calc
    _ ≤ |(r*s-r'*s')*x^m|+|r'*s'*(x^m-y^m)| := abs_add_le _ _
    _ ≤ (2*δ)*1+1*((m : ℝ)*|x-y|) := by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul hcoef hxpow (abs_nonneg _) (by positivity))
        (mul_le_mul hrs hpow (abs_nonneg _) (by norm_num))
    _ = _ := by ring

/-- Double integration preserves a continuous variable error bound. -/
theorem rectangle_integral_difference_bound {F G H : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hG : Continuous (Function.uncurry G))
    (hH : Continuous (Function.uncurry H)) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hbound : ∀ u ∈ Icc 0 a,∀ v ∈ Icc 0 b,|F u v-G u v| ≤ H u v) :
    |(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,F u v)-
      (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,G u v)| ≤
      ∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,H u v := by
  have hFi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hF 0 b
  have hGi := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) hG 0 b
  have he : (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,F u v)-
      (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,G u v)=
      ∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,F u v-G u v := by
    rw [←intervalIntegral.integral_sub (hFi.intervalIntegrable 0 a) (hGi.intervalIntegrable 0 a)]
    apply intervalIntegral.integral_congr
    intro u _
    exact (intervalIntegral.integral_sub
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 b)
      ((hG.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 b)).symm
  rw [he]
  exact (rectangle_abs_integral_le (F := fun u v => F u v-G u v) (hF.sub hG) ha hb).trans
    (rectangle_integral_mono (F := fun u v => |F u v-G u v|) (G := H)
      (hF.sub hG).abs hH ha hb hbound)

/-- Only the actual regularity and physical local bounds are packaged here. -/
structure UnitData (A : ℝ) (C R Q : ℝ → ℝ → ℝ) : Prop where
  correlation_continuous : Continuous (Function.uncurry C)
  response_continuous : Continuous (Function.uncurry R)
  solution_continuous : Continuous (Function.uncurry Q)
  correlation_bound : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|C a b| ≤ 1
  response_bound : ∀ a ∈ Icc 0 A,∀ u ∈ Icc 0 a,|R a u| ≤ 1
  solution_bound : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|Q a b| ≤ 1

/-- Coefficient error in the nonlinearity, separated from the unknown kernel. -/
theorem memory_integrand_difference {A δ a b u v : ℝ} {m : ℕ}
    {C R Q C' R' Q' : ℝ → ℝ → ℝ}
    (h : UnitData A C R Q) (h' : UnitData A C' R' Q') (hδ : 0 ≤ δ)
    (hC : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|C a b-C' a b| ≤ δ)
    (hR : ∀ a ∈ Icc 0 A,∀ u ∈ Icc 0 a,|R a u-R' a u| ≤ δ)
    (ha : a ∈ Icc 0 A) (hb : b ∈ Icc 0 A) (hu : u ∈ Icc 0 a) (hv : v ∈ Icc 0 b) :
    |R a u*R b v*(C u v^m-Q u v^m)-R' a u*R' b v*(C' u v^m-Q' u v^m)| ≤
      ((m : ℝ)+4)*δ+(m : ℝ)*|Q u v-Q' u v| := by
  have huA : u ∈ Icc 0 A := ⟨hu.1,hu.2.trans ha.2⟩
  have hvA : v ∈ Icc 0 A := ⟨hv.1,hv.2.trans hb.2⟩
  have hc := power_triple_difference_le (by norm_num : (0 : ℝ) ≤ 1) hδ
    (h.correlation_bound u huA v hvA) (h'.correlation_bound u huA v hvA)
    (h.response_bound a ha u hu) (h'.response_bound a ha u hu)
    (h.response_bound b hb v hv) (h'.response_bound b hb v hv)
    (hC u huA v hvA) (hR a ha u hu) (hR b hb v hv) m
  simp only [tripleLip,powerLip,one_pow,mul_one] at hc
  have hq := unit_product_power_difference hδ
    (h.response_bound a ha u hu) (h.response_bound b hb v hv)
    (h'.response_bound a ha u hu) (h'.response_bound b hb v hv)
    (h.solution_bound u huA v hvA) (h'.solution_bound u huA v hvA)
    (hR a ha u hu) (hR b hb v hv) m
  have he : R a u*R b v*(C u v^m-Q u v^m)-R' a u*R' b v*(C' u v^m-Q' u v^m)=
      (C u v^m*R a u*R b v-C' u v^m*R' a u*R' b v)-
      (R a u*R b v*Q u v^m-R' a u*R' b v*Q' u v^m) := by ring
  rw [he]
  have ht := abs_sub_le (C u v^m*R a u*R b v-C' u v^m*R' a u*R' b v) 0
    (R a u*R b v*Q u v^m-R' a u*R' b v*Q' u v^m)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  nlinarith only [ht,hc,hq]

/-- The explicit coefficient contribution to the rectangle error. -/
@[expose] def coefficientFactor (m : ℕ) (B A : ℝ) : ℝ := 1+4*A+B*((m : ℝ)+4)*A^2

theorem coefficientFactor_nonnegative (m : ℕ) {B A : ℝ} (hB : 0 ≤ B) (hA : 0 ≤ A) :
    0 ≤ coefficientFactor m B A := by unfold coefficientFactor; positivity

/-- Actual subtraction of two rectangle equations gives their Volterra error
inequality; no smallness of the rectangle is required. -/
theorem rectangle_operators_difference {m : ℕ} {B A δ : ℝ}
    {C R Q C' R' Q' : ℝ → ℝ → ℝ}
    (h : UnitData A C R Q) (h' : UnitData A C' R' Q')
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hC : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|C a b-C' a b| ≤ δ)
    (hR : ∀ a ∈ Icc 0 A,∀ u ∈ Icc 0 a,|R a u-R' a u| ≤ δ) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,
      |rectangleOperator m B C R Q a b-rectangleOperator m B C' R' Q' a b| ≤
      coefficientFactor m B A*δ+B*(m : ℝ)*
        (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|Q u v-Q' u v|) := by
  intro a ha b hb
  have hA : 0 ≤ A := ha.1.trans ha.2
  have hmin : 0 ≤ min a b := le_min ha.1 hb.1
  have hN := integral_difference_variable_bound
    (f := fun u => R a u*R b u) (g := fun u => R' a u*R' b u)
    ((h.response_continuous.comp (continuous_const.prodMk continuous_id)).mul
      (h.response_continuous.comp (continuous_const.prodMk continuous_id)))
    ((h'.response_continuous.comp (continuous_const.prodMk continuous_id)).mul
      (h'.response_continuous.comp (continuous_const.prodMk continuous_id))) continuous_const hmin
    (b := fun _ => 2*δ) (fun u hu => by
      have hua : u ∈ Icc 0 a := ⟨hu.1,hu.2.trans (min_le_left a b)⟩
      have hub : u ∈ Icc 0 b := ⟨hu.1,hu.2.trans (min_le_right a b)⟩
      have hh := unit_product_power_difference hδ
        (h.response_bound a ha u hua) (h.response_bound b hb u hub)
        (h'.response_bound a ha u hua) (h'.response_bound b hb u hub)
        (by norm_num : |(1 : ℝ)| ≤ 1) (by norm_num : |(1 : ℝ)| ≤ 1)
        (hR a ha u hua) (hR b hb u hub) 0
      simpa only [pow_zero,mul_one,Nat.cast_zero,zero_mul,add_zero] using hh)
  rw [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hN
  have hNa : |(∫ u in (0 : ℝ)..min a b,R a u*R b u)-
      (∫ u in (0 : ℝ)..min a b,R' a u*R' b u)| ≤ 2*A*δ :=
    hN.trans (by nlinarith [min_le_left a b,ha.2])
  have hf : Continuous (Function.uncurry (fun u v => R a u*R b v*(C u v^m-Q u v^m))) :=
    (((h.response_continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (h.response_continuous.comp (continuous_const.prodMk continuous_snd))).mul
      ((h.correlation_continuous.pow m).sub (h.solution_continuous.pow m)))
  have hfp : Continuous (Function.uncurry (fun u v => R' a u*R' b v*(C' u v^m-Q' u v^m))) :=
    (((h'.response_continuous.comp (continuous_const.prodMk continuous_fst)).mul
      (h'.response_continuous.comp (continuous_const.prodMk continuous_snd))).mul
      ((h'.correlation_continuous.pow m).sub (h'.solution_continuous.pow m)))
  have hd : Continuous (fun z : ℝ × ℝ => |Q z.1 z.2-Q' z.1 z.2|) := by
    simpa only [Function.uncurry_def,Pi.sub_apply] using
      (h.solution_continuous.sub h'.solution_continuous).abs
  have hMaj : Continuous (Function.uncurry (fun u v => ((m : ℝ)+4)*δ+(m : ℝ)*|Q u v-Q' u v|)) := by
    convert (continuous_const (y := ((m : ℝ)+4)*δ)).add (hd.const_mul (m : ℝ)) using 1
    funext z
    rfl
  have hI := rectangle_integral_difference_bound
    (H := fun u v => ((m : ℝ)+4)*δ+(m : ℝ)*|Q u v-Q' u v|) hf hfp
    hMaj ha.1 hb.1
    (fun u hu v hv => memory_integrand_difference h h' hδ hC hR ha hb hu hv)
  have hsplit : (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,((m : ℝ)+4)*δ+(m : ℝ)*|Q u v-Q' u v|)=
      a*b*(((m : ℝ)+4)*δ)+(m : ℝ)*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|Q u v-Q' u v|) := by
    have hrow (u : ℝ) :
        (∫ v in (0 : ℝ)..b,((m : ℝ)+4)*δ+(m : ℝ)*|Q u v-Q' u v|)=
          b*(((m : ℝ)+4)*δ)+(m : ℝ)*(∫ v in (0 : ℝ)..b,|Q u v-Q' u v|) := by
      rw [intervalIntegral.integral_add (f := fun _ => ((m : ℝ)+4)*δ)
        (g := fun v => (m : ℝ)*|Q u v-Q' u v|) intervalIntegrable_const
        (((hd.comp (continuous_const.prodMk continuous_id)).const_mul (m : ℝ)).intervalIntegrable 0 b),
        intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
      simp only [sub_zero,smul_eq_mul]
    simp_rw [hrow]
    have hc := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
      (f := fun u v => |Q u v-Q' u v|) hd 0 b
    rw [intervalIntegral.integral_add (f := fun _ => b*(((m : ℝ)+4)*δ))
      (g := fun u => (m : ℝ)*(∫ v in (0 : ℝ)..b,|Q u v-Q' u v|))
      intervalIntegrable_const ((hc.const_mul (m : ℝ)).intervalIntegrable 0 a),
      intervalIntegral.integral_const,intervalIntegral.integral_const_mul]
    simp only [sub_zero,smul_eq_mul]
    ring
  rw [hsplit] at hI
  have harea : a*b ≤ A^2 := by nlinarith [mul_le_mul ha.2 hb.2 hb.1 hA]
  have hI' := hI.trans (add_le_add
    (mul_le_mul_of_nonneg_right harea (by positivity : 0 ≤ ((m : ℝ)+4)*δ)) le_rfl)
  unfold rectangleOperator
  have ht := abs_sub_le (C a b-C' a b) 0
    (2*((∫ u in (0 : ℝ)..min a b,R a u*R b u)-
        (∫ u in (0 : ℝ)..min a b,R' a u*R' b u))+
      B*((∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R a u*R b v*(C u v^m-Q u v^m))-
        (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R' a u*R' b v*(C' u v^m-Q' u v^m))))
  simp only [sub_zero,zero_sub,abs_neg] at ht
  have htri := abs_add_le
    (2*((∫ u in (0 : ℝ)..min a b,R a u*R b u)-
      (∫ u in (0 : ℝ)..min a b,R' a u*R' b u)))
    (B*((∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R a u*R b v*(C u v^m-Q u v^m))-
      (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R' a u*R' b v*(C' u v^m-Q' u v^m))))
  rw [abs_mul,abs_mul,abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),abs_of_nonneg hB] at htri
  have hn := mul_le_mul_of_nonneg_left hNa (by norm_num : (0 : ℝ) ≤ 2)
  have hm := mul_le_mul_of_nonneg_left hI' hB
  have hc := hC a ha b hb
  have he : C a b-2*(∫ u in (0 : ℝ)..min a b,R a u*R b u)-
      B*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R a u*R b v*(C u v^m-Q u v^m))-
      (C' a b-2*(∫ u in (0 : ℝ)..min a b,R' a u*R' b u)-
      B*(∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R' a u*R' b v*(C' u v^m-Q' u v^m)))=
      (C a b-C' a b)-(2*((∫ u in (0 : ℝ)..min a b,R a u*R b u)-
        (∫ u in (0 : ℝ)..min a b,R' a u*R' b u))+
      B*((∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R a u*R b v*(C u v^m-Q u v^m))-
        (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,R' a u*R' b v*(C' u v^m-Q' u v^m)))) := by ring
  rw [he]
  unfold coefficientFactor
  nlinarith only [ht,htri,hn,hm,hc]

/-- Actual equation subtraction, using only the coefficient error bounds. -/
theorem rectangle_equations_difference {m : ℕ} {B A δ : ℝ}
    {C R Q C' R' Q' : ℝ → ℝ → ℝ}
    (h : UnitData A C R Q) (h' : UnitData A C' R' Q')
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (heq : RectangleEquation m B A C R Q) (heq' : RectangleEquation m B A C' R' Q')
    (hC : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|C a b-C' a b| ≤ δ)
    (hR : ∀ a ∈ Icc 0 A,∀ u ∈ Icc 0 a,|R a u-R' a u| ≤ δ) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|Q a b-Q' a b| ≤
      coefficientFactor m B A*δ+B*(m : ℝ)*
        (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|Q u v-Q' u v|) := by
  intro a ha b hb
  rw [heq a ha b hb,heq' a ha b hb]
  exact rectangle_operators_difference h h' hB hδ hC hR a ha b hb

/-- The complete finite-rectangle coefficient stability estimate. -/
theorem rectangle_stability {m : ℕ} {B A δ : ℝ}
    {C R Q C' R' Q' : ℝ → ℝ → ℝ}
    (h : UnitData A C R Q) (h' : UnitData A C' R' Q')
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (heq : RectangleEquation m B A C R Q) (heq' : RectangleEquation m B A C' R' Q')
    (hC : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|C a b-C' a b| ≤ δ)
    (hR : ∀ a ∈ Icc 0 A,∀ u ∈ Icc 0 a,|R a u-R' a u| ≤ δ) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|Q a b-Q' a b| ≤
      (coefficientFactor m B A*Real.exp (2*B*(m : ℝ)*A^2))*δ := by
  have hD : Continuous (Function.uncurry (fun a b => Q a b-Q' a b)) := by
    convert h.solution_continuous.sub h'.solution_continuous using 1
    funext z
    rfl
  have hh := rectangle_volterra_stability hD hA
    (mul_nonneg (coefficientFactor_nonnegative m hB hA) hδ)
    (mul_nonneg hB (Nat.cast_nonneg m))
    (rectangle_equations_difference h h' hB hδ heq heq' hC hR)
  intro a ha b hb
  have he : 2*(B*(m : ℝ))*A^2=2*B*(m : ℝ)*A^2 := by ring
  rw [he] at hh
  simpa only [mul_assoc,mul_comm,mul_left_comm] using hh a ha b hb

/-- The limiting rectangle equation has at most one physical solution. -/
theorem rectangle_unique {m : ℕ} {B A : ℝ} {C R Q Q' : ℝ → ℝ → ℝ}
    (h : UnitData A C R Q) (h' : UnitData A C R Q') (hA : 0 ≤ A) (hB : 0 ≤ B)
    (heq : RectangleEquation m B A C R Q) (heq' : RectangleEquation m B A C R Q') :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,Q a b=Q' a b := by
  have hh := rectangle_stability h h' hA hB (le_refl 0) heq heq'
    (by intro a ha b hb; simp) (by intro a ha b hb; simp)
  intro a ha b hb
  exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm (by simpa using hh a ha b hb) (abs_nonneg _)))

/-- Converging physical coefficients make the actual projected solutions
uniformly Cauchy, before any limiting equation or reflection is known. -/
theorem rectangle_uniformCauchy {m : ℕ} {B A : ℝ}
    {C R Q : ℕ → ℝ → ℝ → ℝ} {c r : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ∀ n,UnitData A (C n) (R n) (Q n))
    (heq : ∀ n,RectangleEquation m B A (C n) (R n) (Q n))
    (hC : TendstoUniformlyOn (fun n => Function.uncurry (C n)) (Function.uncurry c) atTop (square A))
    (hR : TendstoUniformlyOn (fun n => Function.uncurry (R n)) (Function.uncurry r) atTop (triangle A)) :
    UniformCauchySeqOn (fun n => Function.uncurry (Q n)) atTop (square A) := by
  rw [Metric.uniformCauchySeqOn_iff]
  intro ε hε
  let K := coefficientFactor m B A*Real.exp (2*B*(m : ℝ)*A^2)
  have hK : 0 ≤ K := mul_nonneg (coefficientFactor_nonnegative m hB hA) (Real.exp_pos _).le
  let δ := ε/(K+1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  obtain ⟨NC,hNC⟩ := Metric.uniformCauchySeqOn_iff.mp hC.uniformCauchySeqOn δ hδ
  obtain ⟨NR,hNR⟩ := Metric.uniformCauchySeqOn_iff.mp hR.uniformCauchySeqOn δ hδ
  refine ⟨max NC NR,?_⟩
  intro i hi j hj z hz
  have hcb (a : ℝ) (ha : a ∈ Icc 0 A) (b : ℝ) (hb : b ∈ Icc 0 A) :
      |C i a b-C j a b| ≤ δ := by
    have hh := hNC i ((le_max_left _ _).trans hi) j ((le_max_left _ _).trans hj) (a,b) ⟨ha,hb⟩
    simpa only [Real.dist_eq,Function.uncurry_def] using hh.le
  have hrb (a : ℝ) (ha : a ∈ Icc 0 A) (u : ℝ) (hu : u ∈ Icc 0 a) :
      |R i a u-R j a u| ≤ δ := by
    have hh := hNR i ((le_max_right _ _).trans hi) j ((le_max_right _ _).trans hj) (a,u) ⟨ha,hu⟩
    simpa only [Real.dist_eq,Function.uncurry_def] using hh.le
  have hs := rectangle_stability (h i) (h j) hA hB hδ.le (heq i) (heq j) hcb hrb z.1 hz.1 z.2 hz.2
  have hsmall : K*δ < ε := by
    have hh : (K+1)*δ=ε := by dsimp only [δ]; field_simp
    nlinarith only [hh,hδ]
  change |Q i z.1 z.2-Q j z.1 z.2| < ε
  exact hs.trans_lt hsmall

/-- Clamping to the compact offset square provides a harmless continuous
extension of its genuine uniform limit. -/
@[expose] def clip (A x : ℝ) : ℝ := max 0 (min A x)

theorem clip_continuous (A : ℝ) : Continuous (clip A) := by unfold clip; fun_prop

theorem clip_mem {A : ℝ} (hA : 0 ≤ A) (x : ℝ) : clip A x ∈ Icc 0 A :=
  ⟨le_max_left _ _,max_le hA (min_le_left _ _)⟩

theorem clip_eq {A x : ℝ} (hx : x ∈ Icc 0 A) : clip A x=x := by
  simp only [clip,min_eq_right hx.2,max_eq_right hx.1]

/-- Actual coefficient convergence constructs a continuous physical kernel
limit. Existence is derived from completeness of the real numbers. -/
theorem rectangle_limit_exists {m : ℕ} {B A : ℝ}
    {C R Q : ℕ → ℝ → ℝ → ℝ} {c r : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ∀ n,UnitData A (C n) (R n) (Q n))
    (heq : ∀ n,RectangleEquation m B A (C n) (R n) (Q n))
    (hC : TendstoUniformlyOn (fun n => Function.uncurry (C n)) (Function.uncurry c) atTop (square A))
    (hR : TendstoUniformlyOn (fun n => Function.uncurry (R n)) (Function.uncurry r) atTop (triangle A)) :
    ∃ q : ℝ → ℝ → ℝ,Continuous (Function.uncurry q) ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Q n)) (Function.uncurry q) atTop (square A) ∧
      ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|q a b| ≤ 1 := by
  classical
  have hU := rectangle_uniformCauchy hA hB h heq hC hR
  have hlim (z : ℝ × ℝ) (hz : z ∈ square A) :
      ∃ l : ℝ,Tendsto (fun n => Q n z.1 z.2) atTop (nhds l) :=
    by simpa only [Function.uncurry_def] using cauchySeq_tendsto_of_complete (hU.cauchySeq hz)
  let f (z : ℝ × ℝ) : ℝ := if hz : z ∈ square A then Classical.choose (hlim z hz) else 0
  have hf (z : ℝ × ℝ) (hz : z ∈ square A) :
      Tendsto (fun n => Q n z.1 z.2) atTop (nhds (f z)) := by
    simpa only [f,dite_eq_left hz] using Classical.choose_spec (hlim z hz)
  have hUf : TendstoUniformlyOn (fun n => Function.uncurry (Q n)) f atTop (square A) :=
    hU.tendstoUniformlyOn_of_tendsto hf
  have hfc : ContinuousOn f (square A) := hUf.continuousOn
    (Frequently.of_forall (fun n => (h n).solution_continuous.continuousOn))
  let q (a b : ℝ) := f (clip A a,clip A b)
  have hqc : Continuous (Function.uncurry q) := by
    exact hfc.comp_continuous ((clip_continuous A).comp continuous_fst |>.prodMk
      ((clip_continuous A).comp continuous_snd)) (fun z => ⟨clip_mem hA z.1,clip_mem hA z.2⟩)
  have hqe (z : ℝ × ℝ) (hz : z ∈ square A) : q z.1 z.2=f z := by
    dsimp only [q]
    rw [clip_eq hz.1,clip_eq hz.2]
  refine ⟨q,hqc,?_,?_⟩
  · exact hUf.congr_right (fun z hz => (hqe z hz).symm)
  · intro a ha b hb
    have hl := (hf (a,b) ⟨ha,hb⟩).abs
    have hbnd := le_of_tendsto hl (Eventually.of_forall (fun n => (h n).solution_bound a ha b hb))
    rw [hqe (a,b) ⟨ha,hb⟩]
    exact hbnd

/-- A uniform solution error has its genuine area bound inside the operator. -/
theorem rectangle_operator_uniform_bound {m : ℕ} {B A δ : ℝ}
    {C R Q C' R' Q' : ℝ → ℝ → ℝ}
    (h : UnitData A C R Q) (h' : UnitData A C' R' Q')
    (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hC : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|C a b-C' a b| ≤ δ)
    (hR : ∀ a ∈ Icc 0 A,∀ u ∈ Icc 0 a,|R a u-R' a u| ≤ δ)
    (hQ : ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,|Q a b-Q' a b| ≤ δ) :
    ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,
      |rectangleOperator m B C R Q a b-rectangleOperator m B C' R' Q' a b| ≤
        (coefficientFactor m B A+B*(m : ℝ)*A^2)*δ := by
  intro a ha b hb
  have hA := ha.1.trans ha.2
  have hd : Continuous (Function.uncurry (fun u v => |Q u v-Q' u v|)) := by
    convert (h.solution_continuous.sub h'.solution_continuous).abs using 1
    funext z
    rfl
  have hm := rectangle_integral_mono hd continuous_const ha.1 hb.1
    (G := fun _ _ => δ) (fun u hu v hv => hQ u ⟨hu.1,hu.2.trans ha.2⟩ v ⟨hv.1,hv.2.trans hb.2⟩)
  simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hm
  have harea : a*b ≤ A^2 := by nlinarith [mul_le_mul ha.2 hb.2 hb.1 hA]
  have hmem : (∫ u in (0 : ℝ)..a,∫ v in (0 : ℝ)..b,|Q u v-Q' u v|) ≤ A^2*δ := by
    have hh := mul_le_mul_of_nonneg_right harea hδ
    nlinarith only [hm,hh]
  have h1 := rectangle_operators_difference (m := m) h h' hB hδ hC hR a ha b hb
  have h2 := mul_le_mul_of_nonneg_left hmem (mul_nonneg hB (Nat.cast_nonneg m))
  nlinarith only [h1,h2]

/-- Passing to the actual continuous rectangle operator is justified by
its proven coefficient and solution estimates. -/
theorem rectangle_limit_equation {m : ℕ} {B A : ℝ}
    {C R Q : ℕ → ℝ → ℝ → ℝ} {c r q : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ∀ n,UnitData A (C n) (R n) (Q n))
    (hlim : UnitData A c r q)
    (heq : ∀ n,RectangleEquation m B A (C n) (R n) (Q n))
    (hC : TendstoUniformlyOn (fun n => Function.uncurry (C n)) (Function.uncurry c) atTop (square A))
    (hR : TendstoUniformlyOn (fun n => Function.uncurry (R n)) (Function.uncurry r) atTop (triangle A))
    (hQ : TendstoUniformlyOn (fun n => Function.uncurry (Q n)) (Function.uncurry q) atTop (square A)) :
    RectangleEquation m B A c r q := by
  intro a ha b hb
  have hqp := hQ.tendsto_at (x := (a,b)) ⟨ha,hb⟩
  have hop : Tendsto (fun n => rectangleOperator m B (C n) (R n) (Q n) a b)
      atTop (nhds (rectangleOperator m B c r q a b)) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    let K := coefficientFactor m B A+B*(m : ℝ)*A^2
    have hK : 0 ≤ K := add_nonneg (coefficientFactor_nonnegative m hB hA) (by positivity)
    let δ := ε/(K+1)
    have hδ : 0 < δ := div_pos hε (by linarith)
    have hc := Metric.tendstoUniformlyOn_iff.mp hC δ hδ
    have hr := Metric.tendstoUniformlyOn_iff.mp hR δ hδ
    have hq := Metric.tendstoUniformlyOn_iff.mp hQ δ hδ
    filter_upwards [hc,hr,hq] with n hnC hnR hnQ
    have hcb (x : ℝ) (hx : x ∈ Icc 0 A) (y : ℝ) (hy : y ∈ Icc 0 A) : |C n x y-c x y| ≤ δ := by
      simpa only [Real.dist_eq,Function.uncurry_def,abs_sub_comm] using (hnC (x,y) ⟨hx,hy⟩).le
    have hrb (x : ℝ) (hx : x ∈ Icc 0 A) (u : ℝ) (hu : u ∈ Icc 0 x) : |R n x u-r x u| ≤ δ := by
      simpa only [Real.dist_eq,Function.uncurry_def,abs_sub_comm] using (hnR (x,u) ⟨hx,hu⟩).le
    have hqb (x : ℝ) (hx : x ∈ Icc 0 A) (y : ℝ) (hy : y ∈ Icc 0 A) : |Q n x y-q x y| ≤ δ := by
      simpa only [Real.dist_eq,Function.uncurry_def,abs_sub_comm] using (hnQ (x,y) ⟨hx,hy⟩).le
    have hh := rectangle_operator_uniform_bound (m := m) (h n) hlim hB hδ.le hcb hrb hqb a ha b hb
    have hsmall : K*δ < ε := by
      have he : (K+1)*δ=ε := by dsimp only [δ]; field_simp
      nlinarith only [he,hδ]
    rw [Real.dist_eq]
    exact hh.trans_lt hsmall
  have he : (fun n => Q n a b)=(fun n => rectangleOperator m B (C n) (R n) (Q n) a b) := by
    funext n
    exact heq n a ha b hb
  have hqp' : Tendsto (fun n => Q n a b) atTop (nhds (q a b)) := by
    simpa only [Function.uncurry_def] using hqp
  rw [←he] at hop
  exact tendsto_nhds_unique hqp' hop

/-- Existence, the genuine limiting rectangle equation and uniqueness are
all consequences of the finite projected equations and coefficient convergence. -/
theorem rectangle_limit_exists_equation {m : ℕ} {B A : ℝ}
    {C R Q : ℕ → ℝ → ℝ → ℝ} {c r : ℝ → ℝ → ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (h : ∀ n,UnitData A (C n) (R n) (Q n))
    (hc : Continuous (Function.uncurry c)) (hr : Continuous (Function.uncurry r))
    (heq : ∀ n,RectangleEquation m B A (C n) (R n) (Q n))
    (hC : TendstoUniformlyOn (fun n => Function.uncurry (C n)) (Function.uncurry c) atTop (square A))
    (hR : TendstoUniformlyOn (fun n => Function.uncurry (R n)) (Function.uncurry r) atTop (triangle A)) :
    ∃ q : ℝ → ℝ → ℝ,UnitData A c r q ∧ RectangleEquation m B A c r q ∧
      TendstoUniformlyOn (fun n => Function.uncurry (Q n)) (Function.uncurry q) atTop (square A) ∧
      ∀ q',UnitData A c r q' → RectangleEquation m B A c r q' →
        ∀ a ∈ Icc 0 A,∀ b ∈ Icc 0 A,q' a b=q a b := by
  obtain ⟨q,hqc,hQ,hqb⟩ := rectangle_limit_exists hA hB h heq hC hR
  have hcb (a : ℝ) (ha : a ∈ Icc 0 A) (b : ℝ) (hb : b ∈ Icc 0 A) : |c a b| ≤ 1 := by
    have ht := hC.tendsto_at (x := (a,b)) ⟨ha,hb⟩
    have hh := le_of_tendsto ht.abs (Eventually.of_forall (fun n => (h n).correlation_bound a ha b hb))
    simpa only [Function.uncurry_def] using hh
  have hrb (a : ℝ) (ha : a ∈ Icc 0 A) (u : ℝ) (hu : u ∈ Icc 0 a) : |r a u| ≤ 1 := by
    have ht := hR.tendsto_at (x := (a,u)) ⟨ha,hu⟩
    have hh := le_of_tendsto ht.abs (Eventually.of_forall (fun n => (h n).response_bound a ha u hu))
    simpa only [Function.uncurry_def] using hh
  let hl : UnitData A c r q := ⟨hc,hr,hqc,hcb,hrb,hqb⟩
  have he := rectangle_limit_equation hA hB h hl heq hC hR hQ
  refine ⟨q,hl,he,hQ,?_⟩
  intro q' hq' heq'
  exact rectangle_unique hq' hl hA hB heq' he

end SphericalAging.PrefixRectangleStability
