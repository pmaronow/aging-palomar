module

public import SphericalAging.StationaryNormalization
public import SphericalAging.PlateauAlgebra
public import SphericalAging.StationaryUniqueness
public import SphericalAging.TriangleUniqueness
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

public section

/-!
# Scalar constraints from the stationary response equation

The inputs below are precisely stationary-cluster facts from Proposition 5.7.
The scalar memory equation, plateau multiplier identity and sign constraints
are derived from the response equation rather than included as hypotheses.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace SphericalAging.ScalarConstraints

@[expose] def rayExtension (f : ℝ → ℝ) (t : ℝ) : ℝ := f (max 0 t)

theorem rayExtension_continuous (f : ℝ → ℝ) (hf : ContinuousOn f (Ici 0)) :
    Continuous (rayExtension f) := hf.comp_continuous
      (continuous_const.max continuous_id) (fun t => le_max_left 0 t)

theorem rayExtension_eq (f : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) : rayExtension f t = f t := by
  simp only [rayExtension, max_eq_right ht]

@[expose] def causalMemory (n : ℕ) (c r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..t, c (t-u)^n*r (t-u)*r u

theorem extended_memory_continuous (n : ℕ) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0)) :
    Continuous (causalMemory n (rayExtension c) (rayExtension r)) := by
  have hce := rayExtension_continuous c hc
  have hre := rayExtension_continuous r hr
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
  · exact ((hce.comp (continuous_fst.sub continuous_snd)).pow n).mul
      (hre.comp (continuous_fst.sub continuous_snd)) |>.mul (hre.comp continuous_snd)
  · exact continuous_id

theorem extended_memory_eq (n : ℕ) (c r : ℝ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    causalMemory n (rayExtension c) (rayExtension r) t = causalMemory n c r t := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [rayExtension_eq c (t-u) (sub_nonneg.mpr hu.2),
    rayExtension_eq r (t-u) (sub_nonneg.mpr hu.2), rayExtension_eq r u hu.1]

theorem causalMemory_continuousOn (n : ℕ) (c r : ℝ → ℝ)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0)) :
    ContinuousOn (causalMemory n c r) (Ici 0) :=
  (extended_memory_continuous n c r hc hr).continuousOn.congr
    (fun t ht => (extended_memory_eq n c r t ht).symm)

/-- The actual regularity, FDT and response equation of a stationary cluster.
The generic exponent is `p-2` and the coefficient is `beta^2*p` in the manuscript. -/
structure StationaryInputs (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ) : Prop where
  coefficient_nonnegative : 0 ≤ B
  continuous_c : ContinuousOn c (Ici 0)
  continuous_r : ContinuousOn r (Ici 0)
  initial_c : c 0 = 1
  initial_r : r 0 = 1
  correlation_derivative : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t
  response_derivative : ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt r
    (-ell*r t+B*((n:ℝ)+1)*causalMemory n c r t) (Ici 0) t
  correlation_nonnegative : ∀ t : ℝ, 0 ≤ t → 0 ≤ c t
  response_nonnegative : ∀ t : ℝ, 0 ≤ t → 0 ≤ r t

theorem causalMemory_nonnegative (n : ℕ) (c r : ℝ → ℝ)
    (hc : ∀ t : ℝ, 0 ≤ t → 0 ≤ c t) (hr : ∀ t : ℝ, 0 ≤ t → 0 ≤ r t)
    (t : ℝ) (ht : 0 ≤ t) : 0 ≤ causalMemory n c r t := by
  apply intervalIntegral.integral_nonneg ht
  intro u hu
  exact mul_nonneg (mul_nonneg (pow_nonneg (hc _ (sub_nonneg.mpr hu.2)) _)
    (hr _ (sub_nonneg.mpr hu.2))) (hr _ hu.1)

theorem stationary_response_exponential_lower (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    Real.exp (-ell*t) ≤ r t := by
  have hder (v : ℝ) (hv : v ∈ Ico 0 t) :
      HasDerivWithinAt (fun u => -r u)
        (-(-ell*r v+B*((n:ℝ)+1)*causalMemory n c r v)) (Ici v) v :=
    (h.response_derivative v hv.1).neg.mono (Ici_subset_Ici.mpr hv.1)
  have hbound := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun v => -r v)
    (f' := fun v => -(-ell*r v+B*((n:ℝ)+1)*causalMemory n c r v))
    (δ := -1) (K := -ell) (ε := 0)
    (h.continuous_r.neg.mono Icc_subset_Ici_self)
    (fun v hv a ha => (hder v hv).liminf_right_slope_le ha)
    (show -r 0 ≤ -1 by simp [h.initial_r])
    (fun v hv => by
      have hmemory := causalMemory_nonnegative n c r
        h.correlation_nonnegative h.response_nonnegative v hv.1
      have hmul : 0 ≤ B*((n:ℝ)+1)*causalMemory n c r v :=
        mul_nonneg (mul_nonneg h.coefficient_nonnegative (by positivity)) hmemory
      nlinarith only [hmul])
  have hb := hbound t ⟨ht,le_rfl⟩
  simp only [gronwallBound_ε0, sub_zero, neg_one_mul] at hb
  linarith

theorem stationary_response_positive (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) : 0 < r t :=
  lt_of_lt_of_le (Real.exp_pos _) (stationary_response_exponential_lower n B ell c r h t ht)

theorem stationary_integral_response (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    (∫ u in 0..t, r u) = 1-c t := by
  have hi : IntervalIntegrable (fun u => -r u) volume 0 t :=
    (show ContinuousOn (fun u => -r u) (uIcc 0 t) by
      rw [uIcc_of_le ht]; exact h.continuous_r.neg.mono Icc_subset_Ici_self).intervalIntegrable
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (h.continuous_c.mono Icc_subset_Ici_self)
    (fun u hu => (h.correlation_derivative u hu.1.le).hasDerivAt (Ici_mem_nhds hu.1)) hi
  rw [intervalIntegral.integral_neg, h.initial_c] at hft
  linarith

theorem stationary_integrated_response_equation (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    r t-1 = -ell*(1-c t)+B*((n:ℝ)+1)*∫ v in 0..t, causalMemory n c r v := by
  have hrint : IntervalIntegrable r volume 0 t :=
    (show ContinuousOn r (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact h.continuous_r.mono Icc_subset_Ici_self).intervalIntegrable
  have hMint : IntervalIntegrable (causalMemory n c r) volume 0 t :=
    (show ContinuousOn (causalMemory n c r) (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact (causalMemory_continuousOn n c r h.continuous_c h.continuous_r).mono
        Icc_subset_Ici_self).intervalIntegrable
  have hi := (hrint.const_mul (-ell)).add (hMint.const_mul (B*((n:ℝ)+1)))
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    (h.continuous_r.mono Icc_subset_Ici_self)
    (fun u hu => (h.response_derivative u hu.1.le).hasDerivAt (Ici_mem_nhds hu.1)) hi
  rw [h.initial_r, intervalIntegral.integral_add (hrint.const_mul (-ell))
    (hMint.const_mul (B*((n:ℝ)+1))), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul, stationary_integral_response n B ell c r h t ht] at hft
  exact hft.symm

theorem stationary_power_integral (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    ((n:ℝ)+1)*(∫ w in 0..t, c w^n*r w) = 1-c t^(n+1) := by
  have hpow (w : ℝ) (hw : 0 ≤ w) :
      HasDerivWithinAt (fun v => c v^(n+1))
        (-((n:ℝ)+1)*(c w^n*r w)) (Ici 0) w := by
    convert (h.correlation_derivative w hw).pow (n+1) using 1
    simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    ring
  have hf : ContinuousOn (fun w => c w^n*r w) (Ici 0) := h.continuous_c.pow n |>.mul h.continuous_r
  have hi : IntervalIntegrable (fun w => -((n:ℝ)+1)*(c w^n*r w)) volume 0 t :=
    (show ContinuousOn (fun w => -((n:ℝ)+1)*(c w^n*r w)) (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact hf.const_mul _ |>.mono Icc_subset_Ici_self).intervalIntegrable
  have hft := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht
    ((h.continuous_c.pow (n+1)).mono Icc_subset_Ici_self)
    (fun w hw => (hpow w hw.1.le).hasDerivAt (Ici_mem_nhds hw.1)) hi
  simp only [Pi.pow_apply] at hft
  rw [intervalIntegral.integral_const_mul, h.initial_c, one_pow] at hft
  linarith

@[expose] def powerMemory (n : ℕ) (c r : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ u in 0..t, c (t-u)^(n+1)*r u

theorem stationary_memory_integrated (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    ((n:ℝ)+1)*(∫ v in 0..t, causalMemory n c r v) = 1-c t-powerMemory n c r t := by
  let ce := rayExtension c
  let re := rayExtension r
  have hce : Continuous ce := rayExtension_continuous c h.continuous_c
  have hre : Continuous re := rayExtension_continuous r h.continuous_r
  have hF : Continuous (fun z : ℝ × ℝ => ce (z.1-z.2)^n*re (z.1-z.2)*re z.2) :=
    ((hce.comp (continuous_fst.sub continuous_snd)).pow n).mul
      (hre.comp (continuous_fst.sub continuous_snd)) |>.mul (hre.comp continuous_snd)
  have hswap := TriangleUniqueness.standard_triangle_integral_swap
    (F := fun v u => ce (v-u)^n*re (v-u)*re u) hF ht
  have hactual : (∫ v in 0..t, causalMemory n c r v) =
      ∫ v in 0..t, ∫ u in 0..v, ce (v-u)^n*re (v-u)*re u := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le ht] at hv
    exact (extended_memory_eq n c r v hv.1).symm
  have hinner (u : ℝ) (hu : u ∈ Icc 0 t) :
      ((n:ℝ)+1)*(∫ v in u..t, ce (v-u)^n*re (v-u)*re u) =
        r u*(1-c (t-u)^(n+1)) := by
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_comp_sub_right (fun v => ce v^n*re v) u, sub_self]
    have heq : (∫ w in 0..(t-u), ce w^n*re w) = ∫ w in 0..(t-u), c w^n*r w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [uIcc_of_le (sub_nonneg.mpr hu.2)] at hw
      dsimp only [ce, re]
      rw [rayExtension_eq c w hw.1, rayExtension_eq r w hw.1]
    rw [heq, show re u = r u from rayExtension_eq r u hu.1]
    have hi := stationary_power_integral n B ell c r h (t-u) (sub_nonneg.mpr hu.2)
    have him := congrArg (fun x : ℝ => x*r u) hi
    nlinarith only [him]
  have heq : ((n:ℝ)+1)*(∫ v in 0..t, causalMemory n c r v) =
      ∫ u in 0..t, r u*(1-c (t-u)^(n+1)) := by
    rw [hactual, hswap, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    exact hinner u hu
  have hrint : IntervalIntegrable r volume 0 t :=
    (show ContinuousOn r (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact h.continuous_r.mono Icc_subset_Ici_self).intervalIntegrable
  have hmaps : MapsTo (fun u : ℝ => t-u) (Icc 0 t) (Ici 0) := fun u hu => sub_nonneg.mpr hu.2
  have hmcont : ContinuousOn (fun u => c (t-u)^(n+1)*r u) (Icc 0 t) :=
    ((h.continuous_c.comp (continuous_const.sub continuous_id).continuousOn hmaps).pow (n+1)).mul
      (h.continuous_r.mono Icc_subset_Ici_self)
  have hmInt : IntervalIntegrable (fun u => c (t-u)^(n+1)*r u) volume 0 t :=
    (show ContinuousOn (fun u => c (t-u)^(n+1)*r u) (uIcc 0 t) by
      simpa only [uIcc_of_le ht] using hmcont).intervalIntegrable
  calc
    _ = ∫ u in 0..t, r u*(1-c (t-u)^(n+1)) := heq
    _ = ∫ u in 0..t, r u-c (t-u)^(n+1)*r u := by
      apply intervalIntegral.integral_congr
      intro u _
      dsimp only
      ring
    _ = (∫ u in 0..t, r u)-(∫ u in 0..t, c (t-u)^(n+1)*r u) :=
      intervalIntegral.integral_sub hrint hmInt
    _ = _ := by rw [stationary_integral_response n B ell c r h t ht]; rfl

/-- The scalar memory equation is derived from the stationary response system. -/
theorem stationary_scalar_memory (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    -r t = -1+∫ u in 0..t, (ell-B+B*c (t-u)^(n+1))*r u := by
  have hresp := stationary_integrated_response_equation n B ell c r h t ht
  have hmemory := stationary_memory_integrated n B ell c r h t ht
  have hmaps : MapsTo (fun u : ℝ => t-u) (Icc 0 t) (Ici 0) := fun u hu => sub_nonneg.mpr hu.2
  have hrint : IntervalIntegrable r volume 0 t :=
    (show ContinuousOn r (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact h.continuous_r.mono Icc_subset_Ici_self).intervalIntegrable
  have hmInt : IntervalIntegrable (fun u => c (t-u)^(n+1)*r u) volume 0 t :=
    (show ContinuousOn (fun u => c (t-u)^(n+1)*r u) (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact ((h.continuous_c.comp (continuous_const.sub continuous_id).continuousOn hmaps).pow
        (n+1)).mul (h.continuous_r.mono Icc_subset_Ici_self)).intervalIntegrable
  have heq : (∫ u in 0..t, (ell-B+B*c (t-u)^(n+1))*r u) =
      (ell-B)*(1-c t)+B*powerMemory n c r t := by
    calc
      _ = ∫ u in 0..t, (ell-B)*r u+B*(c (t-u)^(n+1)*r u) := by
        apply intervalIntegral.integral_congr
        intro u _
        dsimp only
        ring
      _ = (ell-B)*(∫ u in 0..t, r u)+B*(∫ u in 0..t, c (t-u)^(n+1)*r u) := by
        rw [intervalIntegral.integral_add (hrint.const_mul (ell-B)) (hmInt.const_mul B),
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = _ := by rw [stationary_integral_response n B ell c r h t ht]; rfl
  rw [heq]
  have hmB := congrArg (fun x : ℝ => B*x) hmemory
  nlinarith only [hresp, hmB]

/-- A bounded kernel approaching a constant has the expected causal-memory
limit against any integrable response. The whole-past limit is proved by
dominated convergence, including the moving upper integration limit. -/
theorem bounded_causal_integral_tendsto (f g : ℝ → ℝ) (q M : ℝ)
    (hf : ContinuousOn f (Ici 0)) (hg : IntegrableOn g (Ioi 0))
    (hbound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M) (hlim : Tendsto f atTop (𝓝 q)) :
    Tendsto (fun t => ∫ u in 0..t, f (t-u)*g u) atTop
      (𝓝 (q*(∫ u in Ioi 0, g u))) := by
  let F : ℝ → ℝ → ℝ := fun t u => if u ≤ t then rayExtension f (t-u)*g u else 0
  have hfe := rayExtension_continuous f hf
  have hM : 0 ≤ M := (abs_nonneg (f 0)).trans (hbound 0 (le_refl 0))
  have hFm (t : ℝ) : AEStronglyMeasurable (F t) (volume.restrict (Ioi 0)) := by
    have hh : AEStronglyMeasurable (fun u => rayExtension f (t-u)*g u)
        (volume.restrict (Ioi 0)) :=
      ((hfe.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
      (μ := volume.restrict (Ioi 0))).mul hg.aestronglyMeasurable
    have hind := hh.indicator (s := Iic t) measurableSet_Iic
    convert hind using 1
    ext u
    simp only [F, Set.indicator, mem_Iic]
  have hFb (t u : ℝ) : ‖F t u‖ ≤ M*‖g u‖ := by
    dsimp only [F]
    split_ifs with hut
    · rw [Real.norm_eq_abs, abs_mul, rayExtension_eq f (t-u) (sub_nonneg.mpr hut), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hbound _ (sub_nonneg.mpr hut)) (abs_nonneg _)
    · simpa using mul_nonneg hM (norm_nonneg (g u))
  have hFlim (u : ℝ) : Tendsto (fun t => F t u) atTop (𝓝 (q*g u)) := by
    have hshift : Tendsto (fun t : ℝ => t-u) atTop atTop := by
      simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-u) tendsto_id
    apply ((hlim.comp hshift).mul_const (g u)).congr'
    filter_upwards [eventually_ge_atTop u] with t ht
    simp only [F, ite_eq_left ht, rayExtension_eq f (t-u) (sub_nonneg.mpr ht), Function.comp_apply]
  have hdct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Ioi 0)) (F := F) (f := fun u => q*g u) (fun u => M*‖g u‖)
    (Filter.Eventually.of_forall hFm)
    (Filter.Eventually.of_forall (fun t => Filter.Eventually.of_forall (hFb t)))
    (hg.norm.const_mul M) (Filter.Eventually.of_forall hFlim)
  rw [integral_const_mul] at hdct
  apply hdct.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  rw [intervalIntegral.integral_of_le ht]
  have hind : (∫ u in Ioi 0, F t u) =
      ∫ u in Iic t, rayExtension f (t-u)*g u ∂volume.restrict (Ioi 0) := by
    rw [← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun u => by simp [F, Set.indicator])
  rw [hind, Measure.restrict_restrict measurableSet_Iic,
    show Iic t ∩ Ioi (0:ℝ) = Ioc 0 t by ext u; simp [and_comm]]
  apply setIntegral_congr_fun measurableSet_Ioc
  intro u hu
  dsimp only
  rw [rayExtension_eq f (t-u) (sub_nonneg.mpr hu.2)]

theorem integrable_ray_limit_zero (f : ℝ → ℝ) (a : ℝ)
    (hf : IntegrableOn f (Ioi 0)) (hlim : Tendsto f atTop (𝓝 a)) : a = 0 := by
  apply IntegrableAtFilter.eq_zero_of_tendsto (μ := volume)
    (show IntegrableAtFilter f atTop volume from ⟨Ioi 0, Ioi_mem_atTop 0, hf⟩) _ hlim
  intro s hs
  obtain ⟨b, hb⟩ := mem_atTop_sets.mp hs
  rw [← top_le_iff, ← Real.volume_Ici (a := b)]
  exact measure_mono hb

@[expose] def scalarPhi (n : ℕ) (B ell : ℝ) (y : ℝ) : ℝ := ell-B+B*y^(n+1)

@[expose] def signPolynomial (n : ℕ) (B ell : ℝ) (y : ℝ) : ℝ := scalarPhi n B ell y*(1-y)-1

theorem stationary_plateau_identity (n : ℕ) (B ell q : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r)
    (hc1 : ∀ t : ℝ, 0 ≤ t → c t ≤ 1)
    (hrint : IntegrableOn r (Ioi 0)) (hrmass : (∫ u in Ioi 0, r u) = 1-q)
    (hlim : Tendsto c atTop (𝓝 q)) : scalarPhi n B ell q*(1-q) = 1 := by
  let f : ℝ → ℝ := fun t => scalarPhi n B ell (c t)
  have hf : ContinuousOn f (Ici 0) := by
    exact continuousOn_const.add ((h.continuous_c.pow (n+1)).const_mul B)
  have hfb (t : ℝ) (ht : 0 ≤ t) : |f t| ≤ |ell-B|+B := by
    have hpow : 0 ≤ c t^(n+1) := pow_nonneg (h.correlation_nonnegative t ht) _
    have hpow1 : c t^(n+1) ≤ 1 := pow_le_one₀ (h.correlation_nonnegative t ht) (hc1 t ht)
    dsimp [f, scalarPhi]
    calc
      _ ≤ |ell-B|+|B*c t^(n+1)| := abs_add_le _ _
      _ = |ell-B|+B*c t^(n+1) := by
        rw [abs_of_nonneg (mul_nonneg h.coefficient_nonnegative hpow)]
      _ ≤ _ := by nlinarith [h.coefficient_nonnegative]
  have hflim : Tendsto f atTop (𝓝 (scalarPhi n B ell q)) :=
    tendsto_const_nhds.add ((hlim.pow (n+1)).const_mul B)
  have hmemlim := bounded_causal_integral_tendsto f r (scalarPhi n B ell q) (|ell-B|+B)
    hf hrint hfb hflim
  rw [hrmass] at hmemlim
  have hrzero : 1-scalarPhi n B ell q*(1-q) = 0 := by
    apply integrable_ray_limit_zero r _ hrint
    apply (tendsto_const_nhds.sub hmemlim).congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    have hm := stationary_scalar_memory n B ell c r h t ht
    change 1-(∫ u in 0..t, (ell-B+B*c (t-u)^(n+1))*r u) = r t
    linarith
  linarith

theorem stationary_multiplier (n : ℕ) (B ell q : ℝ)
    (hq : q < 1) (hplateau : scalarPhi n B ell q*(1-q) = 1) :
    ell = 1/(1-q)+B*(1-q^(n+1)) := by
  have hne : 1-q ≠ 0 := by linarith
  unfold scalarPhi at hplateau
  apply (mul_right_cancel₀ hne)
  field_simp
  nlinarith only [hplateau]

theorem stationary_sign_at_profile (n : ℕ) (B ell : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (t : ℝ) (ht : 0 ≤ t) :
    signPolynomial n B ell (c t) ≤ -r t := by
  have hrpos := stationary_response_positive n B ell c r h
  have hanti := StationaryNormalization.stationaryProfile_strictAntiOn c r
    h.continuous_c h.correlation_derivative hrpos
  have hrint : IntervalIntegrable r volume 0 t :=
    (show ContinuousOn r (uIcc 0 t) by
      rw [uIcc_of_le ht]
      exact h.continuous_r.mono Icc_subset_Ici_self).intervalIntegrable
  have hmaps : MapsTo (fun u : ℝ => t-u) (Icc 0 t) (Ici 0) :=
    fun u hu => sub_nonneg.mpr hu.2
  have hmemcont : ContinuousOn (fun u => scalarPhi n B ell (c (t-u))*r u) (Icc 0 t) :=
    (continuousOn_const.add (((h.continuous_c.comp
      (continuous_const.sub continuous_id).continuousOn hmaps).pow (n+1)).const_mul B)).mul
        (h.continuous_r.mono Icc_subset_Ici_self)
  have hmInt : IntervalIntegrable (fun u => scalarPhi n B ell (c (t-u))*r u) volume 0 t :=
    (show ContinuousOn (fun u => scalarPhi n B ell (c (t-u))*r u) (uIcc 0 t) by
      simpa only [uIcc_of_le ht] using hmemcont).intervalIntegrable
  have hbound : scalarPhi n B ell (c t)*(∫ u in 0..t, r u) ≤
      ∫ u in 0..t, scalarPhi n B ell (c (t-u))*r u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on ht (hrint.const_mul _) hmInt
    intro u hu
    have hct : c t ≤ c (t-u) := hanti.antitoneOn (sub_nonneg.mpr hu.2) ht (by linarith [hu.1])
    apply mul_le_mul_of_nonneg_right _ (h.response_nonnegative u hu.1)
    dsimp [scalarPhi]
    exact add_le_add le_rfl
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (h.correlation_nonnegative t ht) hct _)
        h.coefficient_nonnegative)
  rw [stationary_integral_response n B ell c r h t ht] at hbound
  have hscalar := stationary_scalar_memory n B ell c r h t ht
  change -r t = -1+(∫ u in 0..t, scalarPhi n B ell (c (t-u))*r u) at hscalar
  dsimp [signPolynomial]
  linarith

theorem stationary_sign_strict (n : ℕ) (B ell q : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r) (hlim : Tendsto c atTop (𝓝 q))
    (y : ℝ) (hyq : q < y) (hy1 : y < 1) : signPolynomial n B ell y < 0 := by
  have hty : ∀ᶠ t in atTop, c t < y := hlim.eventually (gt_mem_nhds hyq)
  obtain ⟨T, hT, hcT⟩ := ((eventually_ge_atTop (0:ℝ)).and hty).exists
  obtain ⟨t, ht, hvalue⟩ := intermediate_value_Icc' hT
    (h.continuous_c.mono Icc_subset_Ici_self)
    (show y ∈ Icc (c T) (c 0) by rw [h.initial_c]; exact ⟨hcT.le,hy1.le⟩)
  rw [← hvalue]
  exact lt_of_le_of_lt (stationary_sign_at_profile n B ell c r h t ht.1)
    (neg_neg_of_pos (stationary_response_positive n B ell c r h t ht.1))

theorem signPolynomial_hasDerivAt (n : ℕ) (B ell q : ℝ) :
    HasDerivAt (signPolynomial n B ell)
      (B*((n:ℝ)+1)*q^n*(1-q)-scalarPhi n B ell q) q := by
  have hp := (((hasDerivAt_id q).pow (n+1)).const_mul B).const_add (ell-B)
  have h := (hp.mul ((hasDerivAt_const q (1:ℝ)).sub (hasDerivAt_id q))).sub_const 1
  convert h using 1
  · unfold signPolynomial scalarPhi
    ext y
    simp only [Pi.mul_apply, Pi.sub_apply, Pi.pow_apply, id_eq]
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one, Pi.sub_apply,
      Pi.pow_apply, id_eq]
    unfold scalarPhi
    ring

theorem sign_implies_submarginality (n : ℕ) (B ell q : ℝ) (hq : q < 1)
    (hplateau : scalarPhi n B ell q*(1-q) = 1)
    (hstrict : ∀ y : ℝ, q < y → y < 1 → signPolynomial n B ell y < 0) :
    B*((n:ℝ)+1)*q^n*(1-q)^2 ≤ 1 := by
  have hzero : signPolynomial n B ell q = 0 := by dsimp [signPolynomial]; linarith
  have hslope := (signPolynomial_hasDerivAt n B ell q).tendsto_slope.mono_left
    (nhdsGT_le_nhdsNE q)
  have hdnonpos : B*((n:ℝ)+1)*q^n*(1-q)-scalarPhi n B ell q ≤ 0 := by
    apply le_of_tendsto hslope
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds hq).filter_mono nhdsWithin_le_nhds] with y hyq hy1
    rw [slope_def_field, hzero, sub_zero]
    exact div_nonpos_of_nonpos_of_nonneg (hstrict y hyq hy1).le (sub_nonneg.mpr hyq.le)
  have hmul := mul_nonpos_of_nonpos_of_nonneg hdnonpos (sub_nonneg.mpr hq.le)
  nlinarith only [hmul, hplateau]

structure ScalarConclusions (n : ℕ) (B ell q : ℝ) (c r : ℝ → ℝ) : Prop where
  response_positive : ∀ t : ℝ, 0 ≤ t → 0 < r t
  scalar_equation : ∀ t : ℝ, 0 ≤ t →
    -r t = -1+∫ u in 0..t, scalarPhi n B ell (c (t-u))*r u
  plateau_range : 0 ≤ q ∧ q < 1
  plateau_identity : scalarPhi n B ell q*(1-q) = 1
  multiplier_identity : ell = 1/(1-q)+B*(1-q^(n+1))
  sign_at_plateau : signPolynomial n B ell q = 0
  strict_sign : ∀ y : ℝ, q < y → y < 1 → signPolynomial n B ell y < 0
  submarginality : B*((n:ℝ)+1)*q^n*(1-q)^2 ≤ 1

/-- Complete scalar-constraints proposition from the actual stationary inputs. -/
theorem scalar_constraints_from_stationary (n : ℕ) (B ell q : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs n B ell c r)
    (hc1 : ∀ t : ℝ, 0 ≤ t → c t ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrint : IntegrableOn r (Ioi 0)) (hrmass : (∫ u in Ioi 0, r u) = 1-q)
    (hlim : Tendsto c atTop (𝓝 q)) : ScalarConclusions n B ell q c r := by
  have hp := stationary_plateau_identity n B ell q c r h hc1 hrint hrmass hlim
  have hs := stationary_sign_strict n B ell q c r h hlim
  exact ⟨stationary_response_positive n B ell c r h,
    stationary_scalar_memory n B ell c r h, ⟨hq0,hq1⟩, hp,
    stationary_multiplier n B ell q hq1 hp,
    (by dsimp [signPolynomial]; linarith), hs,
    sign_implies_submarginality n B ell q hq1 hp hs⟩

/-- Proposition 6.1 in expanded pure-model notation, including the actual
one-sided derivative, multiplier, strict sign and submarginality conclusion. -/
theorem pure_scalar_constraints (p : ℕ) (hp : 3 ≤ p) (β ell q : ℝ) (c r : ℝ → ℝ)
    (h : StationaryInputs (p-2) (β^2*(p:ℝ)) ell c r)
    (hc1 : ∀ t : ℝ, 0 ≤ t → c t ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hrint : IntegrableOn r (Ioi 0)) (hrmass : (∫ u in Ioi 0, r u) = 1-q)
    (hlim : Tendsto c atTop (𝓝 q)) :
    (∀ t : ℝ, 0 ≤ t → 0 < r t ∧
      derivWithin c (Ici 0) t = -1+∫ u in 0..t,
        (ell-β^2*(p:ℝ)+β^2*(p:ℝ)*c (t-u)^(p-1))*r u) ∧
    (0 ≤ q ∧ q < 1) ∧
    (ell-β^2*(p:ℝ)+β^2*(p:ℝ)*q^(p-1))*(1-q) = 1 ∧
    ell = PlateauAlgebra.multiplier p β q ∧
    PlateauAlgebra.scalarSignPolynomial p β ell q = 0 ∧
    (∀ y : ℝ, q < y → y < 1 → PlateauAlgebra.scalarSignPolynomial p β ell y < 0) ∧
    β^2*(p:ℝ)*((p:ℝ)-1)*q^(p-2)*(1-q)^2 ≤ 1 := by
  have hs := scalar_constraints_from_stationary (p-2) (β^2*(p:ℝ)) ell q c r
    h hc1 hq0 hq1 hrint hrmass hlim
  have hnat : p-2+1 = p-1 := by omega
  have hcast : ((p-2:ℕ):ℝ)+1 = (p:ℝ)-1 := by
    rw [Nat.cast_sub (by omega : 2 ≤ p)]
    norm_num
    ring
  have hphi (y : ℝ) : scalarPhi (p-2) (β^2*(p:ℝ)) ell y =
      ell-β^2*(p:ℝ)+β^2*(p:ℝ)*y^(p-1) := by simp only [scalarPhi, hnat]
  have hsign (y : ℝ) : signPolynomial (p-2) (β^2*(p:ℝ)) ell y =
      PlateauAlgebra.scalarSignPolynomial p β ell y := by
    rw [signPolynomial, hphi]
    unfold PlateauAlgebra.scalarSignPolynomial
    ring
  refine ⟨?_,hs.plateau_range,?_,?_,?_,?_,?_⟩
  · intro t ht
    refine ⟨hs.response_positive t ht,?_⟩
    rw [(h.correlation_derivative t ht).derivWithin
      ((uniqueDiffWithinAt_Ici t).mono (Ici_subset_Ici.mpr ht))]
    simpa only [scalarPhi, hnat] using hs.scalar_equation t ht
  · simpa only [hphi] using hs.plateau_identity
  · simpa only [PlateauAlgebra.multiplier, hnat] using hs.multiplier_identity
  · simpa only [hsign] using hs.sign_at_plateau
  · intro y hyq hy1
    simpa only [hsign] using hs.strict_sign y hyq hy1
  · simpa only [hcast] using hs.submarginality

end SphericalAging.ScalarConstraints
