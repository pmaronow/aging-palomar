module

public import SphericalAging.PrefixRectangleLimit
public import SphericalAging.ScalarConstraints
public import SphericalAging.UniformMultiplier
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.ContDiff.Deriv

public section

/-! The stationary response equation follows from actual translated CK rows.
FDT is deliberately a separate hypothesis in the final optional bridge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryResponseLimit
open CKSpecification CKPhysicalConsequences GreenCovariance CKKernelBounds
open UniformMultiplier ScalarConstraints PrefixRectangleStability BackwardResponse

/-- Pointwise translated coefficient limits; no equation for the limit is assumed. -/
structure TranslationLimits (d : CKData) (T : ℕ → ℝ) (c r : ℝ → ℝ) (ell : ℝ) : Prop where
  correlation : ∀ a b, 0 ≤ a → 0 ≤ b →
    Tendsto (fun n => d.C (T n+a) (T n+b)) atTop (nhds (c |a-b|))
  response : ∀ a u, 0 ≤ u → u ≤ a →
    Tendsto (fun n => d.R (T n+a) (T n+u)) atTop (nhds (r (a-u)))
  multiplier : ∀ a, 0 ≤ a →
    Tendsto (fun n => d.multiplier (T n+a)) atTop (nhds ell)

@[expose] def translatedSlope (p : ℕ) (β : ℝ) (d : CKData) (T v : ℝ) :=
  clampedResponseSlope p β d (T+v) T

@[expose] def translatedMemoryIntegrand (p : ℕ) (β : ℝ) (d : CKData) (T v u : ℝ) :=
  clampedMemory p β d (T+v) (T+u)*clampedResponse d (T+u) T

theorem translatedSlope_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T : ℝ) : Continuous (translatedSlope p β d T) :=
  (clampedResponseSlope_continuous h).comp
    ((continuous_const.add continuous_id).prodMk continuous_const)

theorem translatedMemoryIntegrand_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T v : ℝ) :
    Continuous (translatedMemoryIntegrand p β d T v) :=
  ((clampedMemory_continuous h).comp
    (continuous_const.prodMk (continuous_const.add continuous_id))).mul
    ((clampedResponse_continuous h).comp
      ((continuous_const.add continuous_id).prodMk continuous_const))

theorem translatedMemoryIntegrand_abs_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (T v u : ℝ) :
    |translatedMemoryIntegrand p β d T v u| ≤ memoryCoefficient p β := by
  have hb := physical_bounds_of_equations h
  unfold translatedMemoryIntegrand
  rw [abs_mul,abs_of_nonneg (clampedMemory_nonnegative h.spin_ge_three hb _ _)]
  exact (mul_le_of_le_one_right (clampedMemory_nonnegative h.spin_ge_three hb _ _)
    (clampedResponse_abs_le_one h hb _ _)).trans (clampedMemory_le_coefficient h hb _ _)

theorem translatedSlope_eq {p : ℕ} {β T v : ℝ} {d : CKData}
    (hT : 0 ≤ T) (hv : 0 ≤ v) :
    translatedSlope p β d T v = -d.multiplier (T+v)*d.R (T+v) T +
      ∫ u in (0 : ℝ)..v, translatedMemoryIntegrand p β d T v u := by
  have htv : T ≤ T+v := by linarith
  have hs : translatedSlope p β d T v=responseSlope p β d (T+v) T := by
    simp only [translatedSlope,clampedResponseSlope,max_eq_right hT,max_eq_left htv]
  rw [hs,responseSlope_linear_memory hT htv,clampedResponse_eq hT htv]
  congr 1
  simpa only [zero_add,add_zero,translatedMemoryIntegrand] using
    (intervalIntegral.integral_comp_add_left
      (fun z => clampedMemory p β d (T+v) z*clampedResponse d z T)
      (a := 0) (b := v) T).symm

/-- The finite translated integral row is proved by the CK derivative and FTC. -/
theorem translated_response_integral {p : ℕ} {β T t : ℝ} {d : CKData}
    (h : CKEquations p β d) (hT : 0 ≤ T) (ht : 0 ≤ t) :
    d.R (T+t) T=1+∫ v in (0 : ℝ)..t,translatedSlope p β d T v := by
  have hc : Continuous (fun v => clampedResponse d (T+v) T) :=
    (clampedResponse_continuous h).comp
      ((continuous_const.add continuous_id).prodMk continuous_const)
  have hd (v : ℝ) (hv : v ∈ Ioo 0 t) :
      HasDerivAt (fun x => clampedResponse d (T+x) T) (translatedSlope p β d T v) v := by
    have hh := (clampedResponse_hasDerivAt h hT (show T<T+v by linarith [hv.1])).comp v
      ((hasDerivAt_id v).const_add T)
    simpa only [translatedSlope,mul_one,Function.comp_def] using hh
  have hf := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hc.continuousOn hd
    ((translatedSlope_continuous h T).intervalIntegrable 0 t)
  rw [clampedResponse_eq hT (by linarith),add_zero,clampedResponse_eq hT le_rfl,
    h.response_diagonal T hT] at hf
  linarith

/-- The genuine unit and initial bounds persist under translated CK limits. -/
theorem limit_physical {p : ℕ} {β ell : ℝ} {d : CKData} {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n) (hl : TranslationLimits d T c r ell) :
    c 0=1 ∧ r 0=1 ∧ (∀ t,0 ≤ t → 0 ≤ r t ∧ r t ≤ c t ∧ c t ≤ 1) ∧
      1 ≤ ell ∧ ell ≤ multiplierCeiling p β := by
  have hb := physical_bounds_of_equations h
  have hc0 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (c 0)) := by
    simpa only [sub_self,abs_zero,add_zero,h.correlation_diagonal _ (hT _)] using
      hl.correlation 0 0 le_rfl le_rfl
  have hr0 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds (r 0)) := by
    simpa only [sub_self,add_zero,h.response_diagonal _ (hT _)] using
      hl.response 0 0 le_rfl le_rfl
  refine ⟨tendsto_nhds_unique hc0 tendsto_const_nhds,
    tendsto_nhds_unique hr0 tendsto_const_nhds,?_,?_,?_⟩
  · intro t ht
    have hr := hl.response t 0 le_rfl ht
    have hc := hl.correlation t 0 ht le_rfl
    simp only [sub_zero,abs_of_nonneg ht,add_zero] at hr hc
    refine ⟨ge_of_tendsto hr (Eventually.of_forall (fun n => hb.2 _ _ (hT n) (by linarith))),
      le_of_tendsto_of_tendsto hr hc (Eventually.of_forall (fun n =>
        response_le_correlation h (hT n) (by linarith))),
      le_of_tendsto hc (Eventually.of_forall (fun n => (hb.1 _ _ (add_nonneg (hT n) ht) (hT n)).2))⟩
  · exact ge_of_tendsto (hl.multiplier 0 le_rfl) (Eventually.of_forall (fun n => by
      simpa only [add_zero] using (multiplier_uniform_bound h hb
        (correlation_psd_of_equations h) (hT n)).1))
  · exact le_of_tendsto (hl.multiplier 0 le_rfl) (Eventually.of_forall (fun n => by
      simpa only [add_zero] using (multiplier_uniform_bound h hb
        (correlation_psd_of_equations h) (hT n)).2))

/-- Actual compact memory convergence, using the uniform CK kernel bound. -/
theorem translated_memory_tendsto {p : ℕ} {β ell v : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n) (hl : TranslationLimits d T c r ell)
    (hv : 0 ≤ v) :
    Tendsto (fun n => ∫ u in (0 : ℝ)..v,translatedMemoryIntegrand p β d (T n) v u)
      atTop (nhds (memoryCoefficient p β*causalMemory (p-2) c r v)) := by
  unfold causalMemory
  rw [←intervalIntegral.integral_const_mul]
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun _ => memoryCoefficient p β)
  · exact Eventually.of_forall (fun n =>
      (translatedMemoryIntegrand_continuous h (T n) v).aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun u _ => by
      simpa only [Real.norm_eq_abs] using translatedMemoryIntegrand_abs_bound h (T n) v u))
  · exact intervalIntegrable_const
  · apply ae_of_all
    intro u hu
    rw [uIoc_of_le hv] at hu
    have hu' : u ∈ Icc 0 v := Ioc_subset_Icc_self hu
    have hc := hl.correlation v u hv hu'.1
    have hr := hl.response v u hu'.1 hu'.2
    have hr0 := hl.response u 0 le_rfl hu'.1
    simp only [abs_of_nonneg (sub_nonneg.mpr hu'.2),sub_zero,add_zero] at hc hr hr0
    have hk : Tendsto (fun _ : ℕ => memoryCoefficient p β) atTop (nhds (memoryCoefficient p β)) := tendsto_const_nhds
    have hp := (hk.mul (hc.pow (p-2))).mul hr |>.mul hr0
    convert hp using 1
    · funext n
      unfold translatedMemoryIntegrand clampedMemory memoryCoefficient xiDoublePrime
      rw [clampedCorrelation_eq (add_nonneg (hT n) hv) (add_nonneg (hT n) hu'.1),
        clampedResponse_eq (add_nonneg (hT n) hu'.1) (add_le_add le_rfl hu'.2),
        clampedResponse_eq (hT n) (by linarith [hu'.1])]
      ring
    · congr 1
      ring

/-- The limiting slope is derived from actual finite CK rows. -/
theorem translated_slope_tendsto {p : ℕ} {β ell v : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n) (hl : TranslationLimits d T c r ell)
    (hv : 0 ≤ v) :
    Tendsto (fun n => translatedSlope p β d (T n) v) atTop
      (nhds (-ell*r v+memoryCoefficient p β*causalMemory (p-2) c r v)) := by
  have hr := hl.response v 0 le_rfl hv
  simp only [sub_zero,add_zero] at hr
  have hh := (hl.multiplier v hv).neg.mul hr |>.add (translated_memory_tendsto h hT hl hv)
  convert hh using 1
  funext n
  exact translatedSlope_eq (hT n) hv


/-- Integration of the derived limiting slope gives the actual response equation. -/
theorem stationary_response_integral {p : ℕ} {β ell t : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n) (hl : TranslationLimits d T c r ell)
    (ht : 0 ≤ t) :
    r t=1+∫ v in (0 : ℝ)..t,
      -ell*r v+memoryCoefficient p β*causalMemory (p-2) c r v := by
  have hb := physical_bounds_of_equations h
  have hI : Tendsto (fun n => ∫ v in (0 : ℝ)..t,translatedSlope p β d (T n) v) atTop
      (nhds (∫ v in (0 : ℝ)..t,-ell*r v+memoryCoefficient p β*causalMemory (p-2) c r v)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => multiplierCeiling p β+memoryCoefficient p β*t)
    · exact Eventually.of_forall (fun n => (translatedSlope_continuous h (T n)).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => ae_of_all _ (fun v hv => by
        rw [uIoc_of_le ht] at hv
        have hv' : v ∈ Icc 0 t := Ioc_subset_Icc_self hv
        have hLam := multiplier_uniform_bound h hb (correlation_psd_of_equations h)
          (add_nonneg (hT n) hv'.1)
        have hLamAbs : |d.multiplier (T n+v)| ≤ multiplierCeiling p β := by
          rw [abs_of_nonneg (by linarith [hLam.1])]
          exact hLam.2
        have he : translatedSlope p β d (T n) v=responseSlope p β d (T n+v) (T n) := by
          simp only [translatedSlope,clampedResponseSlope,max_eq_right (hT n),
            max_eq_left (show T n ≤ T n+v from by linarith [hv'.1])]
        rw [Real.norm_eq_abs,he]
        calc
          _ ≤ multiplierCeiling p β+memoryCoefficient p β*(T n+v-T n) :=
            responseSlope_abs_bound h hb (hT n) (by linarith [hv'.1]) hLamAbs
          _ ≤ multiplierCeiling p β+memoryCoefficient p β*t := by
            have hm := memoryCoefficient_nonnegative (β := β) h.spin_ge_three
            nlinarith [hv'.2]))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro v hv
      rw [uIoc_of_le ht] at hv
      exact translated_slope_tendsto h hT hl hv.1.le
  have hr := hl.response t 0 le_rfl ht
  simp only [sub_zero,add_zero] at hr
  have heq : (fun n => d.R (T n+t) (T n))=
      (fun n => 1+∫ v in (0 : ℝ)..t,translatedSlope p β d (T n) v) := by
    funext n
    exact translated_response_integral h (hT n) ht
  rw [heq] at hr
  exact tendsto_nhds_unique hr (tendsto_const_nhds.add hI)

@[expose] def stationarySlope (p : ℕ) (β ell : ℝ) (c r : ℝ → ℝ) (v : ℝ) :=
  -ell*r v+memoryCoefficient p β*causalMemory (p-2) c r v

theorem stationarySlope_continuousOn {p : ℕ} {β ell : ℝ} {c r : ℝ → ℝ}
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0)) :
    ContinuousOn (stationarySlope p β ell c r) (Ici 0) :=
  hr.const_mul (-ell) |>.add
    ((causalMemory_continuousOn (p-2) c r hc hr).const_mul (memoryCoefficient p β))

/-- FTC applied to the true limit integral equation yields the right derivative,
including the endpoint zero. No derivative of the limiting response is assumed. -/
theorem stationary_response_derivative {p : ℕ} {β ell t : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n) (hl : TranslationLimits d T c r ell)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0)) (ht : 0 ≤ t) :
    HasDerivWithinAt r
      (-ell*r t+memoryCoefficient p β*causalMemory (p-2) c r t) (Ici 0) t := by
  let f := stationarySlope p β ell c r
  have hf : Continuous (rayExtension f) :=
    rayExtension_continuous f (stationarySlope_continuousOn hc hr)
  have hd : HasDerivAt (fun v => 1+∫ u in (0 : ℝ)..v,rayExtension f u) (f t) t := by
    have hi := intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable 0 t)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
    simpa only [rayExtension_eq f t ht] using hi.const_add 1
  apply hd.hasDerivWithinAt.congr_of_mem _ ht
  intro v hv
  have hi := stationary_response_integral h hT hl hv
  rw [hi]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hv] at hu
  exact (rayExtension_eq f u hu.1).symm

/-- Only a genuine FDT derivative remains to construct the earlier scalar input.
This bridge makes that remaining assumption explicit. -/
theorem stationaryInputs_of_translation_and_fdt {p : ℕ} {β ell : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ}
    (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n) (hl : TranslationLimits d T c r ell)
    (hc : ContinuousOn c (Ici 0)) (hr : ContinuousOn r (Ici 0))
    (hFDT : ∀ t,0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t) :
    StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r := by
  have hp := limit_physical h hT hl
  refine ⟨mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _),hc,hr,hp.1,hp.2.1,hFDT,?_,?_,?_⟩
  · intro t ht
    have hd := stationary_response_derivative h hT hl hc hr ht
    have hcast : ((p-2 : ℕ) : ℝ)+1=(p : ℝ)-1 := by
      rw [Nat.cast_sub (show 2 ≤ p from by have := h.spin_ge_three; omega)]
      norm_num
      ring
    convert hd using 1
    unfold memoryCoefficient
    rw [hcast]
  · intro t ht
    exact (hp.2.2.1 t ht).1.trans (hp.2.2.1 t ht).2.1
  · intro t ht
    exact (hp.2.2.1 t ht).1


/-- Harmlessly clamp the finitely many nonphysical translation times. -/
theorem TranslationLimits.clamp {d : CKData} {T : ℕ → ℝ} {c r : ℝ → ℝ} {ell : ℝ}
    (hl : TranslationLimits d T c r ell) (hT : ∀ᶠ n in atTop,0 ≤ T n) :
    TranslationLimits d (fun n => max 0 (T n)) c r ell := by
  constructor
  · intro a b ha hb
    apply (hl.correlation a b ha hb).congr'
    filter_upwards [hT] with n hn
    simp only [max_eq_right hn]
  · intro a u hu hua
    apply (hl.response a u hu hua).congr'
    filter_upwards [hT] with n hn
    simp only [max_eq_right hn]
  · intro a ha
    apply (hl.multiplier a ha).congr'
    filter_upwards [hT] with n hn
    simp only [max_eq_right hn]

/-- The original locally uniform translated convergence supplies all pointwise inputs. -/
theorem translationLimits_of_uniform {d : CKData} {T : ℕ → ℝ} {c r : ℝ → ℝ} {ell : ℝ}
    (hC : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hLam : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n a => d.multiplier (T n+a)) (fun _ => ell) atTop (Icc 0 A)) :
    TranslationLimits d T c r ell := by
  constructor
  · intro a b ha hb
    exact (hC (max a b) (ha.trans (le_max_left _ _))).tendsto_at
      (x := (a,b)) ⟨⟨ha,le_max_left _ _⟩,⟨hb,le_max_right _ _⟩⟩
  · intro a u hu hua
    exact (hR a (hu.trans hua)).tendsto_at (x := (a,u)) ⟨⟨hu.trans hua,le_rfl⟩,hu,hua⟩
  · intro a ha
    exact (hLam a ha).tendsto_at (x := a) ⟨ha,le_rfl⟩

theorem continuousOn_ray_of_intervals {f : ℝ → ℝ}
    (hf : ∀ A,0 ≤ A → ContinuousOn f (Icc 0 A)) : ContinuousOn f (Ici 0) := by
  intro t ht
  change 0 ≤ t at ht
  apply ((hf (t+1) (by linarith)).continuousWithinAt ⟨ht,by linarith⟩).mono_of_mem_nhdsWithin
  have hN : Iio (t+1) ∈ 𝓝[Ici 0] t :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by linarith))
  exact mem_of_superset (inter_mem self_mem_nhdsWithin hN) (fun u hu => ⟨hu.1,hu.2.le⟩)

/-- Profile continuity itself is derived from the locally uniform translated limit. -/
theorem profiles_continuous_of_uniform {p : ℕ} {β : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (h : CKEquations p β d) (hT : ∀ n,0 ≤ T n)
    (hC : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A)) :
    ContinuousOn c (Ici 0) ∧ ContinuousOn r (Ici 0) := by
  constructor
  · apply continuousOn_ray_of_intervals
    intro A hA
    have hc' : TendstoUniformlyOn
        (fun n (z : ℝ × ℝ) => clampedCorrelation d (T n+z.1) (T n+z.2))
        (fun z => c |z.1-z.2|) atTop (square A) := (hC A hA).congr
      (Eventually.of_forall (fun n z hz =>
        (clampedCorrelation_eq (add_nonneg (hT n) hz.1.1) (add_nonneg (hT n) hz.2.1)).symm))
    have hc := hc'.continuousOn (Eventually.of_forall (fun n =>
      ((clampedCorrelation_continuous h).comp
        (show Continuous (fun z : ℝ × ℝ => (T n+z.1,T n+z.2)) by fun_prop)).continuousOn)).frequently
    have hr := hc.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun a (ha : a ∈ Icc 0 A) => show (a,0) ∈ square A from ⟨ha,⟨le_rfl,hA⟩⟩)
    apply hr.congr
    intro a ha
    simp only [Function.comp_def,id_eq,sub_zero,abs_of_nonneg ha.1]
  · apply continuousOn_ray_of_intervals
    intro A hA
    have hr' : TendstoUniformlyOn
        (fun n (z : ℝ × ℝ) => clampedResponse d (T n+z.1) (T n+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A) := (hR A hA).congr
      (Eventually.of_forall (fun n z hz =>
        (clampedResponse_eq (add_nonneg (hT n) hz.2.1) (add_le_add le_rfl hz.2.2)).symm))
    have hr := hr'.continuousOn (Eventually.of_forall (fun n =>
      ((clampedResponse_continuous h).comp
        (show Continuous (fun z : ℝ × ℝ => (T n+z.1,T n+z.2)) by fun_prop)).continuousOn)).frequently
    simpa only [Function.comp_def,id_eq,sub_zero] using
      hr.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun a (ha : a ∈ Icc 0 A) => show (a,0) ∈ triangle A from ⟨ha,le_rfl,ha.1⟩)

/-- Derived conclusions of the response part of Proposition 5.7.
The hypotheses of the theorem constructing this record contain only actual CK
and translated coefficient convergence, with no limiting derivative premise. -/
structure ResponseConclusions (p : ℕ) (β ell : ℝ) (c r : ℝ → ℝ) : Prop where
  continuous_c : ContinuousOn c (Ici 0)
  continuous_r : ContinuousOn r (Ici 0)
  initial_c : c 0=1
  initial_r : r 0=1
  physical : ∀ t,0 ≤ t → 0 ≤ r t ∧ r t ≤ c t ∧ c t ≤ 1
  multiplier_bounds : 1 ≤ ell ∧ ell ≤ multiplierCeiling p β
  continuous_slope : ContinuousOn (stationarySlope p β ell c r) (Ici 0)
  response_derivative : ∀ t,0 ≤ t → HasDerivWithinAt r
    (-ell*r t+memoryCoefficient p β*causalMemory (p-2) c r t) (Ici 0) t

/-- The actual late translated CK limit satisfies the stationary response
Volterra equation, its unit initial condition, and all physical bounds.
Stationarity of the coefficient limits and FDT remain separate Section 5 inputs. -/
theorem stationary_response_of_uniform_translation {p : ℕ} {β ell : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (h : CKEquations p β d) (hT : Tendsto T atTop atTop)
    (hC : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hLam : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n a => d.multiplier (T n+a)) (fun _ => ell) atTop (Icc 0 A)) :
    ResponseConclusions p β ell c r := by
  have hTe := hT.eventually (eventually_ge_atTop 0)
  let T' n := max 0 (T n)
  have hC' : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T' n+z.1) (T' n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A) := by
    intro A hA
    apply (hC A hA).congr
    filter_upwards [hTe] with n hn z hz
    simp only [T',max_eq_right hn]
  have hR' : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T' n+z.1) (T' n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A) := by
    intro A hA
    apply (hR A hA).congr
    filter_upwards [hTe] with n hn z hz
    simp only [T',max_eq_right hn]
  have hl := (translationLimits_of_uniform hC hR hLam).clamp hTe
  have ht' : ∀ n,0 ≤ T' n := fun n => le_max_left _ _
  have hcont := profiles_continuous_of_uniform h ht' hC' hR'
  have hp := limit_physical h ht' hl
  exact ⟨hcont.1,hcont.2,hp.1,hp.2.1,hp.2.2.1,hp.2.2.2,
    stationarySlope_continuousOn hcont.1 hcont.2,
    fun t ht => stationary_response_derivative h ht' hl hcont.1 hcont.2 ht⟩

theorem ResponseConclusions.derivative_zero {p : ℕ} {β ell : ℝ} {c r : ℝ → ℝ}
    (h : ResponseConclusions p β ell c r) : HasDerivWithinAt r (-ell) (Ici 0) 0 := by
  simpa only [h.initial_r,causalMemory,intervalIntegral.integral_same,mul_zero,add_zero,mul_one]
    using h.response_derivative 0 le_rfl

/-- Optional explicit FDT bridge, with no assumed response ODE. -/
theorem ResponseConclusions.stationaryInputs {p : ℕ} {β ell : ℝ} {c r : ℝ → ℝ}
    (hp : 3 ≤ p) (h : ResponseConclusions p β ell c r)
    (hFDT : ∀ t,0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t) :
    StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r := by
  refine ⟨mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _),h.continuous_c,h.continuous_r,
    h.initial_c,h.initial_r,hFDT,?_,?_,?_⟩
  · intro t ht
    have hcast : ((p-2 : ℕ) : ℝ)+1=(p : ℝ)-1 := by
      rw [Nat.cast_sub (show 2 ≤ p from by omega)]
      norm_num
      ring
    convert h.response_derivative t ht using 1
    unfold memoryCoefficient
    rw [hcast]
  · intro t ht
    exact (h.physical t ht).1.trans (h.physical t ht).2.1
  · intro t ht
    exact (h.physical t ht).1


/-- Continuous differentiability on the closed physical ray is a conclusion. -/
theorem ResponseConclusions.contDiffOn {p : ℕ} {β ell : ℝ} {c r : ℝ → ℝ}
    (h : ResponseConclusions p β ell c r) : ContDiffOn ℝ 1 r (Ici 0) := by
  apply (contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ici 0)).mpr
  constructor
  · intro t ht
    exact (h.response_derivative t ht).differentiableWithinAt
  · apply h.continuous_slope.congr
    intro t ht
    exact (h.response_derivative t ht).derivWithin (uniqueDiffOn_Ici 0 t ht)

/-- The precise stationary response formula printed in Proposition 5.7. -/
theorem ResponseConclusions.source_response_equation {p : ℕ} {β ell : ℝ} {c r : ℝ → ℝ}
    (h : ResponseConclusions p β ell c r) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt r (-ell*r t+β^2*(p : ℝ)*((p : ℝ)-1)*
      (∫ u in (0 : ℝ)..t,c (t-u)^(p-2)*r (t-u)*r u)) (Ici 0) t :=
  h.response_derivative t ht

end SphericalAging.StationaryResponseLimit
