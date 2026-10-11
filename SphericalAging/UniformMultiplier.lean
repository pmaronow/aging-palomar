module

public import SphericalAging.EnergyTradeoff
public import SphericalAging.CKKernelBounds
public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Topology.Order.IsLUB

public section

/-! The sharp uniform multiplier bound from the actual energy-response
tradeoff, positive CK memory, and a supremum argument. -/

noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal

namespace SphericalAging.UniformMultiplier
open CKSpecification GreenCovariance BackwardResponse EnergyTradeoff

@[expose] def multiplierCeiling (p : ℕ) (β : ℝ) : ℝ := (1+Real.sqrt (1+4*β^2*(p : ℝ)^3))/2

@[expose] def multiplierSup (d : CKData) : ℝ := sSup (range (fun t : ℝ≥0 => d.multiplier t))

theorem multiplier_ge_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ d.multiplier t := by
  have hm : 0 ≤ memoryMass p d t := by
    unfold memoryMass
    exact intervalIntegral.integral_nonneg ht (fun u hu =>
      mul_nonneg (pow_nonneg (hb.1 t u ht hu.1).1 _) (hb.2 t u hu.1 hu.2))
  rw [h.multiplier_eq t ht]
  exact le_add_of_nonneg_right (mul_nonneg
    (mul_nonneg (sq_nonneg β) (sq_nonneg (p : ℝ))) hm)

theorem multiplier_range_bddAbove {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d) :
    BddAbove (range (fun t : ℝ≥0 => d.multiplier t)) := by
  refine ⟨1+Real.sqrt (β^2*(p : ℝ)^3), ?_⟩
  rintro _ ⟨t,rfl⟩
  exact multiplier_first_upper_bound h hPSD t.coe_nonneg

theorem multiplier_le_sup {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d)
    {t : ℝ} (ht : 0 ≤ t) : d.multiplier t ≤ multiplierSup d :=
  le_csSup (multiplier_range_bddAbove h hPSD) ⟨⟨t,ht⟩,rfl⟩

theorem multiplierSup_ge_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hPSD : PositiveSemidefiniteCorrelation d) :
    1 ≤ multiplierSup d := by
  simpa only [multiplier_zero h] using multiplier_le_sup h hPSD (t := 0) le_rfl

theorem response_exponential_lower {p : ℕ} {β M : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hM : ∀ t : ℝ, 0 ≤ t → d.multiplier t ≤ M) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : Real.exp (-M*(t-s)) ≤ d.R t s := by
  have hc : ContinuousOn (fun v => -d.R v s) (Icc s t) := by
    have hcont : Continuous (fun v : ℝ => clampedResponse d v s) :=
      (clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const)
    apply hcont.neg.continuousOn.congr
    intro v hv
    change -d.R v s = -clampedResponse d v s
    rw [clampedResponse_eq hs hv.1]
  have hd (v : ℝ) (hv : v ∈ Ico s t) :
      HasDerivWithinAt (fun u => -d.R u s) (-responseSlope p β d v s) (Ici v) v :=
    (h.response_derivative v s hs hv.1).neg.mono (Ici_subset_Ici.mpr hv.1)
  have hbound := le_gronwallBound_of_liminf_deriv_right_le
    (f := fun v => -d.R v s) (f' := fun v => -responseSlope p β d v s)
    (δ := -1) (K := -M) (ε := 0) hc
    (fun v hv a ha => (hd v hv).liminf_right_slope_le ha)
    (show -d.R s s ≤ -1 by rw [h.response_diagonal s hs])
    (fun v hv => by
      rw [responseSlope_linear_memory hs hv.1]
      rw [clampedResponse_eq hs hv.1]
      have hi : 0 ≤ ∫ u in s..v, clampedMemory p β d v u*clampedResponse d u s :=
        intervalIntegral.integral_nonneg hv.1 (fun u _ =>
          mul_nonneg (clampedMemory_nonnegative h.spin_ge_three hb v u)
            (clampedResponse_nonnegative hb u s))
      have hm := mul_le_mul_of_nonneg_right (hM v (hs.trans hv.1)) (hb.2 v s hs hv.1)
      nlinarith only [hi,hm])
  have hh := hbound t ⟨hst,le_rfl⟩
  simp only [gronwallBound_ε0,neg_one_mul] at hh
  linarith

theorem integral_exponential_response_square {M t : ℝ} (hM : 0 < M) (ht : 0 ≤ t) :
    (∫ u in (0 : ℝ)..t, Real.exp (-2*M*(t-u))) =
      (1-Real.exp (-2*M*t))/(2*M) := by
  let F : ℝ → ℝ := fun u => Real.exp (-2*M*(t-u))/(2*M)
  have hF : Continuous F := by fun_prop
  have hd (u : ℝ) : HasDerivAt F (Real.exp (-2*M*(t-u))) u := by
    convert (((hasDerivAt_id u).const_sub t).const_mul (-2*M)).exp.div_const (2*M) using 1
    · ext x
      dsimp [F]
    · dsimp
      field_simp [hM.ne']
  have hi : IntervalIntegrable (fun u => Real.exp (-2*M*(t-u))) volume 0 t :=
    (show Continuous (fun u => Real.exp (-2*M*(t-u))) by fun_prop).intervalIntegrable 0 t
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht hF.continuousOn
    (fun u _ => hd u) hi
  simpa only [F,sub_self,mul_zero,Real.exp_zero,sub_zero,div_sub_div_same] using hh

theorem response_square_mass_lower {p : ℕ} {β M : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (hM : 1 ≤ M)
    (hbound : ∀ t : ℝ, 0 ≤ t → d.multiplier t ≤ M) {t : ℝ} (ht : 0 ≤ t) :
    1 ≤ M*(d.R t 0 ^ 2+2*(∫ u in (0 : ℝ)..t, d.R t u ^ 2)) := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hsq (u : ℝ) (hu : u ∈ Icc 0 t) :
      Real.exp (-2*M*(t-u)) ≤ d.R t u ^ 2 := by
    have hh := response_exponential_lower h hb hbound hu.1 hu.2
    have he : Real.exp (-M*(t-u)) ^ 2 = Real.exp (-2*M*(t-u)) := by
      rw [pow_two,← Real.exp_add]
      congr 1
      ring
    rw [← he]
    nlinarith [Real.exp_pos (-M*(t-u)),hb.2 t u hu.1 hu.2]
  have hr : IntervalIntegrable (fun u => d.R t u ^ 2) volume 0 t := by
    have hc : ContinuousOn (fun u => d.R t u ^ 2) (Icc 0 t) := by
      have hcont : Continuous (fun u : ℝ => clampedResponse d t u) :=
        (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
      apply (hcont.pow 2).continuousOn.congr
      intro u hu
      change d.R t u ^ 2 = clampedResponse d t u ^ 2
      rw [clampedResponse_eq hu.1 hu.2]
    exact hc.intervalIntegrable_of_Icc ht
  have heint : IntervalIntegrable (fun u => Real.exp (-2*M*(t-u))) volume 0 t :=
    (show Continuous (fun u => Real.exp (-2*M*(t-u))) by fun_prop).intervalIntegrable 0 t
  have hi := intervalIntegral.integral_mono_on ht heint hr hsq
  rw [integral_exponential_response_square hMp ht] at hi
  have hh := mul_le_mul_of_nonneg_left hi (show 0 ≤ 2*M by positivity)
  have hcancel : (2*M)*((1-Real.exp (-2*M*t))/(2*M)) = 1-Real.exp (-2*M*t) := by
    field_simp
  rw [hcancel] at hh
  have hzero := hsq 0 ⟨le_rfl,ht⟩
  simp only [sub_zero] at hzero
  have hmzero := mul_le_mul_of_nonneg_left hzero hMp.le
  have hpos := mul_nonneg (Real.exp_nonneg (-2*M*t)) (sub_nonneg.mpr hM)
  nlinarith only [hh,hmzero,hpos]

theorem multiplierSup_quadratic {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (hPSD : PositiveSemidefiniteCorrelation d) :
    multiplierSup d ^ 2-multiplierSup d-β^2*(p : ℝ)^3 ≤ 0 := by
  let M := multiplierSup d
  let A := β^2*(p : ℝ)^3
  have hM : 1 ≤ M := multiplierSup_ge_one h hPSD
  have hA : 0 ≤ A := mul_nonneg (sq_nonneg β) (pow_nonneg (Nat.cast_nonneg p) 3)
  have hpoint (t : ℝ≥0) : M*(d.multiplier t-1)^2 ≤ A*(M-1) := by
    have ht := multiplier_response_tradeoff h hPSD t.coe_nonneg
    have hm := response_square_mass_lower h hb hM (fun u hu => multiplier_le_sup h hPSD hu) t.coe_nonneg
    calc
      _ ≤ M*(A*(1-d.R t 0 ^ 2-2*(∫ u in (0 : ℝ)..(t : ℝ),d.R t u ^ 2))) :=
        mul_le_mul_of_nonneg_left ht (by linarith)
      _ = A*(M-M*(d.R t 0 ^ 2+2*(∫ u in (0 : ℝ)..(t : ℝ),d.R t u ^ 2))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (sub_le_sub_left hm M) hA
  obtain ⟨u,_,hlim,hu⟩ := exists_seq_tendsto_sSup
    (range_nonempty (fun t : ℝ≥0 => d.multiplier t)) (multiplier_range_bddAbove h hPSD)
  have hlim' : Tendsto (fun n => M*(u n-1)^2) atTop (𝓝 (M*(M-1)^2)) :=
    tendsto_const_nhds.mul ((hlim.sub_const 1).pow 2)
  have hineq : M*(M-1)^2 ≤ A*(M-1) := le_of_tendsto hlim' (Eventually.of_forall fun n => by
    obtain ⟨t,ht⟩ := hu n
    rw [← ht]
    exact hpoint t)
  by_cases hM1 : M = 1
  · change M^2-M-A ≤ 0
    rw [hM1]
    nlinarith
  · have hpos : 0 < M-1 := sub_pos.mpr (lt_of_le_of_ne hM (Ne.symm hM1))
    have hdiv : M*(M-1) ≤ A := by
      apply (mul_le_mul_iff_right₀ hpos).mp
      nlinarith only [hineq]
    change M^2-M-A ≤ 0
    nlinarith only [hdiv]

theorem multiplier_uniform_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (hPSD : PositiveSemidefiniteCorrelation d)
    {t : ℝ} (ht : 0 ≤ t) : 1 ≤ d.multiplier t ∧ d.multiplier t ≤ multiplierCeiling p β := by
  refine ⟨multiplier_ge_one h hb ht, (multiplier_le_sup h hPSD ht).trans ?_⟩
  have hh := multiplierSup_quadratic h hb hPSD
  have hA : 0 ≤ 1+4*β^2*(p : ℝ)^3 := by positivity
  have hsqrt := Real.sq_sqrt hA
  have hs := Real.sqrt_nonneg (1+4*β^2*(p : ℝ)^3)
  unfold multiplierCeiling
  nlinarith

/-- Both assertions of manuscript Proposition 4.3. -/
theorem uniform_bounds_proposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (hPSD : PositiveSemidefiniteCorrelation d) :
    (∀ t : ℝ, 0 ≤ t → energy p β d t ^ 2/(p : ℝ)+d.C t 0 ^ 2+
      2*(∫ u in (0 : ℝ)..t,d.R t u ^ 2) ≤ 1) ∧
    (∀ t : ℝ, 0 ≤ t → 1 ≤ d.multiplier t ∧ d.multiplier t ≤ multiplierCeiling p β) :=
  ⟨fun _ ht => energy_response_tradeoff h hPSD ht,
    fun _ ht => multiplier_uniform_bound h hb hPSD ht⟩

end SphericalAging.UniformMultiplier
