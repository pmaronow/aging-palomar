module

public import SphericalAging.RenewalIntervalHat

public section

/-! The true Blackwell interval theorem for source-nonarithmetic positive
renewal laws under only a finite first moment. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal
namespace SphericalAging.PositiveRenewalBlackwell
noncomputable section
set_option backward.isDefEq.respectTransparency false
open RenewalIntervalHat PositiveRenewalCompactLimit PositiveRenewalCompactKernel
open PositiveRenewalSeries PositiveRenewalCellBound RenewalFirstMoment AbsorptionCutoff.Renewal

@[expose] def renewalInterval (μ : Measure ℝ) (a b x : ℝ) : ℝ :=
  (renewalMeasure μ).real (Icc (x-b) (x-a))

theorem renewalInterval_uniform_bound {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (a b : ℝ) :
    ∀x : ℝ,renewalInterval μ a b x≤(renewalMeasure μ (Icc 0 (b-a))).toReal := by
  intro x
  apply ENNReal.toReal_mono (positive_renewal_locally_finite hp 0 (b-a))
  simpa only [show x-b+(b-a)=x-a by ring] using positive_renewal_interval_bound hp (x-b) (b-a)

theorem intervalHat_renewal_lower {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (a b : ℝ) {ε : ℝ} (he : 0<ε) (x : ℝ) :
    renewalConvolution μ (intervalHat a b ε) x≤renewalInterval μ a b x := by
  let U := renewalMeasure μ
  let J := Icc (x-b) (x-a)
  have hiH := compact_kernel_integrable hp (intervalHat_lipschitz a b he).continuous.measurable
    (intervalHat_support_radius a b he) (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (intervalHat_nonnegative a b ε t)]
      exact intervalHat_le_one a b ε t) x
  have hiI : Integrable (J.indicator (fun _ : ℝ => (1:ℝ))) U :=
    (integrableOn_const (positive_renewal_locally_finite hp (x-b) (x-a))).integrable_indicator measurableSet_Icc
  change (∫y,intervalHat a b ε (x-y) ∂U)≤U.real J
  rw [←integral_indicator_one measurableSet_Icc]
  apply integral_mono hiH hiI
  intro y
  by_cases hy : y∈J
  · rw [indicator_of_mem hy]
    exact intervalHat_le_one a b ε (x-y)
  · rw [indicator_of_notMem hy]
    have hz : intervalHat a b ε (x-y)=0 := by
      apply intervalHat_zero he
      intro htab
      apply hy
      constructor <;> linarith [htab.1,htab.2]
    exact hz.le

theorem intervalHat_renewal_upper {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (a b : ℝ) {ε : ℝ} (he : 0<ε) (x : ℝ) :
    renewalInterval μ a b x≤renewalConvolution μ (intervalHat (a-ε) (b+ε) ε) x := by
  let U := renewalMeasure μ
  let J := Icc (x-b) (x-a)
  have hiH := compact_kernel_integrable hp (intervalHat_lipschitz (a-ε) (b+ε) he).continuous.measurable
    (intervalHat_support_radius (a-ε) (b+ε) he) (fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg (intervalHat_nonnegative (a-ε) (b+ε) ε t)]
      exact intervalHat_le_one (a-ε) (b+ε) ε t) x
  have hiI : Integrable (J.indicator (fun _ : ℝ => (1:ℝ))) U :=
    (integrableOn_const (positive_renewal_locally_finite hp (x-b) (x-a))).integrable_indicator measurableSet_Icc
  change U.real J≤∫y,intervalHat (a-ε) (b+ε) ε (x-y) ∂U
  rw [←integral_indicator_one measurableSet_Icc]
  apply integral_mono hiI hiH
  intro y
  by_cases hy : y∈J
  · rw [indicator_of_mem hy]
    change 1 ≤ intervalHat (a-ε) (b+ε) ε (x-y)
    rw [intervalHat_eq_one he (show x-y∈Icc ((a-ε)+ε) ((b+ε)-ε) from by
      constructor <;> linarith [hy.1,hy.2])]
  · rw [indicator_of_notMem hy]
    exact intervalHat_nonnegative (a-ε) (b+ε) ε (x-y)

/-- Actual renewal interval mass tends to interval length divided by the
actual finite first mean. The original arithmetic definition is sufficient. -/
theorem first_moment_blackwell {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hp : ∀ᵐ y ∂μ,0<y) (hna : ¬Arithmetic μ) (hi : Integrable id μ)
    (a b : ℝ) (hab : a≤b) :
    Tendsto (renewalInterval μ a b) atTop (𝓝 ((b-a)/(∫y : ℝ,y ∂μ))) := by
  let W := renewalInterval μ a b
  let m := ∫y : ℝ,y ∂μ
  have hm : 0<m := mean_positive_of_positive_integrable hp hi
  have hupper : atTop.IsBoundedUnder (·≤·) W :=
    ⟨(renewalMeasure μ (Icc 0 (b-a))).toReal,show ∀ᶠx : ℝ in atTop,W x≤_ from
      Eventually.of_forall (renewalInterval_uniform_bound hp a b)⟩
  have hlower : atTop.IsBoundedUnder (·≥·) W :=
    ⟨0,show ∀ᶠx : ℝ in atTop,0≤W x from Eventually.of_forall (fun _ => measureReal_nonneg)⟩
  have hSup : limsup W atTop≤(b-a)/m := by
    apply le_of_forall_gt_imp_ge_of_dense
    intro d hd
    let ε := (d*m-(b-a))/4
    have he : 0<ε := by dsimp [ε];have hd' := (div_lt_iff₀ hm).mp hd;linarith
    let H := intervalHat (a-ε) (b+ε) ε
    have hconv := first_moment_compact_key_renewal hp hna hi
      (intervalHat_lipschitz (a-ε) (b+ε) he) (intervalHat_support_radius (a-ε) (b+ε) he)
      (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (intervalHat_nonnegative (a-ε) (b+ε) ε t)];exact intervalHat_le_one (a-ε) (b+ε) ε t)
      (intervalHat_nonnegative (a-ε) (b+ε) ε)
    have hcomp : limsup W atTop≤(∫t : ℝ,H t)/m := by
      have hl := limsup_le_limsup (Eventually.of_forall (intervalHat_renewal_upper hp a b he))
        hlower.isCoboundedUnder_le hconv.isBoundedUnder_le
      rw [hconv.limsup_eq] at hl
      exact hl
    have harea : (∫t : ℝ,H t)≤b-a+2*ε := by
      have ht := intervalHat_integral_upper he (by linarith : a-ε≤b+ε)
      dsimp [H]
      linarith
    have hclose : (b-a+2*ε)/m≤d := by
      apply (div_le_iff₀ hm).mpr
      dsimp [ε]
      have hd' := (div_lt_iff₀ hm).mp hd
      linarith
    exact hcomp.trans ((div_le_div_of_nonneg_right harea hm.le).trans hclose)
  have hInf : (b-a)/m≤liminf W atTop := by
    apply le_of_forall_lt_imp_le_of_dense
    intro d hd
    let ε := ((b-a)-d*m)/4
    have he : 0<ε := by dsimp [ε];have hd' := (lt_div_iff₀ hm).mp hd;linarith
    let H := intervalHat a b ε
    have hconv := first_moment_compact_key_renewal hp hna hi
      (intervalHat_lipschitz a b he) (intervalHat_support_radius a b he)
      (fun t => by rw [Real.norm_eq_abs,abs_of_nonneg (intervalHat_nonnegative a b ε t)];exact intervalHat_le_one a b ε t)
      (intervalHat_nonnegative a b ε)
    have hcomp : (∫t : ℝ,H t)/m≤liminf W atTop := by
      have hl := liminf_le_liminf (Eventually.of_forall (intervalHat_renewal_lower hp a b he))
        hconv.isBoundedUnder_ge hupper.isCoboundedUnder_ge
      rw [hconv.liminf_eq] at hl
      exact hl
    have harea : b-a-2*ε≤∫t : ℝ,H t := intervalHat_integral_lower he
    have hclose : d≤(b-a-2*ε)/m := by
      apply (le_div_iff₀ hm).mpr
      dsimp [ε]
      have hd' := (lt_div_iff₀ hm).mp hd
      linarith
    exact hclose.trans ((div_le_div_of_nonneg_right harea hm.le).trans hcomp)
  exact tendsto_of_le_liminf_of_limsup_le hInf hSup hupper hlower

end
end SphericalAging.PositiveRenewalBlackwell
