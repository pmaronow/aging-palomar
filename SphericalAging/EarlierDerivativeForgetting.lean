module

public import SphericalAging.ColoredMemoryForgetting

public section

/-! Fixed-wait forgetting of the genuine earlier CK derivative.
Colored forgetting and the earlier derivative equation are proved; the only
selection input is fixed-wait forgetting of the actual correlation. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped Topology InnerProductSpace
open Set MeasureTheory Filter
namespace SphericalAging.EarlierDerivativeForgetting
open CKSpecification CausalTreeRealization ProjectedTreeDrift GreenCovariance
  EarlierCovariance ColoredMemoryForgetting BackwardResponse UniformMultiplier CKKernelBounds

/-- Compactness upgrades pointwise convergence under a genuine uniform half-Hölder bound. -/
theorem uniform_of_half_holder {F : ℝ → ℝ → ℝ} {S K : ℝ} (hK : 0 ≤ K)
    (hh : ∀ t : ℝ, 0 ≤ t → ∀ v ∈ Icc 0 S, ∀ w ∈ Icc 0 S,
      |F t v-F t w| ≤ K*Real.sqrt |v-w|)
    (hp : ∀ v ∈ Icc 0 S, Tendsto (fun t => F t v) atTop (nhds 0)) :
    TendstoUniformlyOn F (fun _ => 0) atTop (Icc 0 S) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hzero : Tendsto (fun δ : ℝ => K*Real.sqrt δ) (nhdsWithin 0 (Ioi 0)) (nhds 0) := by
    simpa using ((Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds).const_mul K
  obtain ⟨δ,hδ,hsmall⟩ := (eventually_mem_nhdsWithin.and
    (hzero.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < ε/2)))).exists
  obtain ⟨s,hs,hfin,hcover⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) S)).finite_cover_balls hδ
  have hpoint : ∀ v ∈ hfin.toFinset, ∀ᶠ t in atTop, |F t v| < ε/2 := by
    intro v hv
    simpa only [Real.dist_eq,sub_zero] using
      Metric.tendsto_nhds.mp (hp v (hs (hfin.mem_toFinset.mp hv))) (ε/2) (by positivity)
  filter_upwards [eventually_ge_atTop (0 : ℝ),(eventually_all_finset hfin.toFinset).mpr hpoint]
    with t ht hpoint
  intro v hv
  obtain ⟨w,hw⟩ := mem_iUnion.mp (hcover hv)
  obtain ⟨hw,hclose⟩ := mem_iUnion.mp hw
  have hdist : |v-w| < δ := by simpa only [Metric.mem_ball,Real.dist_eq] using hclose
  have hm := (hh t ht v hv w (hs hw)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdist.le) hK)
  have he := abs_sub_le (F t v) (F t w) 0
  simp only [sub_zero] at he
  rw [Real.dist_eq,zero_sub,abs_neg]
  linarith [hpoint w (hfin.mem_toFinset.mpr hw)]

/-- Fixed-wait correlation forgetting is automatically uniform on bounded earlier intervals. -/
theorem correlation_fixed_wait_uniform {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    (S : ℝ) : TendstoUniformlyOn d.C (fun _ => 0) atTop (Icc 0 S) := by
  apply uniform_of_half_holder (K := Real.sqrt (2*multiplierCeiling p β)) (Real.sqrt_nonneg _)
  · intro t ht v hv w hw
    have hi := abs_real_inner_le_norm (ckTreeState h t) (ckTreeState h v-ckTreeState h w)
    rw [inner_sub_right,ckTreeState_gram h hb ht hv.1,ckTreeState_gram h hb ht hw.1,
      ckTreeState_norm h hb ht,one_mul] at hi
    have hh := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left
      (ColoredEnergyRegularity.one_minus_correlation_bound h hv.1 hw.1) (by norm_num : (0 : ℝ) ≤ 2))
    rw [← tree_distance_sq h hb hv.1 hw.1,Real.sqrt_sq (norm_nonneg _)] at hh
    rw [show 2*(multiplierCeiling p β*|v-w|)=(2*multiplierCeiling p β)*|v-w| from by ring,
      Real.sqrt_mul (by unfold multiplierCeiling; positivity)] at hh
    exact hi.trans hh
  · intro v hv
    exact hforget v hv.1

@[expose] def earlierCeiling (p : ℕ) (β S : ℝ) : ℝ :=
  multiplierCeiling p β+2+memoryCoefficient p β*S+β^2*(p : ℝ)

theorem earlierSlope_abs_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {t s S ε : ℝ}
    (hs : 0 ≤ s) (hsS : s ≤ S) (hSt : S ≤ t) (hε : 0 ≤ ε)
    (hC : ∀ u ∈ Icc 0 S, d.C t u ≤ ε)
    (hK : ∀ u ∈ Icc 0 S, coloredMemory p d t u ≤ ε) :
    |earlierSlope p β d t s| ≤ earlierCeiling p β S*ε := by
  have ht := hs.trans (hsS.trans hSt)
  have hst := hsS.trans hSt
  have ha := memoryCoefficient_nonnegative h.spin_ge_three (β := β)
  have hB : 0 ≤ β^2*(p : ℝ) := by positivity
  have hLambda : 0 ≤ multiplierCeiling p β := by unfold multiplierCeiling; positivity
  have hm := multiplier_uniform_bound h hb (CKPhysicalConsequences.correlation_psd_of_equations h) hs
  have hc := (hb.1 t s ht hs).1
  have hr := (response_correlation_bounds h hb hs hst)
  have hk := coloredMemory_nonneg (p := p) hb ht hs
  have hCu := hC s ⟨hs,hsS⟩
  have hKu := hK s ⟨hs,hsS⟩
  have hin : 0 ≤ ∫ u in (0 : ℝ)..s, clampedMemory p β d s u*d.C t u :=
    intervalIntegral.integral_nonneg hs (fun u hu =>
      mul_nonneg (clampedMemory_nonnegative h.spin_ge_three hb s u) (hb.1 t u ht hu.1).1)
  have hcont : Continuous (fun u => clampedMemory p β d s u*clampedCorrelation d t u) :=
    ((clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)).mul
      ((clampedCorrelation_continuous h).comp (continuous_const.prodMk continuous_id))
  have hI : IntervalIntegrable (fun u => clampedMemory p β d s u*d.C t u) volume 0 s := by
    apply (hcont.intervalIntegrable 0 s).congr
    intro u hu
    rw [uIoc_of_le hs] at hu
    dsimp only
    rw [clampedCorrelation_eq ht hu.1.le]
  have hib : (∫ u in (0 : ℝ)..s, clampedMemory p β d s u*d.C t u) ≤
      memoryCoefficient p β*S*ε := by
    have hi := intervalIntegral.integral_mono_on hs hI intervalIntegrable_const (fun u hu =>
      mul_le_mul (clampedMemory_le_coefficient h hb s u) (hC u ⟨hu.1,hu.2.trans hsS⟩)
        (hb.1 t u ht hu.1).1 ha)
    simp only [intervalIntegral.integral_const,sub_zero,smul_eq_mul] at hi
    calc
      _ ≤ s*(memoryCoefficient p β*ε) := hi
      _ ≤ _ := by nlinarith [mul_nonneg ha hε,mul_le_mul_of_nonneg_right hsS (mul_nonneg ha hε)]
  have hneg : -multiplierCeiling p β*ε ≤ earlierSlope p β d t s := by
    unfold earlierSlope
    nlinarith [mul_le_mul hm.2 hCu hc hLambda,mul_nonneg hB hk]
  have hpos : earlierSlope p β d t s ≤ (2+memoryCoefficient p β*S+β^2*(p : ℝ))*ε := by
    unfold earlierSlope
    nlinarith [mul_nonneg (by linarith [hm.1] : 0 ≤ d.multiplier s) hc,
      mul_le_mul_of_nonneg_left hKu hB]
  apply abs_le.mpr
  unfold earlierCeiling
  constructor
  · nlinarith [mul_nonneg ha (hs.trans hsS),mul_nonneg hB hε]
  · nlinarith [mul_nonneg hLambda hε]

/-- Source backward-FDT Step 2: actual earlier slopes forget every bounded earlier interval. -/
theorem earlierSlope_fixed_wait_uniform {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {S : ℝ} (hS : 0 ≤ S) :
    TendstoUniformlyOn (earlierSlope p β d) (fun _ => 0) atTop (Icc 0 S) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let K := earlierCeiling p β S
  have hK : 0 ≤ K := by
    dsimp [K,earlierCeiling]
    have ha := memoryCoefficient_nonnegative h.spin_ge_three (β := β)
    unfold multiplierCeiling
    positivity
  let δ := ε/(K+1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hC := Metric.tendstoUniformlyOn_iff.mp (correlation_fixed_wait_uniform h hb hforget S) δ hδ
  have hCol := Metric.tendstoUniformlyOn_iff.mp (coloredMemory_tendstoUniformlyOn h hb hforget S) δ hδ
  filter_upwards [eventually_ge_atTop S,hC,hCol] with t ht hC hCol
  intro s hs
  have hi := earlierSlope_abs_bound h hb hs.1 hs.2 ht hδ.le
    (fun u hu => (le_abs_self (d.C t u)).trans (by simpa only [Real.dist_eq,zero_sub,abs_neg] using (hC u hu).le))
    (fun u hu => (le_abs_self (coloredMemory p d t u)).trans
      (by simpa only [Real.dist_eq,zero_sub,abs_neg] using (hCol u hu).le))
  rw [Real.dist_eq,zero_sub,abs_neg]
  have hid : (K+1)*δ=ε := by dsimp [δ]; field_simp
  change |earlierSlope p β d t s| ≤ K*δ at hi
  linarith

end SphericalAging.EarlierDerivativeForgetting
