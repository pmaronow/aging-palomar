module

public import SphericalAging.HalfLineL2Translation
public import SphericalAging.WhitePrefixResponse
public import SphericalAging.LateTriangleSup
public import SphericalAging.BackwardStrongL2

public section

/-! Actual thermal covariance convergence on the full late triangle. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.ThermalRowConvergence
open CKSpecification EarlierCovariance GreenCovariance StrongBackwardDefect EarlierSmoothing
  BackwardRowL2 BackwardRowResidual HalfLineL2Translation WhitePrefixResponse LateTriangleSup

@[expose] def thermalProfile (r : ℝ→ℝ) (τ : ℝ) : ℝ :=
  2*(∫v : ℝ,r (τ+v)*r v ∂rayMeasure)

@[expose] def rowError (d : CKData) (r : ℝ→ℝ) (t : ℝ) : ℝ :=
  (eLpNorm (fun v => responseRow d t v-r v) 2 rayMeasure).toReal

/-- The exact half-line pairing of the actual causal response rows is the
original finite thermal covariance, by the true reflection substitution. -/
theorem thermal_row_pair {d : CKData} {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    whiteTerm d t s=2*(∫v : ℝ,responseRow d t (t-s+v)*responseRow d s v ∂rayMeasure) := by
  have he : (fun v => responseRow d t (t-s+v)*responseRow d s v)=ᵐ[rayMeasure]
      (Ioc 0 s).indicator (fun v => clampedResponse d t (s-v)*clampedResponse d s (s-v)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    have hv0 : 0<v := hv
    by_cases hvs : v≤s
    · have hmem : v∈Ioc 0 s := ⟨hv,hvs⟩
      have hmt : t-s+v∈Ioc 0 t := ⟨by linarith,by linarith⟩
      simp only [responseRow,indicator_of_mem hmem,indicator_of_mem hmt]
      congr 2
      ring
    · simp only [responseRow,indicator_of_notMem (show v∉Ioc 0 s from fun hh => hvs hh.2),mul_zero]
  rw [integral_congr_ae he,integral_indicator measurableSet_Ioc,rayMeasure,
    Measure.restrict_restrict measurableSet_Ioc,
    inter_eq_left.mpr (show Ioc (0:ℝ) s⊆Ioi 0 from fun _ hx => hx.1),
    ←intervalIntegral.integral_of_le hs,whiteTerm,min_eq_right hst]
  congr 1
  simpa only [sub_zero,sub_self] using (intervalIntegral.integral_comp_sub_left
    (fun u => clampedResponse d t u*clampedResponse d s u) s (a:=0) (b:=s)).symm

theorem response_row_square {d : CKData} {t : ℝ} (ht : 0≤t) :
    (∫v : ℝ,(responseRow d t v)^2 ∂rayMeasure)=∫u in (0:ℝ)..t,(d.R t u)^2 := by
  rw [responseRow,causal_square_integral (f:=fun u => clampedResponse d t u) ht]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le ht] at hu
  dsimp only
  rw [clampedResponse_eq hu.1 hu.2]

/-- A genuine uniform norm bound derived from the white-leaf prefix identity. -/
theorem response_row_norm_le_one {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0≤t) :
    (eLpNorm (responseRow d t) 2 rayMeasure).toReal≤1 := by
  have he := remoteTail_le_center h (L:=0) le_rfl ht
  have hn := PrefixReflection.prefixVector_norm_le_one h
    (CKPhysicalConsequences.physical_bounds_of_equations h) t ht
  simp only [CausalCenterAverage.localCenter,sub_zero,add_zero] at he
  have hs : ‖PrefixReflection.prefixVector h t t‖^2≤1 := by nlinarith [norm_nonneg (PrefixReflection.prefixVector h t t)]
  have hi : (∫u in (0:ℝ)..t,(d.R t u)^2)≤1 := by
    simp only [remoteTail,sub_zero,max_eq_right ht] at he
    nlinarith [intervalIntegral.integral_nonneg (μ:=volume) ht (fun u _ => sq_nonneg (d.R t u))]
  rw [lpNorm_two_eq_sqrt (responseRow_memLp_two h t),response_row_square ht]
  exact (Real.sqrt_le_sqrt hi).trans_eq (by norm_num)

/-- True L2 pairing estimate, uniform over every nonnegative lag. The
profile norm is its actual half-line norm, not a supplied bound. -/
theorem thermal_error_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    {t s : ℝ} (hs : 0≤s) (hst : s≤t) :
    |whiteTerm d t s-thermalProfile r (t-s)|≤
      2*(rowError d r t+(eLpNorm r 2 rayMeasure).toReal*rowError d r s) := by
  let τ := t-s
  have hτ : 0≤τ := sub_nonneg.mpr hst
  have hft := responseRow_memLp_two h t
  have hfs := responseRow_memLp_two h s
  have hgt := shift_memLp_two hft hτ
  have hgr := shift_memLp_two hr hτ
  have hd := shift_memLp_two (hft.sub hr) hτ
  have ha := integral_mul_abs_le hd hfs
  have hb := integral_mul_abs_le hgr (hfs.sub hr)
  have hde : (eLpNorm (fun v => (responseRow d t-r) (τ+v)) 2 rayMeasure).toReal≤rowError d r t :=
    shift_norm_le (hft.sub hr) hτ
  have hre := shift_norm_le hr hτ
  have hfsb := response_row_norm_le_one h hs
  have hpair : (∫v : ℝ,responseRow d t (τ+v)*responseRow d s v ∂rayMeasure)-
      (∫v : ℝ,r (τ+v)*r v ∂rayMeasure)=
      (∫v : ℝ,(responseRow d t (τ+v)-r (τ+v))*responseRow d s v ∂rayMeasure)+
      (∫v : ℝ,r (τ+v)*(responseRow d s v-r v) ∂rayMeasure) := by
    have hia : Integrable (fun v => responseRow d t (τ+v)*responseRow d s v) rayMeasure :=
      hgt.integrable_mul hfs
    have hib : Integrable (fun v => r (τ+v)*r v) rayMeasure := hgr.integrable_mul hr
    have hic : Integrable (fun v => (responseRow d t (τ+v)-r (τ+v))*responseRow d s v) rayMeasure :=
      hd.integrable_mul hfs
    have hid : Integrable (fun v => r (τ+v)*(responseRow d s v-r v)) rayMeasure :=
      hgr.integrable_mul (hfs.sub hr)
    rw [←integral_sub hia hib,←integral_add hic hid]
    apply integral_congr_ae
    exact ae_of_all _ (fun _ => by dsimp only [Pi.sub_apply,Pi.mul_apply]; ring)
  rw [thermal_row_pair hs hst,thermalProfile,←mul_sub,hpair,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ)≤2)]
  have hab := abs_add_le
    (∫v : ℝ,(responseRow d t (τ+v)-r (τ+v))*responseRow d s v ∂rayMeasure)
    (∫v : ℝ,r (τ+v)*(responseRow d s v-r v) ∂rayMeasure)
  have hma := mul_le_mul hde hfsb (by positivity)
    (by unfold rowError; positivity)
  have hmb := mul_le_mul_of_nonneg_right hre
    (show 0≤rowError d r s from by unfold rowError; positivity)
  apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ)≤2)
  apply hab.trans
  apply add_le_add
  · simpa only [mul_one,Pi.sub_apply] using ha.trans hma
  · exact hb.trans hmb

/-- Uniform eventual convergence over the actual whole late triangle. -/
theorem thermal_eventually_uniform {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠS : ℝ in atTop,∀t s : ℝ,S≤s→s≤t→
      |whiteTerm d t s-thermalProfile r (t-s)|≤ε := by
  let M := (eLpNorm r 2 rayMeasure).toReal
  have hM : 0≤M := ENNReal.toReal_nonneg
  let δ := ε/(4*(1+M))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hrow.eventually (gt_mem_nhds hδ))
  have hcal : 2*(δ+M*δ)≤ε := by
    have he : 4*(1+M)*δ=ε := by dsimp [δ]; field_simp
    nlinarith
  filter_upwards [eventually_ge_atTop (max U 0)] with S hS
  intro t s hs ht
  have hs0 : 0≤s := (le_max_right U 0).trans (hS.trans hs)
  have hEs := (hU s ((le_max_left U 0).trans (hS.trans hs))).le
  have hEt := (hU t ((le_max_left U 0).trans ((hS.trans hs).trans ht))).le
  exact (thermal_error_bound h hr hs0 ht).trans
    (by change 2*(rowError d r t+M*rowError d r s)≤ε; nlinarith)

/-- Literal source limit of the full late-triangle supremum. -/
theorem thermal_uniform_supremum {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0)) :
    Tendsto (lateSup (fun t s => |whiteTerm d t s-thermalProfile r (t-s)|) 0)
      atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [thermal_eventually_uniform h hr hrow (by positivity : 0<ε/2)] with S hS
  have hn : 0≤lateSup (fun t s => |whiteTerm d t s-thermalProfile r (t-s)|) 0 S :=
    lateSup_nonneg (abs_nonneg _)
  have he := lateSup_le (D:=0) (S:=S) (fun t s hs ht => hS t s hs (by simpa using ht))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hn]
  linarith

/-- The actual covariance converges to its stationary thermal value along
any late causal pair, uniformly in its lag. -/
theorem thermal_late_pair_error {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0))
    {ι : Type*} {F : Filter ι} {t s : ι→ℝ} (hs : Tendsto s F atTop)
    (hts : ∀ᶠn in F,s n≤t n) :
    Tendsto (fun n => whiteTerm d (t n) (s n)-thermalProfile r (t n-s n)) F (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨S,hS⟩ := (thermal_eventually_uniform h hr hrow (by positivity : 0<ε/2)).exists
  filter_upwards [hs.eventually (eventually_ge_atTop S),hts] with n hsn htsn
  rw [Real.dist_eq,sub_zero]
  exact lt_of_le_of_lt (hS (t n) (s n) hsn htsn) (by linarith)

theorem thermal_late_diverging_pair {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0))
    (hdecay : Tendsto (thermalProfile r) atTop (𝓝 0))
    {ι : Type*} {F : Filter ι} {t s : ι→ℝ} (hs : Tendsto s F atTop)
    (hlag : Tendsto (fun n => t n-s n) F atTop) :
    Tendsto (fun n => whiteTerm d (t n) (s n)) F (𝓝 0) := by
  have hts : ∀ᶠn in F,s n≤t n := by
    filter_upwards [hlag.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    linarith
  have he := (thermal_late_pair_error h hr hrow hs hts).add (hdecay.comp hlag)
  simpa only [sub_add_cancel,zero_add,Function.comp_def] using he

theorem thermal_diagonal_limit {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0)) :
    Tendsto (fun t => whiteTerm d t t) atTop
      (𝓝 (2*(∫v : ℝ,(r v)^2 ∂rayMeasure))) := by
  have he := (thermal_late_pair_error h hr hrow tendsto_id
    (Eventually.of_forall (fun _ => le_rfl))).add_const (thermalProfile r 0)
  simpa only [sub_self,sub_add_cancel,zero_add,thermalProfile,pow_two,id_eq] using he

end SphericalAging.ThermalRowConvergence
