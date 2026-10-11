module

public import SphericalAging.CausalStripIntegralBound
public import SphericalAging.OldResponseL2
public import SphericalAging.IntervalL2Bounds

public section

/-! The final assertion of the disjoint causal strips lemma: the literal
whole-old-row rank-one operator and its moving-prefix counterpart have
vanishing Hilbert--Schmidt distance. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CausalStripDistance
open CausalTree CausalTree.HilbertDatum CausalTreeRealization
open CKSpecification GreenCovariance PrefixReflection HilbertSchmidtTensor
open DisjointCausalStrips CausalStripIntegralBound OldResponseL2
open WhitePrefixResponse BackwardRowL2 ThermalRowConvergence

@[expose] def stateOperatorRow {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (t T : ℝ) :=
  ∫u in (0 : ℝ)..T,d.R t u • stateRankOne h u

@[expose] def prefixOperatorRow {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) (D t T : ℝ) :=
  ∫u in D..T,d.R t u • prefixRankOne h D u

theorem stateRankOne_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) :
    ContinuousOn (stateRankOne h) (Ici 0) := by
  apply (stateRankOne_clamped_continuous h hb).continuousOn.congr
  intro u hu
  change 0≤u at hu
  simp only [max_eq_right hu]

theorem prefixRankOne_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (D : ℝ) :
    ContinuousOn (prefixRankOne h D) (Ici 0) := by
  apply (prefixRankOne_clamped_continuous h hb D).continuousOn.congr
  intro u hu
  change 0≤u at hu
  simp only [max_eq_right hu]

theorem rankOne_row_intervalIntegrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {a b t : ℝ}
    (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    IntervalIntegrable (fun u => d.R t u • stateRankOne h u) volume a b :=
  ((response_continuousOn_interval h ha hbt).smul
    ((stateRankOne_continuousOn h hb).mono (fun u hu => ha.trans hu.1))).intervalIntegrable_of_Icc hab

theorem prefix_row_intervalIntegrable {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) (D : ℝ) {a b t : ℝ}
    (ha : 0≤a) (hab : a≤b) (hbt : b≤t) :
    IntervalIntegrable (fun u => d.R t u • prefixRankOne h D u) volume a b :=
  ((response_continuousOn_interval h ha hbt).smul
    ((prefixRankOne_continuousOn h hb D).mono (fun u hu => ha.trans hu.1))).intervalIntegrable_of_Icc hab

theorem early_operator_row_sq_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D t : ℝ}
    (hD : 0≤D) (hDt : D≤t) :
    ‖stateOperatorRow h t D‖^2≤D*(∫u in (0 : ℝ)..D,(d.R t u)^2) := by
  have hf := rankOne_row_intervalIntegrable h hb le_rfl hD hDt
  have hc : Continuous (fun u : ℝ => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hn : ‖stateOperatorRow h t D‖≤∫u in (0 : ℝ)..D,|clampedResponse d t u| := by
    apply (intervalIntegral.norm_integral_le_integral_norm hD).trans
    apply intervalIntegral.integral_mono_on hD hf.norm (hc.abs.intervalIntegrable 0 D)
    intro u hu
    rw [norm_smul,stateRankOne_norm h hb hu.1,Real.norm_eq_abs,mul_one,
      clampedResponse_eq hu.1 (hu.2.trans hDt)]
  have hs := IntervalL2Bounds.integral_abs_le_sqrt hc hD
  have he : (∫u in (0 : ℝ)..D,(clampedResponse d t u)^2)=
      ∫u in (0 : ℝ)..D,(d.R t u)^2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hD] at hu
    dsimp only
    rw [clampedResponse_eq hu.1 (hu.2.trans hDt)]
  rw [he,sub_zero] at hs
  have hE : 0≤∫u in (0 : ℝ)..D,(d.R t u)^2 :=
    intervalIntegral.integral_nonneg hD (fun _ _ => sq_nonneg _)
  have hh := hn.trans hs
  have hsD := Real.sq_sqrt hD
  have hsE := Real.sq_sqrt hE
  nlinarith [norm_nonneg (stateOperatorRow h t D),Real.sqrt_nonneg D,
    Real.sqrt_nonneg (∫u in (0 : ℝ)..D,(d.R t u)^2),sq_nonneg
      (Real.sqrt D*Real.sqrt (∫u in (0 : ℝ)..D,(d.R t u)^2)-‖stateOperatorRow h t D‖)]

theorem operator_row_difference_decomposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0≤D) (hDT : D≤T) (hTt : T≤t) :
    stateOperatorRow h t T-prefixOperatorRow h D t T=
      stateOperatorRow h t D+(∫u in D..T,d.R t u • strip h D u) := by
  unfold stateOperatorRow prefixOperatorRow
  rw [←intervalIntegral.integral_add_adjacent_intervals
    (rankOne_row_intervalIntegrable h hb le_rfl hD (hDT.trans hTt))
    (rankOne_row_intervalIntegrable h hb hD hDT hTt)]
  have he : (fun u => d.R t u • strip h D u)=
      (fun u => d.R t u • stateRankOne h u-d.R t u • prefixRankOne h D u) := by
    funext u
    exact smul_sub _ _ _
  rw [he,intervalIntegral.integral_sub (rankOne_row_intervalIntegrable h hb hD hDT hTt)
    (prefix_row_intervalIntegrable h hb D hD hDT hTt)]
  abel

/-- A concrete squared distance estimate in terms of the actual whole old
response energy; the constant is sufficient for the source vanishing limit. -/
theorem operator_row_distance_sq_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {D T t : ℝ}
    (hD : 0<D) (hDT : D≤T) (hTt : T≤t) :
    ‖stateOperatorRow h t T-prefixOperatorRow h D t T‖^2≤
      18*D*(∫u in (0 : ℝ)..T,(d.R t u)^2) := by
  have h0T := hD.le.trans hDT
  have hi : IntervalIntegrable (fun u => (d.R t u)^2) volume 0 T :=
    (response_continuousOn_interval h le_rfl hTt).pow 2 |>.intervalIntegrable_of_Icc h0T
  have hE := intervalIntegral.integral_mono_interval le_rfl hD.le hDT
    (ae_of_all _ (fun _ => sq_nonneg _)) hi
  have hS := intervalIntegral.integral_mono_interval hD.le hDT le_rfl
    (ae_of_all _ (fun _ => sq_nonneg _)) hi
  have hA := early_operator_row_sq_bound h hb hD.le (hDT.trans hTt)
  have hB := causal_strip_interval_bound h hb hD hDT hTt
  have hA' := hA.trans (mul_le_mul_of_nonneg_left hE hD.le)
  have hB' := hB.trans (mul_le_mul_of_nonneg_left hS (by positivity : 0≤8*D))
  rw [operator_row_difference_decomposition h hb hD.le hDT hTt]
  have hn := norm_add_le (stateOperatorRow h t D) (∫u in D..T,d.R t u • strip h D u)
  nlinarith [sq_nonneg (‖stateOperatorRow h t D‖-‖∫u in D..T,d.R t u • strip h D u‖),
    norm_nonneg (stateOperatorRow h t D),norm_nonneg (∫u in D..T,d.R t u • strip h D u),
    norm_nonneg (stateOperatorRow h t D+(∫u in D..T,d.R t u • strip h D u))]

/-- The literal final assertion of Lemma 14.6. Only the genuine preceding
strong L2 response-row convergence is used for the long-time part. -/
theorem old_operator_row_distance_tendsto_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {r : ℝ→ℝ} (hr : MemLp r 2 rayMeasure)
    (hrow : Tendsto (rowError d r) atTop (𝓝 0)) {D : ℝ} (hD : 0<D)
    (t L : ℕ→ℝ) (ht : Tendsto t atTop atTop) (hL : Tendsto L atTop atTop)
    (hcausal : ∀n,D≤t n-L n) :
    Tendsto (fun n => ‖stateOperatorRow h (t n) (t n-L n)-
      prefixOperatorRow h D (t n) (t n-L n)‖) atTop (𝓝 0) := by
  have hLt : ∀n,L n≤t n := fun n => by linarith [hcausal n]
  have hE := old_response_square_tendsto_zero h hr hrow t L ht hL hLt
  have he : Tendsto (fun n => 18*D*remoteTail d (t n) (L n)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hE.const_mul (18*D)
  have hs : Tendsto (fun n => ‖stateOperatorRow h (t n) (t n-L n)-
      prefixOperatorRow h D (t n) (t n-L n)‖^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ he
    filter_upwards [hL.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
    have hbnd := operator_row_distance_sq_bound h hb (t := t n) hD (hcausal n) (by linarith)
    simpa only [remoteTail,max_eq_right (hD.le.trans (hcausal n))] using hbnd
  simpa only [Real.sqrt_sq (norm_nonneg _),Real.sqrt_zero] using hs.sqrt

end SphericalAging.CausalStripDistance
