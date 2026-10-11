module

public import SphericalAging.FisherRecentStrip
public import SphericalAging.FisherBulkCalibration

public section

/-! The genuine source15.3 memory lower bound, using actual late three-time
products, oriented clipped FTC and the actual recent-strip limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherMemoryLower
open CKSpecification CKPhysicalConsequences BackwardResponse GreenCovariance
open StrongBackwardDefect FisherPhysicalWindow FisherPhysicalMemory FisherPhysicalResponse
open FisherWindowEnds FisherRecentStrip FisherBulkCalibration ClippedFisherPrimitive
open ActualProductFromSelected ActualCorrelationProduct ProductTransfer

lemma primitive_tendsto {ι : Type*} {F : Filter ι} {k y : ι → ℝ} {κ b : ℝ}
    (hκ : 0<κ) (hk : Tendsto k F (𝓝 κ)) (hy : Tendsto y F (𝓝 b)) :
    Tendsto (fun i => primitive (k i) (y i)) F (𝓝 (primitive κ b)) := by
  have hc : ContinuousAt (fun z : ℝ×ℝ => primitive z.1 z.2) (κ,b) :=
    primitive_joint_continuous.continuousAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hκ)
  exact hc.tendsto.comp (hk.prodMk_nhds hy)

theorem memory_split_lower {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s t W : ℝ} (hs : 0≤s) (hW : 0≤W) (hgap : s+2*W≤t) :
    (∫u in (t-W)..t,(1-d.C u s^2)*d.R t u)+
      (∫u in (s+W)..(t-W),(1-d.C u s^2)*d.R t u)≤memoryIntegral d s t := by
  have hst : s≤t := by linarith
  have hc : ContinuousOn (fun u => (1-d.C u s^2)*d.R t u) (Icc s t) :=
    (continuousOn_const.sub (correlation_first_continuousOn h hs |>.pow 2)).mul
      (response_continuousOn h hs hst)
  have hiA : IntervalIntegrable (fun u => (1-d.C u s^2)*d.R t u) volume (s+W) (t-W) :=
    (hc.mono (fun u hu => ⟨by linarith [hu.1],by linarith [hu.2]⟩)).intervalIntegrable_of_Icc (by linarith)
  have hiB : IntervalIntegrable (fun u => (1-d.C u s^2)*d.R t u) volume (t-W) t :=
    (hc.mono (fun u hu => ⟨by linarith [hu.1],hu.2⟩)).intervalIntegrable_of_Icc (by linarith)
  rw [add_comm,intervalIntegral.integral_add_adjacent_intervals hiA hiB]
  apply intervalIntegral.integral_mono_interval (by linarith : s≤s+W) (by linarith : s+W≤t) le_rfl _
    (hc.intervalIntegrable_of_Icc hst)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
  have hb := physical_bounds_of_equations h
  have hC := hb.1 u s (hs.trans hu.1.le) hs
  exact mul_nonneg (by nlinarith [hC.1,hC.2]) (hb.2 t u (hs.trans hu.1.le) hu.2)

/-- Every actual convergent memory subsequence obeys the source lower bound.
The actual existence of such a subsequence follows from the physical window
bound and is used only in the final obstruction assembly. -/
theorem memory_limit_lower {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ} {z ε I : ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z))
    (herr : Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 ε))
    (hz : z∈Ioo 0 q) (hI : Tendsto (fun n => memoryIntegral d (s n) (t n)) atTop (𝓝 I)) :
    FisherCost.memoryMainTerm q z-ε≤I := by
  have hqz : 0<q*z := mul_pos H.q_positive hz.1
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hs
    filter_upwards [hgap.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    linarith
  have hk := hC.const_mul q
  have hfixed (π : ℝ) (hπ : 0<π) : FisherCost.memoryMainTerm q z-ε-2*(1+ε)*π/(q*z)≤I := by
    have hprod := actual_three_time_product (threshold_inputs H hf ⟨a,ha⟩) hπ
    have htwo : Tendsto (fun D : ℝ => 2*D) atTop atTop := tendsto_id.const_mul_atTop (by norm_num)
    have hφ := primitive_tendsto hqz tendsto_const_nhds (H.plateau_limit.comp htwo)
    have hDlim := (((tendsto_const_nhds (x:=(1:ℝ))).sub
      (H.plateau_limit.comp htwo)).mul_const (1-z^2)).add hφ
      |>.sub_const (primitive (q*z) z) |>.sub_const ε |>.sub_const (2*(1+ε)*π/(q*z))
    have hDlim' : Tendsto (fun D : ℝ => (1-c (2*D))*(1-z^2)+
        primitive (q*z) (c (2*D))-primitive (q*z) z-ε-2*(1+ε)*π/(q*z))
        atTop (𝓝 (FisherCost.memoryMainTerm q z-ε-2*(1+ε)*π/(q*z))) := by
      have heq : (1-q)*(1-z^2)+primitive (q*z) q-primitive (q*z) z-ε-
          2*(1+ε)*π/(q*z)=FisherCost.memoryMainTerm q z-ε-2*(1+ε)*π/(q*z) := by
        have hh := calibrated_primitive_difference ⟨H.q_positive,H.plateau_lt_one⟩ hz
        unfold FisherCost.memoryMainTerm
        linarith
      simpa only [Function.comp_def,heq] using hDlim
    apply le_of_tendsto hDlim'
    filter_upwards [hprod] with D hD
    have hDpos := hD.1
    obtain ⟨S,hS⟩ := eventually_atTop.mp hD.2
    have hrecent := recent_memory_tendsto H hf ha hs hgap hC (by positivity : 0<2*D)
    have hend := recent_endpoint_tendsto H ht (by positivity : 0≤2*D)
    have hstart := early_correlation_tendsto H hf ha hs hgap hC (by positivity : 0<2*D)
    have hφend := primitive_tendsto hqz hk hend
    have hφstart := primitive_tendsto hqz hk hstart
    have herror := (((tendsto_const_nhds (x:=(1:ℝ))).add herr).const_mul 2).mul_const π
      |>.div hk (ne_of_gt hqz)
    have hlim := hrecent.add hφend |>.sub hφstart |>.sub herr |>.sub herror
    have hlim' : Tendsto (fun n =>
        (∫u in (t n-2*D)..(t n),(1-d.C u (s n)^2)*d.R (t n) u)+
          primitive (q*d.C (t n) (s n)) (d.C (t n) (t n-2*D))-
          primitive (q*d.C (t n) (s n)) (d.C (t n) (s n+2*D))-
          windowError a (s n) (t n)-2*(1+windowError a (s n) (t n))*π/(q*d.C (t n) (s n)))
        atTop (𝓝 ((1-c (2*D))*(1-z^2)+primitive (q*z) (c (2*D))-
          primitive (q*z) z-ε-2*(1+ε)*π/(q*z))) := hlim
    apply le_of_tendsto_of_tendsto hlim' hI
    filter_upwards [hs.eventually (eventually_gt_atTop (0:ℝ)),
      hs.eventually (eventually_ge_atTop (S+D)),hgap.eventually (eventually_ge_atTop (4*D)),
      hk.eventually (lt_mem_nhds hqz)] with n hsn hnS hgn hκ
    have hg : s n+2*(2*D)≤t n := by linarith
    have hb := bulk_calibration h ha hsn (by linarith : s n≤s n+2*D)
      (by linarith : s n+2*D≤t n-2*D) (by linarith : t n-2*D≤t n) hκ hπ.le
      (fun u hu => by
        have hh := (hS S le_rfl (s n) u (t n) hnS hu.1 (by linarith [hu.2])).1
        have hl := le_max_left (d.C (t n) u*d.C u (s n)-q*d.C (t n) (s n)) 0
        change max (d.C (t n) u*d.C u (s n)-q*d.C (t n) (s n)) 0≤π at hh
        linarith)
    have hsplit := memory_split_lower h hsn.le (by positivity : 0≤2*D) hg
    linarith
  have hp0 : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (𝓝 (0:ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hl : Tendsto (fun n : ℕ => FisherCost.memoryMainTerm q z-ε-
      2*(1+ε)*(1/((n:ℝ)+1))/(q*z)) atTop (𝓝 (FisherCost.memoryMainTerm q z-ε)) := by
    simpa only [mul_zero,zero_div,sub_zero] using
      (tendsto_const_nhds (x:=FisherCost.memoryMainTerm q z-ε)).sub
        ((hp0.const_mul (2*(1+ε))).div_const (q*z))
  apply le_of_tendsto hl
  exact Eventually.of_forall (fun n => hfixed _ (by positivity))

end SphericalAging.FisherMemoryLower
