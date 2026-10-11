module

public import SphericalAging.WeightedResponseIdentities

public section

/-! Genuine recent-strip power-weighted response limit for the actual CK
kernels. The integral limit follows from physical bounds and dominated convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.RecentWeightedResponseLimit
open CKSpecification CKPhysicalConsequences GeneralCenterDeficit PrefixRectangleStability
  GreenCovariance CKKernelBounds WeightedResponseIdentities

@[expose] def recentIntegrand (p : ℕ) (d : CKData) (t v : ℝ) : ℝ :=
  clampedCorrelation d t (t-v)^(p-1)*clampedResponse d t (t-v)

theorem recentIntegrand_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) : Continuous (recentIntegrand p d t) :=
  ((((clampedCorrelation_continuous h).comp
    (continuous_const.prodMk (continuous_const.sub continuous_id))).pow (p-1)).mul
    ((clampedResponse_continuous h).comp
      (continuous_const.prodMk (continuous_const.sub continuous_id))))

theorem recentIntegrand_bound {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t v : ℝ) : |recentIntegrand p d t v|≤1 := by
  have hb := physical_bounds_of_equations h
  have hc := hb.1 (max 0 t) (max 0 (t-v)) (le_max_left _ _) (le_max_left _ _)
  have hp : |clampedCorrelation d t (t-v)^(p-1)|≤1 := by
    rw [abs_pow]
    change |d.C (max 0 t) (max 0 (t-v))|^(p-1)≤1
    rw [abs_of_nonneg hc.1]
    exact pow_le_one₀ hc.1 hc.2
  unfold recentIntegrand
  rw [abs_mul]
  simpa only [one_mul] using mul_le_mul hp
    (clampedResponse_abs_le_one h hb t (t-v)) (abs_nonneg _) (by norm_num : (0:ℝ)≤1)

theorem recent_coefficients {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q A v : ℝ} (H : SelectedInputs h c r q)
    (hA : 0≤A) (hv : v∈Icc 0 A) :
    Tendsto (fun t : ℝ => d.C t (t-v)) atTop (𝓝 (c v)) ∧
      Tendsto (fun t : ℝ => d.R t (t-v)) atTop (𝓝 (r v)) := by
  have hs : Tendsto (fun t : ℝ => t-A) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-A)
      (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop)
  have hz : (A,A-v)∈triangle A := ⟨⟨hA,le_rfl⟩,⟨by linarith [hv.2],by linarith [hv.1]⟩⟩
  have hzs : (A,A-v)∈square A := ⟨hz.1,⟨hz.2.1,hz.2.2⟩⟩
  have hc := ((H.translated_correlation A hA).tendsto_at hzs).comp hs
  have hr := ((H.translated_response A hA).tendsto_at hz).comp hs
  have h1 : ∀t : ℝ,t-A+A=t := by intro t; ring
  have h2 : ∀t : ℝ,t-A+(A-v)=t-v := by intro t; ring
  have h3 : A-(A-v)=v := by ring
  constructor
  · simpa only [Function.comp_def,h1,h2,h3,abs_of_nonneg hv.1] using hc
  · simpa only [Function.comp_def,h1,h2,h3] using hr

theorem recent_weighted_response_limit {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q A : ℝ} (H : SelectedInputs h c r q) (hA : 0≤A) :
    Tendsto (fun t : ℝ => (p:ℝ)*(∫ u in t-A..t,d.C t u^(p-1)*d.R t u))
      atTop (𝓝 (1-c A^p)) := by
  have hi : Tendsto (fun t : ℝ => ∫ v in (0:ℝ)..A,recentIntegrand p d t v)
      atTop (𝓝 (∫ v in (0:ℝ)..A,c v^(p-1)*r v)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    · exact Eventually.of_forall (fun t => (recentIntegrand_continuous h t).aestronglyMeasurable)
    · exact Eventually.of_forall (fun t => ae_of_all _ (fun v _ => by
        simpa only [Real.norm_eq_abs] using recentIntegrand_bound h t v))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro v hv
      rw [uIoc_of_le hA] at hv
      have hcv := recent_coefficients H hA ⟨hv.1.le,hv.2⟩
      apply (hcv.1.pow (p-1) |>.mul hcv.2).congr'
      filter_upwards [eventually_ge_atTop A] with t ht
      unfold recentIntegrand
      rw [clampedCorrelation_eq (hA.trans ht) (by linarith [hv.2]),
        clampedResponse_eq (by linarith [hv.2]) (by linarith [hv.1])]
  have hl := hi.const_mul (p:ℝ)
  rw [profile_weighted_mass (by have hp:=h.spin_ge_three; omega) (profile H) hA] at hl
  apply hl.congr'
  filter_upwards [eventually_ge_atTop A] with t ht
  congr 1
  have he := intervalIntegral.integral_comp_sub_left
    (fun u => d.C t u^(p-1)*d.R t u) t (a:=0) (b:=A)
  simp only [sub_zero] at he
  rw [←he]
  apply intervalIntegral.integral_congr
  intro v hv
  rw [uIcc_of_le hA] at hv
  unfold recentIntegrand
  rw [clampedCorrelation_eq (hA.trans ht) (by linarith [hv.2]),
    clampedResponse_eq (by linarith [hv.2]) (by linarith [hv.1])]

end SphericalAging.RecentWeightedResponseLimit
