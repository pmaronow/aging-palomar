module

public import SphericalAging.FisherWindowEnds

public section

/-! Genuine recent-strip memory limit and the two actual bulk endpoint limits. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherRecentStrip
open CKSpecification CKPhysicalConsequences GreenCovariance BackwardResponse
open StrongBackwardDefect FisherWindowEnds CubicResponseLocalization PrefixRectangleStability

theorem recent_correlation_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ} {z W τ : ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z)) (hW : 0<W) (hτ : τ∈Icc 0 W) :
    Tendsto (fun n => d.C (t n-τ) (s n)) atTop (𝓝 z) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hc := Metric.tendsto_nhds.mp hC (ε/2) (by positivity)
  filter_upwards [recent_correlation_uniform H hf ha hs hgap hW (by positivity : 0<ε/2),hc]
    with n hn hc
  have hh := hn (t n-τ) ⟨by linarith [hτ.2],by linarith [hτ.1]⟩
  rw [Real.dist_eq] at hc ⊢
  have he := abs_sub_le (d.C (t n-τ) (s n)) (d.C (t n) (s n)) z
  linarith

theorem response_point_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) {W τ : ℝ} (hW : 0≤W) (hτ : τ∈Icc 0 W) :
    Tendsto (fun n => d.R (t n) (t n-τ)) atTop (𝓝 (r τ)) := by
  have hh := (H.translated_response W hW).tendsto_at (x:=(W,W-τ))
    ⟨⟨hW,le_rfl⟩,⟨by linarith [hτ.2],by linarith [hτ.1]⟩⟩
  have hshift : Tendsto (fun n => t n-W) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-W) ht
  simpa only [Function.comp_def,sub_add_cancel,show W-(W-τ)=τ by ring,
    show ∀x : ℝ,x-W+(W-τ)=x-τ by intro x; ring] using hh.comp hshift

theorem recent_endpoint_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    {t : ℕ → ℝ} (ht : Tendsto t atTop atTop) {W : ℝ} (hW : 0≤W) :
    Tendsto (fun n => d.C (t n) (t n-W)) atTop (𝓝 (c W)) := by
  have hh := (H.translated_correlation W hW).tendsto_at (x:=(W,0))
    ⟨⟨hW,le_rfl⟩,⟨le_rfl,hW⟩⟩
  have hshift : Tendsto (fun n => t n-W) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-W) ht
  simpa only [Function.comp_def,sub_add_cancel,add_zero,sub_zero,abs_of_nonneg hW] using hh.comp hshift

theorem recent_memory_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ → ℝ} (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ} {z W : ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z)) (hW : 0<W) :
    Tendsto (fun n => ∫ u in (t n-W)..(t n),(1-d.C u (s n)^2)*d.R (t n) u)
      atTop (𝓝 ((1-c W)*(1-z^2))) := by
  have hb := physical_bounds_of_equations h
  have ht : Tendsto t atTop atTop := by
    apply tendsto_atTop_mono' atTop _ hs
    filter_upwards [hgap.eventually (eventually_ge_atTop (0:ℝ))] with n hn
    linarith
  let F : ℕ → ℝ → ℝ := fun n τ =>
    (1-clampedCorrelation d (t n-τ) (s n)^2)*clampedResponse d (t n) (t n-τ)
  have hFc (n : ℕ) : Continuous (F n) := by
    exact (continuous_const.sub (((clampedCorrelation_continuous h).comp
      ((continuous_const.sub continuous_id).prodMk continuous_const)).pow 2)).mul
      ((clampedResponse_continuous h).comp
        (continuous_const.prodMk (continuous_const.sub continuous_id)))
  have hFbound (n : ℕ) (τ : ℝ) : ‖F n τ‖≤1 := by
    have hc := hb.1 (max 0 (t n-τ)) (max 0 (s n)) (le_max_left _ _) (le_max_left _ _)
    have hr := response_correlation_bounds h hb (le_max_left (0:ℝ) (t n-τ))
      (le_max_right (t n) (max 0 (t n-τ)))
    change |(1-d.C (max 0 (t n-τ)) (max 0 (s n))^2)*
      d.R (max (t n) (max 0 (t n-τ))) (max 0 (t n-τ))|≤1
    rw [abs_of_nonneg (mul_nonneg (by nlinarith [hc.1,hc.2]) hr.1)]
    nlinarith [sq_nonneg (d.C (max 0 (t n-τ)) (max 0 (s n)))]
  have hp (τ : ℝ) (hτ : τ∈Icc 0 W) : Tendsto (fun n => F n τ) atTop (𝓝 ((1-z^2)*r τ)) := by
    have h1 := recent_correlation_tendsto H hf ha hs hgap hC hW hτ
    have h2 := response_point_tendsto H ht hW.le hτ
    have hl := ((tendsto_const_nhds (x:=(1:ℝ))).sub (h1.pow 2)).mul h2
    apply hl.congr'
    filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),ht.eventually (eventually_ge_atTop W)]
      with n hsn htn
    dsimp only [F]
    rw [clampedCorrelation_eq (by linarith [hτ.2]) hsn,
      clampedResponse_eq (by linarith [hτ.2]) (by linarith [hτ.1])]
  have hi : Tendsto (fun n => ∫τ in (0:ℝ)..W,F n τ) atTop
      (𝓝 (∫τ in (0:ℝ)..W,(1-z^2)*r τ)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (1:ℝ))
    · exact Eventually.of_forall (fun n => (hFc n).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => ae_of_all _ (fun τ _ => hFbound n τ))
    · exact intervalIntegrable_const
    · apply ae_of_all
      intro τ hτ
      rw [uIoc_of_le hW.le] at hτ
      exact hp τ (Ioc_subset_Icc_self hτ)
  rw [intervalIntegral.integral_const_mul,
    ForkParameterBounds.response_interval_mass (profile H) hW.le,
    mul_comm (1-z^2)] at hi
  apply hi.congr'
  filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),ht.eventually (eventually_ge_atTop W)]
    with n hsn htn
  have heq : (∫τ in (0:ℝ)..W,F n τ)=
      ∫τ in (0:ℝ)..W,(1-d.C (t n-τ) (s n)^2)*d.R (t n) (t n-τ) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le hW.le] at hτ
    dsimp only [F]
    rw [clampedCorrelation_eq (by linarith [hτ.2]) hsn,
      clampedResponse_eq (by linarith [hτ.2]) (by linarith [hτ.1])]
  rw [heq]
  simpa only [sub_zero] using intervalIntegral.integral_comp_sub_left
    (a:=0) (b:=W) (fun u => (1-d.C u (s n)^2)*d.R (t n) u) (t n)

end SphericalAging.FisherRecentStrip
