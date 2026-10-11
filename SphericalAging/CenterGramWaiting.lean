module

public import SphericalAging.CenterGramFinite
public import SphericalAging.CenterAverageReal
public import SphericalAging.RemoteForwardDerivative

public section

/-! Uniform waiting-time unnormalized Gram comparison for the actual tree centers.
Remote later derivatives and earlier smoothing are proved ingredients; no Gram
comparison or window-variation conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.CenterGramWaiting
open CKSpecification CKPhysicalConsequences CausalCenterAverage CenterAverageLimit CenterAverageReal
open PrefixReflection PrefixRectangleStability RemoteForwardDerivative EarlierSmoothing StrongBackwardDefect
open CenterGramFinite

/-- The actual all-p remote derivative estimate, uniformly over the whole late
half-plane, follows from the genuine real-ray reflected kernel limit. -/
theorem remote_derivative_waiting {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {c : ℝ → ℝ} (hc : ContDiffOn ℝ 2 c (Ioi 0))
    (hQ : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
      (fun T => Function.uncurry (futureKernel h T)) (fun z => c (z.1+z.2))
      atTop (square A)) {D ε : ℝ} (hD : 0 < D) (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, ∀ t s : ℝ, S+D ≤ t → 0 ≤ s → s+D ≤ t →
      |correlationSlope p β d t s| ≤ Real.sqrt (iteratedDeriv 2 c (2*D))+ε := by
  have he := remote_forward_derivative h (physical_bounds_of_equations h)
    (T := id) (eventually_ge_atTop (0 : ℝ)) hc hQ hD hε
  obtain ⟨U,hU⟩ := eventually_atTop.mp he
  filter_upwards [eventually_ge_atTop U] with S hS
  intro t s ht hs hst
  have hh := hU (t-D) (by linarith) s hs (by change s ≤ t-D; linarith)
  simpa only [id_eq,sub_add_cancel] using hh

/-- The source unnormalized Gram modulus, before taking the large-age limit. -/
@[expose] def gramError (c r : ℝ → ℝ) (D : ℝ) : ℝ :=
  2*Real.sqrt (errorLimit c D)+D*Real.sqrt (iteratedDeriv 2 c (2*D))+
    Real.sqrt D*Real.sqrt (responseTail r D)

/-- Actual uniform unnormalized center/endpoints Gram bound. All error terms
come from genuine projected derivatives, Bochner averages, and whole-row residuals. -/
theorem unnormalized_center_gram_waiting {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (hforget : ∀ s : ℝ, 0 ≤ s → Tendsto (fun t => d.C t s) atTop (nhds 0))
    {a : ℝ → ℝ} (ha : FisherMajorant p β d a) {c r : ℝ → ℝ}
    (hc : ContinuousOn c (Ici 0)) (hc2 : ContDiffOn ℝ 2 c (Ioi 0))
    (hr : ContinuousOn r (Ici 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (nhds 0))
    (hC : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
      (fun T (z : ℝ×ℝ) => d.C (T+z.1) (T+z.2)) (fun z => c |z.1-z.2|)
      atTop (square A))
    (hQ : ∀ A : ℝ, 0 ≤ A → TendstoUniformlyOn
      (fun T => Function.uncurry (futureKernel h T)) (fun z => c (z.1+z.2))
      atTop (square A))
    {D ε : ℝ} (hD : 0 < D) (hri : IntegrableOn (fun v => (r v)^2) (Ici D))
    (hε : 0 < ε) :
    ∀ᶠ S : ℝ in atTop, ∀ s t : ℝ, S+D ≤ s → s+2*D ≤ t →
      |inner ℝ (localCenter h (t-D) D) (localCenter h (s-D) D)-d.C t s| ≤
        gramError c r D+ε := by
  have hnorm := center_average_real_norm_limit h hc hD.le (hC D hD.le) (hQ D hD.le)
  have hnear := hnorm.eventually (gt_mem_nhds (by linarith :
    Real.sqrt (errorLimit c D) < Real.sqrt (errorLimit c D)+ε/4))
  obtain ⟨U,hU⟩ := eventually_atTop.mp hnear
  have hrem := remote_derivative_waiting h hc2 hQ hD (by positivity : 0 < ε/(4*D))
  have hearlier := earlier_smoothing h (physical_bounds_of_equations h) hforget ha hr hrow hD hri
    (by positivity : 0 < ε/4)
  filter_upwards [eventually_ge_atTop (max U 0),hrem,hearlier] with S hS hrem hearlier
  intro s t hs ht
  have hS0 : 0 ≤ S := (le_max_right U 0).trans hS
  have h1 := hU (t-D) (by linarith [le_max_left U 0])
  have h2 := hU (s-D) (by linarith [le_max_left U 0])
  have h3 := hearlier s t hs (by linarith)
  have h4 := center_endpoint_overlap_bound h hD (by linarith : D ≤ s) ht
    (M := Real.sqrt (iteratedDeriv 2 c (2*D))+ε/(4*D))
    (by positivity)
    (fun x hx y hy => hrem x y (by linarith [hx.1])
      (by linarith [hy.1]) (by linarith [hx.1,hy.2]))
  have he : D*(ε/(4*D))=ε/4 := by field_simp [hD.ne']
  unfold gramError
  nlinarith

end SphericalAging.CenterGramWaiting
