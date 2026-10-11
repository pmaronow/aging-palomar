module

public import SphericalAging.ActualSphereOnlyForkL2Estimate
public import SphericalAging.ActualForkMeanBridge
public import SphericalAging.ForkOverlapSupLimit

public section

/-! Literal ordered dimension/late-time and lag-window-supremum L²
convergence of the actual two-independent-future overlap. Only the exact
preceding source3.3 mean bridge and source5.3 Fisher extraction are inputs. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualSphereOnlyForkUniformL2
open Set Filter MeasureTheory FiniteModel CKSpecification StationaryClusterInputs
open ActualForkL2Estimate ActualSphereOnlyForkL2Estimate ActualForkMeanBridge ForkOverlapSupLimit
open ActualSphereForkEndpoints ActualSphereOnlyTensorUniformComparison ActualForkFisherWindowLimit ActualSphereRestrictedFisherBudget
open ActualCompactJointOverlapVariance
open scoped Topology NNReal

theorem actual_fork_ordered_uniform_L2 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ)) (hNR : ∀j,(dim j:ℝ)<(R j:ℝ)^2)
    (hbridge : MeanBridge (p:=p) β dim R hR d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|full (N:=dim j) (p:=p) β (R j) (hR j) w-f w|) atTop (𝓝 0))
    {L : ℝ} (hL : 0≤L) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀a∈Icc 0 L,∀b∈Icc 0 L,
      centeredError (N:=dim j) (p:=p) β (R j) (hR j) (T n) a b (c (a+b))<ε := by
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  have hm := actualMean_ordered_uniform_profile H hT dim R hR hbridge hL
    (show 0<Real.sqrt (ε/3) from Real.sqrt_pos.mpr (by positivity))
  have he := ordered_comparisonError_eventually (by omega : 1≤p) β dim hDim hTop R hR hNR
    hi hn hL1 (show 0≤windowCoefficient p 2 β L by unfold windowCoefficient;positivity)
    hL T H.late (show 0<ε/9 by positivity)
  filter_upwards [hm,he] with n hnm hne
  have hv : Tendsto (fun j => jointVarianceCeiling p β (T n+3*L+1).toNNReal/(dim j:ℝ))
      atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (jointVarianceCeiling p β (T n+3*L+1).toNNReal)).comp hTop
  filter_upwards [hnm,hne,hTop.eventually_ge_atTop 3,
    (tendsto_order.1 hv).2 (ε/3) (by positivity)] with j hjm hje hj3 hjv
  intro a ha b hb
  have hc : |c (a+b)|≤1 := by
    rw [abs_of_nonneg (H.profile.bounds (a+b) (by linarith [ha.1,hb.1])).1]
    exact (H.profile.bounds (a+b) (by linarith [ha.1,hb.1])).2
  have hh := actual_fork_centered_secondMoment_le hj3 hp β (R j) (hR j) (hNR j)
    (hT n) ha hb hc
  obtain ⟨hs,ht⟩ := toNNReal_fork_times (hT n) ha.1 hb.1
  rw [ht,hs] at hh
  change centeredError (N:=dim j) (p:=p) β (R j) (hR j) (T n) a b (c (a+b))≤
    jointVarianceCeiling p β (T n+3*L+1).toNNReal/(dim j:ℝ)+
    (actualMean (N:=dim j) (p:=p) β (R j) (hR j) (T n+a) (T n+2*a+b)-c (a+b))^2+
    3*comparisonError (N:=dim j) (p:=p) (windowCoefficient p 2 β L) L β (R j) (hR j) (T n) at hh
  have hma := hjm a ha b hb
  have hmsq : (actualMean (N:=dim j) (p:=p) β (R j) (hR j) (T n+a) (T n+2*a+b)-c (a+b))^2<ε/3 := by
    have hsqrt := Real.sq_sqrt (by positivity : 0≤ε/3)
    have habs := sq_abs (actualMean (N:=dim j) (p:=p) β (R j) (hR j) (T n+a) (T n+2*a+b)-c (a+b))
    nlinarith [abs_nonneg (actualMean (N:=dim j) (p:=p) β (R j) (hR j) (T n+a) (T n+2*a+b)-c (a+b)),
      Real.sqrt_nonneg (ε/3)]
  linarith

/-- The exact printed source10.3 order: dimension limsup of the full
closed lag-window supremum, followed by the late stationary-cluster limit. -/
theorem actual_fork_overlap_concentration {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ)) (hNR : ∀j,(dim j:ℝ)<(R j:ℝ)^2)
    (hbridge : MeanBridge (p:=p) β dim R hR d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|full (N:=dim j) (p:=p) β (R j) (hR j) w-f w|) atTop (𝓝 0))
    {L : ℝ} (hL : 0≤L) :
    Tendsto (fun n => limsup (fun j => sSup ((fun z : ℝ×ℝ =>
      centeredError (N:=dim j) (p:=p) β (R j) (hR j) (T n) z.1 z.2 (c (z.1+z.2))) ''
        (Icc 0 L×ˢIcc 0 L))) atTop) atTop (𝓝 0) := by
  apply ordered_uniform_limsup (M:=4) hL
  · intro n j z hz
    have hc := H.profile.bounds (z.1+z.2) (by linarith [hz.1.1,hz.2.1])
    exact (centeredError_bounds (by have hj:=hDim j;omega : 0<dim j) β (R j) (hR j) (hNR j)
      (T n) z.1 z.2 (c (z.1+z.2)) (by rw [abs_of_nonneg hc.1];exact hc.2)).1
  · intro n j z hz
    have hc := H.profile.bounds (z.1+z.2) (by linarith [hz.1.1,hz.2.1])
    exact (centeredError_bounds (by have hj:=hDim j;omega : 0<dim j) β (R j) (hR j) (hNR j)
      (T n) z.1 z.2 (c (z.1+z.2)) (by rw [abs_of_nonneg hc.1];exact hc.2)).2
  · intro ε hε
    have hh := actual_fork_ordered_uniform_L2 H hT dim hDim hTop R hR hNR hbridge hi hn hL1 hL hε
    filter_upwards [hh] with n hnε
    filter_upwards [hnε] with j hjε
    intro z hz
    exact hjε z.1 hz.1 z.2 hz.2

end SphericalAging.ActualSphereOnlyForkUniformL2
