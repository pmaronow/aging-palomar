module

public import SphericalAging.PhysicalForkPairSampler
public import SphericalAging.ActualForkMomentTheorem
public import SphericalAging.FiniteForkCenterConcentration
public import Mathlib.Order.Filter.Curry

public section

/-! The genuine spliced physical branches have the exact independent-future
overlap law. Hence the actual source10.3 estimates apply to their literal
Gram matrix, including the ordered dimension-before-stationary-time limit. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology InnerProductSpace
namespace SphericalAging.PhysicalForkOverlapLaw
open FiniteModel HardSphereDynamics AnnealedHamiltonianEnergyStein
open PhysicalForkConstruction PhysicalForkPairSampler
open ActualSphereForkMoment ActualSphereForkEndpoints CKSpecification StationaryClusterInputs
open ActualForkMeanBridge SphereFisherHelly
variable {N p K : ℕ}

theorem restartOverlap_eq_forkOverlap (β : ℝ≥0) (T a d : ℝ≥0)
    (z : PairSample N p) :
    restartOverlap (p:=p) β T a d z=
      ActualForkOverlapLaw.forkOverlap β (N+1) (modelRadius_pos N) T a d z := by
  simp only [restartOverlap,ActualForkOverlapLaw.forkOverlap,momentIntegrand,pow_one,
    endpoint,initialWaiting,jointEndpoint,FiniteCorrelationIto.overlap,NNReal.coe_add,
    NNReal.coe_natCast,NNReal.coe_one]

theorem branch_test_eq_actual_fork (hN : 0<N) (β : ℝ≥0) (T a d : ℝ≥0)
    (b c : Fin K) (hbc : b≠c) {f : ℝ→ℝ} (hf : Measurable f) :
    (∫z : WienerForkTransfer.ForkSpace N p K,
      f (⟪branch β (T+a) T b z,branch β (T+d) T c z⟫_ℝ/(N:ℝ))
        ∂WienerForkTransfer.forkLaw N p K)=
      ∫z : ActualForkOverlapLaw.ForkSample N p,
        f (ActualForkOverlapLaw.forkOverlap β (N+1) (modelRadius_pos N) T a d z)
          ∂ActualForkOverlapLaw.forkLaw N p := by
  rw [branch_test_integral hN (β:ℝ) T a d b c hbc hf]
  simp_rw [restartOverlap_eq_forkOverlap β T a d]
  rfl

/-- The squared physical Gram error is exactly the true source10.3
centered independent-future overlap error. -/
theorem branch_centered_secondMoment (hN : 0<N) (β : ℝ≥0) (T a d : ℝ≥0)
    (b c : Fin K) (hbc : b≠c) (z₀ : ℝ) :
    (∫z : WienerForkTransfer.ForkSpace N p K,
      (⟪branch β (T+a) T b z,branch β (T+d) T c z⟫_ℝ/(N:ℝ)-z₀)^2
        ∂WienerForkTransfer.forkLaw N p K)=
      ActualForkL2Estimate.centeredError (N:=N) (p:=p) β (N+1) (modelRadius_pos N)
        T a d z₀ := by
  have hh := branch_test_eq_actual_fork (p:=p) hN β T a d b c hbc
    (f:=fun x => (x-z₀)^2) (by fun_prop)
  simpa only [ActualForkL2Estimate.centeredError,Real.toNNReal_coe] using hh

theorem offdiagonal_gramError (hN : 0<N) (β : ℝ≥0) (T L : ℝ≥0)
    (b c : Fin K) (hbc : b≠c) (z₀ : ℝ) :
    (∫z : WienerForkTransfer.ForkSpace N p K,
      (FiniteForkCenterConcentration.gramError
        (fun i => branch β (T+L) T i z) z₀ b c)^2
        ∂WienerForkTransfer.forkLaw N p K)=
      ActualForkL2Estimate.centeredError (N:=N) (p:=p) β (N+1) (modelRadius_pos N)
        T L L z₀ := by
  simpa only [FiniteForkCenterConcentration.gramError,if_neg hbc] using
    branch_centered_secondMoment hN β T L L b c hbc z₀

/-- Every distinct pair of the true finite whole-path fork satisfies
the actual source10.3 ordered uniform L² bound. All preceding inputs
concern CK means and Fisher extraction, not physical Gram errors. -/
theorem physical_branch_ordered_uniform_L2 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    {L : ℝ} (hL : 0≤L) {ε : ℝ} (hε : 0<ε) (K : ℕ) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀a∈Icc 0 L,∀b∈Icc 0 L,
      ∀i k : Fin K,i≠k→
        (∫z : WienerForkTransfer.ForkSpace (dim j) p K,
          (⟪branch β ((T n).toNNReal+a.toNNReal) (T n).toNNReal i z,
            branch β ((T n).toNNReal+b.toNNReal) (T n).toNNReal k z⟫_ℝ/
              (dim j:ℝ)-c (a+b))^2 ∂WienerForkTransfer.forkLaw (dim j) p K)<ε := by
  have hh := ActualForkUniformL2.actual_fork_ordered_uniform_L2 H hT dim hDim hTop
    (fun j => dim j+1) (fun j => modelRadius_pos (dim j))
    (fun j => modelRadius_sq (dim j)) E hLaw hbridge hi hn hL1 hL hε
  filter_upwards [hh] with n hnε
  filter_upwards [hnε] with j hjε
  intro a ha b hb i k hik
  rw [branch_centered_secondMoment (by have hd:=hDim j;omega : 0<dim j)
    β (T n).toNNReal a.toNNReal b.toNNReal i k hik (c (a+b))]
  simpa only [Real.coe_toNNReal _ (hT n),Real.coe_toNNReal _ ha.1,
    Real.coe_toNNReal _ hb.1] using hjε a ha b hb

end SphericalAging.PhysicalForkOverlapLaw
