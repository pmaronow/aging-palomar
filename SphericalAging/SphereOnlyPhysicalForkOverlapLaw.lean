module

public import SphericalAging.PhysicalForkPairSampler
public import SphericalAging.ActualForkMomentTheorem
public import SphericalAging.FiniteForkCenterConcentration
public import Mathlib.Order.Filter.Curry
public import SphericalAging.PhysicalForkOverlapLaw
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! The genuine spliced physical branches have the exact independent-future
overlap law. Hence the actual source10.3 estimates apply to their literal
Gram matrix, including the ordered dimension-before-stationary-time limit. -/

noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology InnerProductSpace
namespace SphericalAging.SphereOnlyPhysicalForkOverlapLaw
open PhysicalForkOverlapLaw
open PhysicalForkOverlapLaw
open FiniteModel HardSphereDynamics AnnealedHamiltonianEnergyStein
open PhysicalForkConstruction PhysicalForkPairSampler
open ActualSphereForkMoment ActualSphereForkEndpoints CKSpecification StationaryClusterInputs
open ActualForkMeanBridge SphereFisherHelly
/-- Every distinct pair of the true finite whole-path fork satisfies
the actual source10.3 ordered uniform L² bound. All preceding inputs
concern CK means and Fisher extraction, not physical Gram errors. -/
theorem physical_branch_ordered_uniform_L2 {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    {L : ℝ} (hL : 0≤L) {ε : ℝ} (hε : 0<ε) (K : ℕ) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀a∈Icc 0 L,∀b∈Icc 0 L,
      ∀i k : Fin K,i≠k→
        (∫z : WienerForkTransfer.ForkSpace (dim j) p K,
          (⟪branch β ((T n).toNNReal+a.toNNReal) (T n).toNNReal i z,
            branch β ((T n).toNNReal+b.toNNReal) (T n).toNNReal k z⟫_ℝ/
              (dim j:ℝ)-c (a+b))^2 ∂WienerForkTransfer.forkLaw (dim j) p K)<ε := by
  have hh := ActualSphereOnlyForkUniformL2.actual_fork_ordered_uniform_L2 H hT dim hDim hTop
    (fun j => dim j+1) (fun j => modelRadius_pos (dim j))
    (fun j => modelRadius_sq (dim j)) hbridge hi hn hL1 hL hε
  filter_upwards [hh] with n hnε
  filter_upwards [hnε] with j hjε
  intro a ha b hb i k hik
  rw [branch_centered_secondMoment (by have hd:=hDim j;omega : 0<dim j)
    β (T n).toNNReal a.toNNReal b.toNNReal i k hik (c (a+b))]
  simpa only [Real.coe_toNNReal _ (hT n),Real.coe_toNNReal _ ha.1,
    Real.coe_toNNReal _ hb.1] using hjε a ha b hb

end SphericalAging.SphereOnlyPhysicalForkOverlapLaw
