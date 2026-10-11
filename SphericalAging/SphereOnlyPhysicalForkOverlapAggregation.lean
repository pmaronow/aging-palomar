module

public import SphericalAging.SphereOnlyPhysicalForkOverlapLaw
public import SphericalAging.SphereOnlyPhysicalForkCenterConcentration
public import SphericalAging.SphereOnlyPhysicalForkNormalizationLimits
public import SphericalAging.SphereOnlyPhysicalForkNormTheorem
public import SphericalAging.PhysicalForkDiagonalOverlap
public import SphericalAging.FiniteScalarAverageMoments
public import SphericalAging.PhysicalForkOverlapAggregation
public import SphericalAging.ActualSphereOnlyForkUniformL2

public section

/-! The genuine fork mean's overlap with a branch's earlier state is an
average of the actual diagonal and distinct-branch overlaps. This derives
the source10.4 last-window mixed overlap, without a center-overlap premise. -/

noncomputable section
set_option maxHeartbeats 1900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereOnlyPhysicalForkOverlapAggregation
open PhysicalForkOverlapLaw PhysicalForkCenterConcentration PhysicalForkNormalizationLimits PhysicalForkNormTheorem PhysicalForkOverlapAggregation
open PhysicalForkOverlapAggregation
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open PhysicalForkConstruction SphereOnlyPhysicalForkOverlapLaw PhysicalForkDiagonalOverlap WienerForkTransfer
open FiniteScalarAverageMoments ForkParameterBounds AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly ActualSphereForkEndpoints
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators

/-- The source10.4 Step4 same-branch and mean-branch errors vanish
uniformly on the last-L window in the literal ordered limit. -/
theorem actual_late_overlap_ordered_uniform {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|ActualSphereRestrictedFisherBudget.full (N:=dim j) (p:=p) β (dim j+1) (modelRadius_pos (dim j)) w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀v∈Icc (0:ℝ) L,∀b : Fin K,
      (∫z : ForkSpace (dim j) p K,
        (pairOverlap β (T n).toNNReal L v.toNNReal b b z-c ((L:ℝ)-v))^2
          ∂forkLaw (dim j) p K)+
      (∫z : ForkSpace (dim j) p K,
        (meanOverlap β (T n).toNNReal L v.toNNReal b z-
          mixedOverlap c K L ((L:ℝ)-v))^2 ∂forkLaw (dim j) p K)<ε := by
  have hd := same_branch_ordered_uniform_L2 H hT dim hTop hbridge L
    (show 0<ε/4 by positivity) K
  have ho := SphereOnlyPhysicalForkOverlapLaw.physical_branch_ordered_uniform_L2 H hT dim hDim hTop hbridge
    hi hn hL1 L.coe_nonneg (show 0<ε/4 by positivity) K
  filter_upwards [hd,ho] with n hnd hno
  filter_upwards [hnd,hno] with j hjd hjo
  intro v hv b
  have hpair (k : Fin K) : (∫z : ForkSpace (dim j) p K,
      (pairOverlap β (T n).toNNReal L v.toNNReal b k z-
        pairTarget c L v.toNNReal b k)^2 ∂forkLaw (dim j) p K)≤ε/4 := by
    by_cases hkb : k=b
    · subst k
      simpa only [pairOverlap,pairTarget,ite_true,Real.coe_toNNReal _ hv.1] using (hjd v hv b).le
    · have hLmem : (L:ℝ)∈Icc (0:ℝ) L := ⟨L.coe_nonneg,le_rfl⟩
      simpa only [pairOverlap,pairTarget,if_neg hkb,Real.coe_toNNReal _ hv.1,Real.toNNReal_coe] using
        (hjo L hLmem v hv k b hkb).le
  have hmean := meanOverlap_error_le (N:=dim j) (p:=p) (by have hx:=hDim j;omega)
    hK β (T n).toNNReal L v.toNNReal b c (ε/4) hpair
  rw [Real.coe_toNNReal _ hv.1] at hmean
  have hdiag := hjd v hv b
  change (∫z : ForkSpace (dim j) p K,
    (pairOverlap β (T n).toNNReal L v.toNNReal b b z-c ((L:ℝ)-v))^2
      ∂forkLaw (dim j) p K)<ε/4 at hdiag
  linarith

end SphericalAging.SphereOnlyPhysicalForkOverlapAggregation
