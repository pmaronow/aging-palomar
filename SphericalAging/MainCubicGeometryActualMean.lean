module

public import SphericalAging.SphereActualMeanClusterCompactness
public import SphericalAging.MainCubicGeometryTheorem

public section

/-! Full printed cubic main theorem from actual canonical Wiener mean
realization and finite PDE dimension limits. Stationary compactness, Fisher
clock and waiting derivative estimates are constructed internally. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.MainCubicGeometryActualMean
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereOnSphereCurrent SphereEnergyLimitTransfer SphereWaitingLimitTransfer
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive)
open SphereActualMeanClusterCompactness HardSphereDynamics ActualSphereTransition
open CKSpecification MainCubicGeometryTheorem PlateauAlgebra AllTemperatureTheorem
open scoped Topology NNReal

theorem source1_3_from_actual_mean_dimensions {β : ℝ≥0} {d : CKData}
    (h : CKEquations 3 β d)
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (radius : ℕ→ℝ≥0) (hR : ∀n,0<(radius n:ℝ))
    (hNR : ∀n,(dim n:ℝ)<(radius n:ℝ)^2)
    (E : ∀n,FisherDensity (dim n) 3 β) (M : ∀n,SphereBackwardMean (dim n) 3 β)
    (hmean : ∀n J τ,0≤τ → ∀x,OnSphere x → (M n).m J τ x=
      mean (NullAugmentation.driver (VectorBrownian.driver (dim n))) β (radius n) (hR n) J τ.toNNReal x)
    (hmeas : ∀n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) 3))
    (hlimit : ∀t s,0≤s → s≤t → Tendsto (fun n => SphereOnSphereCurrent.annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s)))
    (hemeas : ∀n t,AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy (E n) J t) (disorderLaw (dim n) 3))
    (helimit : ∀t,0≤t → Tendsto (fun n => annealedEnergy (E n) t)
      atTop (𝓝 (CKSpecification.energy 3 β d t)))
    (hcmeas : ∀n τ,0≤τ → ∀s,0≤s → AEStronglyMeasurable
      (fun J => SphereQuenchedFDT.quenchedCorrelation ((E n).ρ J) ((M n).m J) (s+τ) s)
        (disorderLaw (dim n) 3))
    (hclimit : ∀τ,0≤τ → ∀s,0≤s → Tendsto
      (fun n => annealedCorrelation (E n) (M n) (s+τ) s) atTop (𝓝 (d.C (s+τ) s)))
    (hsector : transitionBetaSquared 3≤(β:ℝ)^2) :
    ∃q : ℝ,q=largerPlateau 3 β ∧ (1/2:ℝ)≤q ∧ PrintedProducts d q ∧
      ENNReal.ofReal (2*(1-q))≤liminf (fun t : ℝ => ENNReal.ofReal (susceptibility d t 0)) atTop ∧
      OrderedAging d q ∧ LastCrossings d q ∧ ((β:ℝ)^2=(4/3:ℝ) → q=1/2) := by
  obtain ⟨hc,aF,ha,_,_⟩ := compactness_and_Fisher_of_actual_mean_dimensions h
    dim hDim hTop radius hR hNR E M hmean hmeas hlimit hemeas helimit hcmeas hclimit
  exact source1_3_with_ordered_aging_and_last_crossings h hc hsector ⟨aF,ha⟩

end SphericalAging.MainCubicGeometryActualMean
