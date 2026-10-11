module

public import SphericalAging.SphereActualClusterCompactness
public import SphericalAging.SphereSharpWaitingRealization
public import SphericalAging.ActualSphereSemigroup

public section

/-! Actual mean realization removes the tangent-gradient premise in the
stationary CK compactness construction. Any preceding diverging dimension
sequence is retained after a finite prefix; all PDE and dimension-limit
realizations remain explicit preceding inputs. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace SphericalAging.SphereActualMeanClusterCompactness
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereOnSphereCurrent SphereEnergyLimitTransfer SphereWaitingLimitTransfer
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive)
open SphereGoodEventFisherClock SphereBadEventFisherMass
open SphereActualClusterCompactness SphereSharpWaitingRealization HardSphereDynamics
open ActualSphereTransition CKSpecification StrongBackwardDefect StationaryMultiplierSelection
open scoped Topology NNReal

theorem compactness_and_Fisher_of_actual_mean_dimensions {p : ℕ} {β : ℝ≥0} {d : CKData}
    (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (radius : ℕ→ℝ≥0) (hR : ∀n,0<(radius n:ℝ))
    (hNR : ∀n,(dim n:ℝ)<(radius n:ℝ)^2)
    (E : ∀n,FisherDensity (dim n) p β) (M : ∀n,SphereBackwardMean (dim n) p β)
    (hmean : ∀n J τ,0≤τ → ∀x,OnSphere x → (M n).m J τ x=
      mean (NullAugmentation.driver (VectorBrownian.driver (dim n))) β (radius n) (hR n) J τ.toNNReal x)
    (hmeas : ∀n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) p))
    (hlimit : ∀t s,0≤s → s≤t → Tendsto (fun n => SphereOnSphereCurrent.annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s)))
    (hemeas : ∀n t,AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy (E n) J t) (disorderLaw (dim n) p))
    (helimit : ∀t,0≤t → Tendsto (fun n => annealedEnergy (E n) t)
      atTop (𝓝 (CKSpecification.energy p β d t)))
    (hcmeas : ∀n τ,0≤τ → ∀s,0≤s → AEStronglyMeasurable
      (fun J => SphereQuenchedFDT.quenchedCorrelation ((E n).ρ J) ((M n).m J) (s+τ) s)
        (disorderLaw (dim n) p))
    (hclimit : ∀τ,0≤τ → ∀s,0≤s → Tendsto
      (fun n => annealedCorrelation (E n) (M n) (s+τ) s) atTop (𝓝 (d.C (s+τ) s))) :
    ClusterCompactness h ∧ ∃aF : ℝ→ℝ,FisherMajorant p β d aF ∧
      (∀s,0≤aF s) ∧ (∫s in Ioi 0,aF s)≤(β:ℝ)^2/2 := by
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hTop.eventually_ge_atTop 3)
  let ψ : ℕ→ℕ := fun n => m+n
  have hψ : StrictMono ψ := by intro n k hnk;dsimp [ψ];omega
  have h3 n : 3≤dim (ψ n) := hm (ψ n) (by dsimp [ψ];omega)
  let B : ℝ→ℝ := fun L => Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)
  apply compactness_and_Fisher_of_actual_dimensions h
    (fun n => dim (ψ n)) (fun n => by have hh := h3 n;omega)
    (hTop.comp hψ.tendsto_atTop) (fun n => E (ψ n)) (fun n => M (ψ n))
    (fun n => hmeas (ψ n)) (fun t s hs hst => (hlimit t s hs hst).comp hψ.tendsto_atTop)
    (fun n => hemeas (ψ n)) (fun t ht => (helimit t ht).comp hψ.tendsto_atTop)
    B (fun _ _ => Real.exp_nonneg _) ?_ (fun n => hcmeas (ψ n))
    (fun τ hτ s hs => (hclimit τ hτ s hs).comp hψ.tendsto_atTop)
  intro n L _ τ hτ hτL J hJ x hx v
  exact waiting_mean_derivative_bound (h3 n) (by have hp := h.spin_ge_three;omega)
    (VectorBrownian.driver (dim (ψ n))) β (radius (ψ n)) (hR (ψ n)) (hNR (ψ n))
    (M (ψ n)) J hJ hτ hτL (hmean (ψ n) J τ hτ) x v hx

end SphericalAging.SphereActualMeanClusterCompactness
