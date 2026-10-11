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
namespace SphericalAging.SphereActualMeanFisherChain
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereOnSphereCurrent SphereEnergyLimitTransfer SphereWaitingLimitTransfer
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive)
open SphereGoodEventFisherClock SphereBadEventFisherMass
open SphereActualClusterCompactness SphereSharpWaitingRealization HardSphereDynamics
open ActualSphereTransition CKSpecification StrongBackwardDefect StationaryMultiplierSelection
open scoped Topology NNReal

theorem actual_Fisher_chain_of_mean_dimensions {p : ℕ} {β : ℝ≥0} {d : CKData}
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
    ∃ (χ : ℕ→ℕ) (aF : ℝ→ℝ),StrictMono χ ∧ (∀s,0≤aF s) ∧
      FisherMajorant p β d aF ∧ (∫s in Ioi 0,aF s)≤(β:ℝ)^2/2 ∧
      (∀s,ContinuousWithinAt aF (Ici s) s) ∧
      Antitone (fun s => Real.exp (-ceilingRate p β (cutoff p)*s)*aF s) ∧
      (∀A : ℝ,Tendsto (fun n => ∫s in Ioc 0 A,|(E (χ n)).full s-aF s|) atTop (𝓝 0)) ∧
      Tendsto (FisherLimitClockDecay.lateSup aF) atTop (𝓝 0) ∧
      CKUniformLateEstimates.IncrementControl aF (CKSpecification.energy p β d) ((p:ℝ)*cutoff p) ∧
      CKUniformLateEstimates.WaitingControl d aF
        (fun L => 1+Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)) := by
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hTop.eventually_ge_atTop 3)
  let ψ : ℕ→ℕ := fun n => m+n
  have hψ : StrictMono ψ := by intro n k hnk;dsimp [ψ];omega
  have h3 n : 3≤dim (ψ n) := hm (ψ n) (by dsimp [ψ];omega)
  have hp : 2≤p := by have hh := h.spin_ge_three;omega
  obtain ⟨φ,aF,hφ,han,ha,hmass,hac,hclock,hFI,hlate,he⟩ :=
    SphereFisherEnergySubsequence.actual_Fisher_energy_refining_dimension_subsequence hp β.coe_nonneg h
      (fun n => dim (ψ n)) (fun n => by have hh := h3 n;omega) (hTop.comp hψ.tendsto_atTop)
      (fun n => E (ψ n)) (fun n => M (ψ n)) (fun n => hmeas (ψ n))
      (fun t s hs hst => (hlimit t s hs hst).comp hψ.tendsto_atTop)
      (fun n => hemeas (ψ n)) (fun t ht => (helimit t ht).comp hψ.tendsto_atTop)
  let B : ℝ→ℝ := fun L => Real.exp ((β:ℝ)*(p:ℝ)^2*cutoff p*L)
  have hDm : ∀n L,0≤L → ∀τ,0≤τ → τ≤L → ∀J∈goodEvent (dim (ψ (φ n))) p (cutoff p),
      ∀x,OnSphere x → ∀z,‖fderiv ℝ ((M (ψ (φ n))).m J τ) x (projection x z)‖≤B L*‖z‖ := by
    intro n L _ τ hτ hτL J hJ x hx v
    exact waiting_mean_derivative_bound (h3 (φ n)) hp
      (VectorBrownian.driver (dim (ψ (φ n)))) β (radius (ψ (φ n))) (hR (ψ (φ n))) (hNR (ψ (φ n)))
      (M (ψ (φ n))) J hJ hτ hτL (hmean (ψ (φ n)) J τ hτ) x v hx
  have hw := waitingControl_of_actual_correlation_limits (by omega : 1≤p) β.coe_nonneg
    (fun n => dim (ψ (φ n))) (fun n => by have hh := h3 (φ n);omega)
    (hTop.comp (hψ.comp hφ).tendsto_atTop) (fun n => E (ψ (φ n))) (fun n => M (ψ (φ n)))
    B (fun _ _ => Real.exp_nonneg _) hDm (fun n => hcmeas (ψ (φ n))) ha.integrable hFI
    (fun τ hτ s hs => (hclimit τ hτ s hs).comp (hψ.comp hφ).tendsto_atTop)
  exact ⟨ψ∘φ,aF,hψ.comp hφ,han,ha,hmass,hac,hclock,hFI,hlate,he,hw⟩

end SphericalAging.SphereActualMeanFisherChain
