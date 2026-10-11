module

public import SphericalAging.SphereFisherEnergySubsequence
public import SphericalAging.SphereWaitingLimitTransfer
public import SphericalAging.CKStationaryClusterExtraction

public section

/-! Actual finite-dimensional Fisher extraction, fixed-horizon dimension limits,
and a genuine good-landscape tangent derivative bound construct the stationary
CK compactness receipt. No Fisher clock or CK increment/compactness target is
assumed. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereActualClusterCompactness
open Set Filter MeasureTheory FiniteModel SphereInitialLaw SphereFisherHelly
open SphereOnSphereCurrent SphereOnSphereFisherMajorant SphereFisherEnergySubsequence
open SphereWaitingLimitTransfer SphereEnergyLimitTransfer SphereQuenchedFDT
open SphereAnnealedCurrentFDT (rowPrimitive)
open SphereCKFisherMajorant (ckRowPrimitive)
open SphereGoodEventFisherClock SphereBadEventFisherMass GaussianLandscape SphereRotationGeometry HardSphereDynamics
open CKSpecification StrongBackwardDefect CKStationaryClusterExtraction StationaryClusterInputs StationaryMultiplierSelection
open scoped Topology

theorem compactness_and_Fisher_of_actual_dimensions {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d)
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hTop : Tendsto dim atTop atTop)
    (E : ∀n,FisherDensity (dim n) p β) (M : ∀n,SphereBackwardMean (dim n) p β)
    (hmeas : ∀n t s,AEStronglyMeasurable
      (fun J => rowPrimitive ((E n).ρ J) ((M n).m J) t s) (disorderLaw (dim n) p))
    (hlimit : ∀t s,0≤s → s≤t → Tendsto (fun n => annealedRowPrimitive (E n) (M n) t s)
      atTop (𝓝 (ckRowPrimitive d t s)))
    (hemeas : ∀n t,AEStronglyMeasurable
      (fun J => SphereEnergyCurrent.energy (E n) J t) (disorderLaw (dim n) p))
    (helimit : ∀t,0≤t → Tendsto (fun n => annealedEnergy (E n) t)
      atTop (𝓝 (CKSpecification.energy p β d t)))
    (B : ℝ→ℝ) (hB : ∀L,0≤L → 0≤B L)
    (hDm : ∀n L,0≤L → ∀τ,0≤τ → τ≤L → ∀J∈goodEvent (dim n) p (cutoff p),
      ∀x,OnSphere x → ∀z,‖fderiv ℝ ((M n).m J τ) x (projection x z)‖≤B L*‖z‖)
    (hcmeas : ∀n τ,0≤τ → ∀s,0≤s → AEStronglyMeasurable
      (fun J => quenchedCorrelation ((E n).ρ J) ((M n).m J) (s+τ) s) (disorderLaw (dim n) p))
    (hclimit : ∀τ,0≤τ → ∀s,0≤s → Tendsto
      (fun n => annealedCorrelation (E n) (M n) (s+τ) s) atTop (𝓝 (d.C (s+τ) s))) :
    ClusterCompactness h ∧ ∃aF : ℝ→ℝ,FisherMajorant p β d aF ∧
      (∀s,0≤aF s) ∧ (∫s in Ioi 0,aF s)≤β^2/2 := by
  have hp := h.spin_ge_three
  obtain ⟨φ,aF,hφ,han,ha,hmass,_,_,hFI,_,he⟩ :=
    actual_Fisher_energy_refining_dimension_subsequence (by omega : 2≤p) h.beta_pos.le h
      dim hDim hTop E M hmeas hlimit hemeas helimit
  have hw := waitingControl_of_actual_correlation_limits (by omega : 1≤p) h.beta_pos.le
    (fun n => dim (φ n)) (fun n => hDim (φ n)) (hTop.comp hφ.tendsto_atTop)
    (fun n => E (φ n)) (fun n => M (φ n)) B hB
    (fun n => hDm (φ n)) (fun n => hcmeas (φ n)) ha.integrable hFI
    (fun τ hτ s hs => (hclimit τ hτ s hs).comp hφ.tendsto_atTop)
  have hB' : ∀L,0≤L → 0≤1+B L := fun L hL => by linarith [hB L hL]
  have hE : 0≤(p:ℝ)*cutoff p := by
    have hc : 0≤cutoff p := by unfold cutoff;linarith [landscapeThreshold_pos p]
    exact mul_nonneg (Nat.cast_nonneg p) hc
  exact ⟨clusterCompactness_of_Fisher_increment_controls h ha han hB' hw hE he,
    aF,ha,han,hmass⟩

end SphericalAging.SphereActualClusterCompactness
