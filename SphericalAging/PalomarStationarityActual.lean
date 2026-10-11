module
public import SphericalAging.PalomarStationarity
public import SphericalAging.ActualSphereFisherTheorem
public import SphericalAging.ActualSphereCKIncrementControls

/-! Proposition 5.7 with all finite-model Fisher and increment interfaces
discharged by the literal spherical-diffusion construction. -/
public section
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency true

namespace SphericalAging.PalomarStationarityActual
open Set Filter MeasureTheory CKSpecification CKUniformLateEstimates
open ActualSphereFisherTheorem ActualSphereCKIncrementControls ActualSphereCKBridges
open AnnealedHamiltonianEnergyStein ActualSphereRestrictedFisherBudget
open SphereBadEventFisherMass PalomarStationarity
open scoped Topology NNReal

/-- Complete printed Proposition 5.7 for any CK solution. Its only premise
is the printed CK equations; the Fisher majorant, energy increment controls,
waiting increment controls, and their constants are all constructed. -/
theorem source5_7 {p : ℕ} {β : ℝ} {d : CKData} (hd : CKEquations p β d) :
    (∀ (T : ℕ → ℝ), Tendsto T atTop atTop →
      ∃ (C : ℝ × ℝ → ℝ) (R : ResponseCompactness.CausalOffsets → ℝ)
        (L : ℝ → ℝ) (φ : ℕ → ℕ),
        StrictMono φ ∧ RawTranslatedCluster d (T∘φ) C R L) ∧
    (∀ (T : ℕ → ℝ) (C : ℝ × ℝ → ℝ) (R : ResponseCompactness.CausalOffsets → ℝ)
      (L : ℝ → ℝ), RawTranslatedCluster d T C R L →
      ∃ (c r : ℝ → ℝ) (ell q e : ℝ), StationaryConclusions p β d T C R L c r ell q e) := by
  let b : ℝ≥0 := ⟨β,hd.beta_pos.le⟩
  have hd' : CKEquations p b d := hd
  let dim : ℕ → ℕ := fun n => n+3
  have hD n : 3≤dim n := by dsimp [dim];omega
  have hTop : Tendsto dim atTop atTop := tendsto_add_atTop_nat 3
  obtain ⟨φ,aF,hφ,han,ha,_,_,_,hFI,_⟩ := actual_FisherMajorant b hd' dim hD hTop
  let D : ℕ → ℕ := dim∘φ
  have hD' n : 3≤D n := hD (φ n)
  have hTop' : Tendsto D atTop atTop := hTop.comp hφ.tendsto_atTop
  have he := actual_energyIncrementControl D hD' hTop' hd.spin_ge_three b hd'.beta_pos
    d hd' ha.integrable hFI
  have hm := canonical_MeanBridge hd.spin_ge_three b hd'.beta_pos d hd' D hTop'
  have hw := actual_waitingControl D hD' hTop' (by have := hd.spin_ge_three;omega)
    b d ha.integrable hFI hm
  have hA : 0≤cutoff p := by
    unfold cutoff
    linarith [GaussianLandscape.landscapeThreshold_pos p]
  exact PalomarStationarity.source5_7 hd' ha han
    (fun _ _ => by positivity) hw (mul_nonneg (Nat.cast_nonneg p) hA) he

end SphericalAging.PalomarStationarityActual
