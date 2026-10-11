module

public import SphericalAging.SphereOnlyActualThresholdForgetting
public import SphericalAging.MainStationaryAgingTheorem

public section

/-! Main Theorem1.1 for every spin in the actual CK model. Actual spherical
Fisher dissipation, finite-fork threshold ceilings, and waiting orthogonality
supply all stationary selection and fixed-wait forgetting inputs. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.SphereOnlyMainStationaryAgingActualModel
open CKSpecification PlateauAlgebra AllTemperatureTheorem StationaryClusterInputs
open StationaryMultiplierSelection StationaryFamilySelection SelectedSectorTheorem
open ActualSphereCKFisherClosure SphereOnlyActualPrefixCeiling SphereOnlyActualThresholdForgetting
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false

theorem actual_source1_1 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      c 0=1 ∧ r 0=1 ∧
      (∀t : ℝ,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t) ∧
      ContDiffOn ℝ (⊤ : ℕ∞) c (Ioi 0) ∧
      (∀n : ℕ,∀t : ℝ,0<t → 0≤(-1:ℝ)^n*iteratedDeriv n c t) ∧
      (∀S : ℝ,0≤S → Tendsto (fun t : ℝ => sSup
        ((fun s => d.C t s+d.R t s) '' Icc 0 S)) atTop (𝓝 0)) ∧
      (transitionBetaSquared p≤β^2 →
        0<q ∧ q=largerPlateau p β ∧ transitionPlateau p≤q ∧
        β^2*marginalityPolynomial p q=1 ∧ ell=multiplier p β q ∧
        (ell-1)/((p:ℝ)*β)=selectedEnergy p β q ∧
        Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
        Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0)) := by
  let dim : ℕ→ℕ := fun n => n+3
  have hDim : ∀n,3≤dim n := fun n => by dsimp [dim];omega
  have hTop : Tendsto dim atTop atTop := by
    exact tendsto_atTop_mono (fun n => by dsimp [dim];omega) tendsto_id
  have hc := (actual_Fisher_closure β h dim hDim hTop).1
  exact MainStationaryAgingTheorem.source1_1 h hc (actual_prefixCeiling h hPub)
    (actual_thresholdForgetting β h dim hDim hTop hPub)

end SphericalAging.SphereOnlyMainStationaryAgingActualModel
