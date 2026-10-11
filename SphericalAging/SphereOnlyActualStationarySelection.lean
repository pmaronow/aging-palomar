module

public import SphericalAging.SphereOnlyActualPrefixCeiling
public import SphericalAging.ActualSphereCKFisherClosure
public import SphericalAging.AllTemperatureTheorem

public section

/-! Source8.4 for every actual spin model. The actual sphere-only Fisher
construction supplies compactness, and genuine finite forks give each
cluster its threshold ceiling before whole-family profile selection. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.SphereOnlyActualStationarySelection
open CKSpecification PlateauAlgebra StationaryClusterInputs StationaryMultiplierSelection
open StationaryFamilySelection AllTemperatureTheorem
open ActualSphereCKFisherClosure SphereOnlyActualPrefixCeiling
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

theorem actual_source8_4 {p : ℕ} (β : ℝ≥0) {d : CKData} (h : CKEquations p β d)
    (hPub : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip) :
    ∃ell q : ℝ,∃c r : ℝ → ℝ,∃T : ℕ → ℝ,
      Cluster h T c r ell q ∧
      Tendsto d.multiplier atTop (𝓝 ell) ∧
      Tendsto (energy p β d) atTop (𝓝 ((ell-1)/((p:ℝ)*β))) ∧
      (∀A : ℝ,0≤A → Tendsto (windowSup d c r A) atTop (𝓝 0)) ∧
      (q=0 ∨ q=largerPlateau p β) ∧
      (β^2<spinodalBetaSquared p → q=0) ∧
      ell=multiplier p β q ∧
      (∀U c' r' ell' q',Cluster h U c' r' ell' q' →
        ell'=ell ∧ ∀t : ℝ,0≤t → c' t=c t ∧ r' t=r t) := by
  let dim : ℕ→ℕ := fun n => n+3
  have hDim : ∀n,3≤dim n := fun n => by dsimp [dim];omega
  have hTop : Tendsto dim atTop atTop := tendsto_add_atTop_nat 3
  exact source8_4 h (actual_Fisher_closure β h dim hDim hTop).1 (actual_prefixCeiling h hPub)

end SphericalAging.SphereOnlyActualStationarySelection
