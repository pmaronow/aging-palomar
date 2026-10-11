module

public import SphericalAging.SphereOnlyActualForwardDerivativeTheorem
public import SphericalAging.SphereOnlyActualStationarySelection
public import SphericalAging.PurePActualPublishedFieldThreshold

public section

/-! The complete all-p extension of source Theorem11.4. The genuine
spherical construction and the native pure-p field threshold supply
all upstream mathematical inputs. A stationary profile can either be
specified through its actual cluster or constructed internally. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.ActualForwardDerivativeTheorem
open CKSpecification StationaryClusterInputs

/-- The literal causal-row conclusions, including the sharp remote
bound, uniform forward derivative limits and the diagonal identities. -/
@[expose] def Conclusions (p : ℕ) (β : ℝ≥0) (d : CKData) (c r : ℝ→ℝ) (q : ℝ) : Prop :=
    (∀L : ℝ,0<L→
      limsup (CausalRowSup.literalRowSup (correlationSlope p β d) L) atTop≤
        Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0

/-- Source11.4 for every admissible spin p>=3, with no field-threshold,
forgetting, reflected-kernel or strong-response premise. -/
theorem actual_source11_4 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) : Conclusions p β d c r q :=
  SphereOnlyActualForwardDerivativeTheorem.actual_source11_4 β H
    (fun Lip => PurePActualPublishedFieldThreshold.actual_published_field_threshold h.spin_ge_three Lip)

/-- The actual stationary profile and all source11.4 conclusions follow
from the genuine CK equations, with the cluster constructed internally. -/
theorem exists_actual_source11_4 {p : ℕ} (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d) :
    ∃ell q : ℝ,∃c r : ℝ→ℝ,∃T : ℕ→ℝ,
      Cluster h T c r ell q ∧ Conclusions p β d c r q := by
  obtain ⟨ell,q,c,r,T,H,_⟩ := SphereOnlyActualStationarySelection.actual_source8_4 β h
    (fun Lip => PurePActualPublishedFieldThreshold.actual_published_field_threshold h.spin_ge_three Lip)
  exact ⟨ell,q,c,r,T,H,actual_source11_4 β H⟩

end SphericalAging.ActualForwardDerivativeTheorem
