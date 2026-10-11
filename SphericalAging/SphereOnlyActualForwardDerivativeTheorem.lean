module

public import SphericalAging.SphereOnlyForwardDerivativeWithThreshold
public import SphericalAging.SphereOnlyActualThresholdForgetting

public section

/-! Theorem 11.4 holds for every p>=3, with all actual-diffusion inputs
constructed. Both literal causal-row suprema and the sharp remote envelope
are included. Only published field threshold 10.1 remains explicit. -/
noncomputable section
open Set Filter MeasureTheory
open scoped NNReal Topology
namespace SphericalAging.SphereOnlyActualForwardDerivativeTheorem
open CKSpecification StationaryClusterInputs
open SphereOnlyForwardDerivativeWithThreshold SphereOnlyActualThresholdForgetting

theorem actual_source11_4 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    :
    (∀L : ℝ,0<L→
      limsup (CausalRowSup.literalRowSup (correlationSlope p β d) L) atTop≤
        Real.sqrt (iteratedDeriv 2 c (2*L)) ∧
      Real.sqrt (iteratedDeriv 2 c (2*L))≤Real.sqrt (1-q)/(Real.exp 1*L)) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+r (t-s)) 0) atTop (𝓝 0) ∧
    Tendsto (CausalRowSup.literalRowSup
      (fun t s => correlationSlope p β d t s+d.R t s) 0) atTop (𝓝 0) ∧
    (∀t : ℝ,0≤t→correlationSlope p β d t t= -1) ∧
    HasDerivWithinAt c (-1) (Ici 0) 0 := by
  exact SphereOnlyForwardDerivativeWithThreshold.actual_source11_4 β H hThreshold
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hThreshold)

end SphericalAging.SphereOnlyActualForwardDerivativeTheorem
