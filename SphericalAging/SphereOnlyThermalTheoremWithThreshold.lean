module

public import SphericalAging.SphereOnlyResponseCorollariesWithThreshold

public section

/-! Every assertion of source thermal Corollary 11.7 for the literal
spherical diffusion, with all spectral and response inputs derived. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped NNReal Topology Asymptotics
namespace SphericalAging.SphereOnlyThermalTheoremWithThreshold
open CKSpecification StationaryClusterInputs
open BackwardRowL2 ThermalRowConvergence ThermalAging
open SphereOnlyResponseCorollariesWithThreshold

theorem actual_source11_7 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    (hthreshold : FixedWaitingForgettingTheorem.ThresholdForgetting h) :
    Tendsto (LateTriangleSup.lateSup
      (fun t s => |GreenCovariance.whiteTerm d t s-thermalProfile r (t-s)|) 0) atTop (𝓝 0) ∧
    ContDiffOn ℝ (⊤ : ℕ∞) (thermalProfile r) (Ioi 0) ∧
    (∀n : ℕ,∀τ : ℝ,0<τ→0≤(-1:ℝ)^n*iteratedDeriv n (thermalProfile r) τ) ∧
    Tendsto (thermalProfile r) atTop (𝓝 0) ∧
    Tendsto (fun t => GreenCovariance.whiteTerm d t t) atTop
      (𝓝 (2*(∫v : ℝ,(r v)^2 ∂rayMeasure))) ∧
    (∀{ι : Type*} {F : Filter ι} {t s : ι→ℝ},Tendsto s F atTop→
      Tendsto (fun n => t n-s n) F atTop→
      Tendsto (fun n => GreenCovariance.whiteTerm d (t n) (s n)) F (𝓝 0)) ∧
    (∀{ι : Type*} {F : Filter ι} {t s : ι→ℝ} {c₀ : ℝ},Tendsto s F atTop→
      Tendsto (fun n => t n-s n) F atTop→
      Tendsto (fun n => d.C (t n) (s n)) F (𝓝 c₀)→
      Tendsto (fun n => β^2*(p:ℝ)*(∫u in (0:ℝ)..t n,∫v in (0:ℝ)..s n,
        d.R (t n) u*d.R (s n) v*(d.C u v)^(p-1))) F (𝓝 c₀)) ∧
    (∀ a A : ℝ, 0 < a → 0 < A → (r ~[atTop] (fun τ : ℝ => a*A*τ^(-1-a))) →
      (thermalProfile r ~[atTop] (fun τ => 2*(1-q)*r τ)) ∧
      (thermalProfile r ~[atTop] (fun τ : ℝ => 2*(1-q)*a*A*τ^(-1-a)))) :=
  ThermalTheorem.source11_7 (actual_thermal_inputs β H hThreshold hthreshold)

end SphericalAging.SphereOnlyThermalTheoremWithThreshold
