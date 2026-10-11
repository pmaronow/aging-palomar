module

public import SphericalAging.SphereOnlyResponseCorollariesWithThreshold
public import SphericalAging.SphereOnlyThermalTheoremWithThreshold
public import SphericalAging.SphereOnlyActualResponsePowerTail
public import SphericalAging.SphereOnlyActualThresholdForgetting

public section

/-! Source 11.2 and 11.5--11.7 from the literal spherical diffusion for
all p>=3. Actual Fisher information, Gaussian query-history forgetting,
strong response rows and thermal spectral laws are proved internally.
Only the published algorithmic field threshold 10.1 remains explicit. -/
noncomputable section
open Set Filter MeasureTheory Asymptotics
open scoped NNReal Topology ENNReal Asymptotics
namespace SphericalAging.SphereOnlyActualResponseCorollaries
open CKSpecification StationaryClusterInputs FixedWaitingForgettingTheorem
open BackwardRowL2 BackwardStrongTheorem StrongBackwardDefect
open EarlierCovariance EarlierSmoothing RemoteEarlierTheorem
open ThermalRowConvergence ThermalAging
open SphereOnlyResponseCorollariesWithThreshold SphereOnlyActualThresholdForgetting

theorem actual_source11_2 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    :
    Tendsto (UniformResponseRows.rowSup d r) atTop (𝓝 0) ∧
    ∀s t : ℕ→ℝ,Tendsto s atTop atTop→Tendsto (fun n => t n-s n) atTop atTop→
      Tendsto (fun n => d.R (t n) (s n)) atTop (𝓝 0) := by
  exact SphereOnlyResponseCorollariesWithThreshold.actual_source11_2 β H hThreshold
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hThreshold)

theorem actual_source11_5 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    :
    (∀S : ℝ,0≤S→Tendsto (fixedWaitSup (earlierSlope p β d) S) atTop (𝓝 0)) ∧
    Tendsto (fun t => ∫s in (0:ℝ)..t,|backwardDefect p β d t s|^2) atTop (𝓝 0) ∧
    Tendsto (fun t => (eLpNorm (fun v => sourceEarlierRow p β d t v-r v) 2 rayMeasure).toReal)
      atTop (𝓝 0) := by
  exact SphereOnlyResponseCorollariesWithThreshold.actual_source11_5 β H hThreshold
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hThreshold)

theorem actual_source11_6 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    :
    Tendsto (fun D : ℝ => limsup (LateTriangleSup.lateSup
      (pointQuantity p β d) D) atTop) atTop (𝓝 0) ∧
    ∀D : ℝ,0<D→limsup (fun S : ℝ => LateTriangleSup.lateSup
      (windowQuantity p β d D) D (S+D)) atTop≤
        Real.sqrt D*Real.sqrt (responseTail r D) := by
  exact SphereOnlyResponseCorollariesWithThreshold.actual_source11_6 β H hThreshold
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hThreshold)

theorem actual_thermal_inputs {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    : ThermalTheorem.Inputs h c r q := by
  exact SphereOnlyResponseCorollariesWithThreshold.actual_thermal_inputs β H hThreshold
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hThreshold)

theorem actual_source11_7 {p : ℕ} (β : ℝ≥0) {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q)
    (hThreshold : ∀Lip,ExternalFieldUniformCost.PublishedFieldThreshold p Lip)
    :
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
      (thermalProfile r ~[atTop] (fun τ : ℝ => 2*(1-q)*a*A*τ^(-1-a)))) := by
  exact SphereOnlyThermalTheoremWithThreshold.actual_source11_7 β H hThreshold
    (actual_thresholdForgetting β h (fun j => j+3) (fun j => by omega)
      (tendsto_add_atTop_nat 3) hThreshold)

end SphericalAging.SphereOnlyActualResponseCorollaries
