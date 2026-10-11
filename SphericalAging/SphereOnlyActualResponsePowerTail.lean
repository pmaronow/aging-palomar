module

public import SphericalAging.ActualStationaryResponseOrder
public import SphericalAging.ResponsePowerTail

public section

/-! The power-law clause of source 11.6 for every actual stationary
cluster. Its square-tail integrability is a theorem, and the source's
conditional Big-O hypothesis yields the exact printed smoothing rate. -/
noncomputable section
open Set Filter MeasureTheory
open scoped Topology NNReal
namespace SphericalAging.SphereOnlyActualResponsePowerTail
open CKSpecification StationaryClusterInputs ActualStationaryResponseOrder
open EarlierSmoothing ResponsePowerTail

theorem actual_response_square_tail_integrable {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) : IntegrableOn (fun v => (r v)^2) (Ici 0) := by
  have hi : IntegrableOn r (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr H.integrable_response
  exact MonotoneResponseTail.square_integrable_ray H.stationary.continuous_r
    (fun v hv => (H.physical v hv).1) (response_antitone H)
    (by rw [H.stationary.initial_r]) hi

/-- The final displayed conditional rate in Corollary 11.6. -/
theorem actual_response_smoothing_isBigO {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) {a : ℝ} (ha : 0<a)
    (hpower : Asymptotics.IsBigO atTop r (fun v : ℝ => v^(-1-a))) :
    Asymptotics.IsBigO atTop (fun D : ℝ => Real.sqrt D*Real.sqrt (responseTail r D))
      (fun D : ℝ => D^(-a)) :=
  power_smoothing_isBigO ha (actual_response_square_tail_integrable H) hpower

/-- Sharp coefficient before the asymptotic conclusion, with the literal
stationary response square-tail integral. -/
theorem actual_response_power_smoothing_bound {p : ℕ} {β ell q : ℝ} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ}
    (H : Cluster h T c r ell q) {a A D : ℝ} (ha : 0<a) (hA : 0≤A) (hD : 0<D)
    (hb : ∀v : ℝ,D≤v→|r v|≤A*v^(-1-a)) :
    Real.sqrt D*Real.sqrt (responseTail r D)≤A/Real.sqrt (1+2*a)*D^(-a) :=
  power_smoothing_bound ha hA hD
    ((actual_response_square_tail_integrable H).mono_set (Ici_subset_Ici.mpr hD.le)) hb

end SphericalAging.SphereOnlyActualResponsePowerTail
