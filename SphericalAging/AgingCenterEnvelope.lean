module

public import SphericalAging.AgingCenterGramSup

public section

/-! Literal source limsup remote-covariance envelope. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.AgingCenterEnvelope
open CKSpecification CKPhysicalConsequences AgingCenterGram

theorem remote_covariance_limsup {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ→ℝ} {q : ℝ} (H : Inputs h c r q) {s t : ℕ→ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop) :
    limsup (fun n => d.C (t n) (s n)) atTop≤q := by
  have hnonneg : ∀ᶠ n in atTop,0≤d.C (t n) (s n) := by
    filter_upwards [hs.eventually (eventually_ge_atTop (0:ℝ)),
      hgap.eventually (eventually_ge_atTop (0:ℝ))] with n hn hg
    have ht : 0≤t n := by linarith
    exact ((physical_bounds_of_equations h).1 (t n) (s n) ht hn).1
  apply le_of_forall_pos_le_add
  intro ε hε
  exact limsup_le_of_le (isCoboundedUnder_le_of_eventually_le atTop hnonneg)
    (remote_covariance_envelope H hs hgap hε)

end SphericalAging.AgingCenterEnvelope
