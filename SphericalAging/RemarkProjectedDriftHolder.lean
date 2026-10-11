module

public import SphericalAging.ProjectedDriftHolder

public section

/-! Remark 7.4: the actual CK diagonal increment discharges the conditional
projected-derivative Hölder hypothesis, with the displayed cutoff-independent constant. -/
noncomputable section
open Set
namespace SphericalAging.RemarkProjectedDriftHolder
open CKSpecification CKPhysicalConsequences CausalTree CausalTreeRealization
open ProjectedTreeDrift UniformMultiplier

theorem source7_4 {p : ℕ} {β : ℝ} {d : CKData} (h : CKEquations p β d) :
    (∀t s : ℝ,0≤t→0≤s→1-d.C t s≤multiplierCeiling p β*|t-s|) ∧
    ∀T t s : ℝ,0≤T→T<t→T<s→
      ‖deriv (fun x => timePrefix T (ckTreeState h x)) t-
        deriv (fun x => timePrefix T (ckTreeState h x)) s‖≤
        ((1+2*β*(p:ℝ)^2*Real.sqrt p)*Real.sqrt (2*multiplierCeiling p β))*Real.sqrt |t-s| := by
  refine ⟨fun t s ht hs => ColoredEnergyRegularity.one_minus_correlation_bound h ht hs,?_⟩
  intro T t s hT ht hs
  exact projected_derivative_holder h (physical_bounds_of_equations h)
    (fun t s ht hs => ColoredEnergyRegularity.one_minus_correlation_bound h ht hs) hT ht hs
end SphericalAging.RemarkProjectedDriftHolder
