module

public import SphericalAging.CKSpecification
public import Mathlib.Topology.Separation.Hausdorff

public section

/-! Literal iterated limits of actual CK correlations in the two source
orders, from the preceding selected stationary window and fixed-wait decay. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.OrderedCorrelationAging
open CKSpecification

theorem source8_9 {p : ℕ} {β q : ℝ} {d : CKData} {c : ℝ→ℝ}
    (h : CKEquations p β d) (hq : 0<q)
    (hprofile : Tendsto c atTop (𝓝 q))
    (hwindow : ∀τ : ℝ,0≤τ→Tendsto (fun s => d.C (s+τ) s) atTop (𝓝 (c τ)))
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    Tendsto (fun τ : ℝ => limUnder atTop (fun s : ℝ => d.C (s+τ) s)) atTop (𝓝 q) ∧
    Tendsto (fun s : ℝ => limUnder atTop (fun τ : ℝ => d.C (s+τ) s)) atTop (𝓝 0) ∧
    q≠0 := by
  refine ⟨?_,?_,hq.ne'⟩
  · apply hprofile.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with τ hτ
    exact (hwindow τ hτ).limUnder_eq.symm
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    have hadd : Tendsto (fun τ : ℝ => s+τ) atTop atTop :=
      tendsto_atTop_add_const_left atTop s tendsto_id
    exact ((hforget s hs).comp hadd).limUnder_eq.symm

end SphericalAging.OrderedCorrelationAging
