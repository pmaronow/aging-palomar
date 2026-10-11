module

public import SphericalAging.CausalStripDistance

public section

/-! Full source Lemma 14.6 for the actual cubic selected-profile setting.
The long-time row convergence is proved by the preceding frozen response
localization theorem from the independent selected-profile inputs. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.DisjointCausalStripTheorem
open CKSpecification CKPhysicalConsequences GreenCovariance
open DisjointCausalStrips CausalStripIntegralBound CausalStripDistance
open BackwardRowL2 BackwardRowResidual ThermalRowConvergence StrongResponseRows

/-- Every numbered assertion of source Lemma geometry-disjoint-strips,
with genuine rank-one Hilbert--Schmidt operators and literal interval rows.
There is no operator geometry, L2 row limit, or distance conclusion among
the hypotheses. -/
theorem cubic_disjoint_causal_strips {β : ℝ} {d : CKData}
    (h : CKEquations 3 β d) {c r : ℝ→ℝ} {q : ℝ}
    (H : CubicResponseLocalization.Inputs h c r q) {D : ℝ} (hD : 0<D) :
    (∀u w : ℝ,D≤u → D≤w → D≤|u-w| → inner ℝ (strip h D u) (strip h D w)=0) ∧
    (∀T t : ℝ,D≤T → T≤t → ‖∫u in D..T,d.R t u • strip h D u‖^2≤
      8*D*(∫u in D..T,(d.R t u)^2)) ∧
    (∀t L : ℕ→ℝ,Tendsto t atTop atTop → Tendsto L atTop atTop →
      (∀n,D≤t n-L n) → Tendsto (fun n => ‖stateOperatorRow h (t n) (t n-L n)-
        prefixOperatorRow h D (t n) (t n-L n)‖) atTop (𝓝 0)) := by
  have hb := physical_bounds_of_equations h
  have hi2 := profile_square_integrable H.response_continuous H.response_integrable
    (profile_bounds_of_translation h H.translated_response)
  have hr : MemLp r 2 rayMeasure :=
    profile_memLp_two H.response_continuous (hi2.mono_set Ioi_subset_Ici_self)
  have hrow : Tendsto (rowError d r) atTop (𝓝 0) :=
    (cubic_positive_plateau_strong_rows H).2.2
  refine ⟨fun u w hu hw hsep => disjoint_strip_orthogonality h hb hD hu hw hsep,
    fun T t hDT hTt => causal_strip_interval_bound h hb hD hDT hTt,?_⟩
  intro t L ht hL hcausal
  exact old_operator_row_distance_tendsto_zero h hb hr hrow hD t L ht hL hcausal

end SphericalAging.DisjointCausalStripTheorem
