module

public import SphericalAging.StationaryReflection
public import SphericalAging.StationaryPrefixConsequences

public section

/-! The complete source prefix-reflection conclusion, with the actual causal tree
centers, exact projected norm and energy limits, and Hankel positivity. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped InnerProductSpace NNReal Topology
open Set Filter
namespace SphericalAging.StationaryReflectionReceipt
open CKSpecification ScalarConstraints PrefixReflection PrefixRectangleStability
  StationaryReflection StationaryPrefixConsequences HankelReflection CausalTreeRealization

/-- Source `sel:prefix-reflection`: all displayed conclusions on the actual prefix
centers of a translated stationary CK cluster. The final Hankel positivity is
source `sel:cluster-complete-monotonicity`, Step 1. The stationary inputs are the
scalar equations and physical/FDT conclusions preceding the source proposition;
neither reflection nor any limiting prefix equation is an input. -/
theorem stationary_prefix_reflection {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} (hT : ∀ n, 0 ≤ T n)
    {c r : ℝ → ℝ} {ell : ℝ}
    (hS : StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r)
    (hC : ∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun n (z : ℝ×ℝ) => d.C (T n+z.1) (T n+z.2))
        (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun n (z : ℝ×ℝ) => d.R (T n+z.1) (T n+z.2))
        (fun z => r (z.1-z.2)) atTop (triangle A))
    (hlambda : ∀ L : ℝ, 0 ≤ L → Tendsto (fun n => d.multiplier (T n+L)) atTop (nhds ell)) :
    (∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (fun z => c (z.1+z.2)) atTop (square A)) ∧
    (∀ L : ℝ, 0 ≤ L →
      Tendsto (fun n => ‖prefixVector h (T n) (T n+L)‖^2) atTop (nhds (c (2*L))) ∧
      Tendsto (fun n => treeEnergy p (prefixVector h (T n) (T n+L))) atTop
        (nhds ((ell-1)/((p : ℝ)*β)+β*(p : ℝ)*
          (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1)))))) ∧
    HankelPositive c := by
  have hQ (A : ℝ) (hA : 0 ≤ A) :
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (fun z => c (z.1+z.2)) atTop (square A) :=
    prefix_reflection_uniform h hS hA hT (hC A hA) (hR A hA)
  refine ⟨hQ,?_,hankel_positive_of_uniform_reflection h hQ⟩
  intro L hL
  exact ⟨prefix_norm_of_uniform_reflection h hL (hQ L hL),
    prefix_energy_of_uniform_translation h hT hL (hC L hL) (hR L hL) (hQ L hL) (hlambda L hL)⟩

end SphericalAging.StationaryReflectionReceipt
