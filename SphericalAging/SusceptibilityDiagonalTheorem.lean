module

public import SphericalAging.SusceptibilityRecentCenters

public section

/-! Source 14.7 Step 1: a true integer-age diagonal with all actual center,
recent-mass and recent-vector assertions, from preceding selected inputs. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.SusceptibilityDiagonalTheorem
open CKSpecification CausalTree PrefixReflection CenterNormalization CubicResponseLocalization
open SusceptibilityDiagonal SusceptibilityRecentCenters

theorem source14_7_step1 {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ (N : ℕ) (i : ℕ → ℕ),
      Receipt h c q (fun n => t (n+N)) (fun n => (i n:ℝ)+1) ∧
      ∀ W : ℝ,0<W → ∀ ε : ℝ,0<ε → ∀ᶠ n : ℕ in atTop,
        ∀ τ : ℝ,τ∈Icc 0 W →
          ‖prefixVector h (t (n+N)-((i n:ℝ)+1)) (t (n+N)-τ)-
            Real.sqrt q • normalizedCenter h (t (n+N)) ((i n:ℝ)+1)‖≤ε := by
  obtain ⟨N,i,A⟩ := exists_integer_receipt H t ht
  exact ⟨N,i,A,fun W hW ε hε => recent_centers_uniform H A hW hε⟩

end SphericalAging.SusceptibilityDiagonalTheorem
