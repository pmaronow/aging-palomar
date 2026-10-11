module

public import SphericalAging.PrefixRectangleLimit
public import SphericalAging.PrefixEnergyLimit
public import SphericalAging.HankelReflection

public section

/-! Actual norm, energy and Hankel consequences of uniform prefix reflection.
The required coefficient limits are exactly translated cluster convergence. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 200000
open scoped InnerProductSpace NNReal Topology
open Set Filter
namespace SphericalAging.StationaryPrefixConsequences
open CKSpecification CKPhysicalConsequences PrefixReflection PrefixRectangleStability
  PrefixEnergyLimit HankelReflection

/-- The exact source energy limit follows directly from uniform translated cluster
coefficients and the reflected prefix Gram conclusion. -/
theorem prefix_energy_of_uniform_translation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} (hT : ∀ n, 0 ≤ T n)
    {c r : ℝ → ℝ} {ell L : ℝ} (hL : 0 ≤ L)
    (hC : TendstoUniformlyOn (fun n (z : ℝ×ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square L))
    (hR : TendstoUniformlyOn (fun n (z : ℝ×ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle L))
    (hQ : TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) atTop (square L))
    (hlambda : Tendsto (fun n => d.multiplier (T n+L)) atTop (nhds ell)) :
    Tendsto (fun n => CausalTreeRealization.treeEnergy p (prefixVector h (T n) (T n+L))) atTop
      (nhds ((ell-1)/((p : ℝ)*β) + β*(p : ℝ)*
        (∫ τ in (0 : ℝ)..L, r τ*(c (2*L-τ)^(p-1)-c τ^(p-1))))) := by
  apply prefix_energy_tendsto h (physical_bounds_of_equations h) hT hL
  · intro τ hτ
    have hm : (L,L-τ) ∈ triangle L := ⟨⟨hL,le_rfl⟩,⟨by linarith [hτ.2],by linarith [hτ.1]⟩⟩
    have hl := hR.tendsto_at hm
    simpa only [show L-(L-τ)=τ from by ring, show T _+(L-τ)=T _+L-τ from by ring] using hl
  · intro τ hτ
    have hm : (L,L-τ) ∈ square L := ⟨⟨hL,le_rfl⟩,⟨by linarith [hτ.2],by linarith [hτ.1]⟩⟩
    have hl := hC.tendsto_at hm
    simpa only [show L-(L-τ)=τ from by ring, abs_of_nonneg hτ.1,
      show T _+(L-τ)=T _+L-τ from by ring] using hl
  · intro τ hτ
    have hm : (L-τ,L) ∈ square L := ⟨⟨by linarith [hτ.2],by linarith [hτ.1]⟩,⟨hL,le_rfl⟩⟩
    have hl := hQ.tendsto_at hm
    simpa only [Function.uncurry_apply_pair, show (L-τ)+L=2*L-τ from by ring] using hl
  · exact hlambda

/-- A uniform reflected Gram limit gives the source's exact projected norm limit. -/
theorem prefix_norm_of_uniform_reflection {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hQ : TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) atTop (square L)) :
    Tendsto (fun n => ‖prefixVector h (T n) (T n+L)‖^2) atTop (nhds (c (2*L))) :=
  by
    have hl := hQ.tendsto_at (x := (L,L)) ⟨⟨hL,le_rfl⟩,⟨hL,le_rfl⟩⟩
    change Tendsto (fun n => futureKernel h (T n) L L) atTop (nhds (c (L+L))) at hl
    exact prefix_norm_sq_tendsto h hl

/-- The complete finite Gram positivity conclusion from locally uniform reflection,
with no positive Hankel assumption supplied. -/
theorem hankel_positive_of_uniform_reflection {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {T : ℕ → ℝ} {c : ℝ → ℝ}
    (hQ : ∀ A : ℝ, 0 ≤ A →
      TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
        (fun z => c (z.1+z.2)) atTop (square A)) : HankelPositive c := by
  apply hankel_positive_of_prefix_limit h (T := T) (c := c)
  intro a b
  have hm : ((a : ℝ),(b : ℝ)) ∈ square (max (a : ℝ) (b : ℝ)) :=
    ⟨⟨a.coe_nonneg,le_max_left _ _⟩,⟨b.coe_nonneg,le_max_right _ _⟩⟩
  have hl := (hQ (max (a : ℝ) (b : ℝ)) (a.coe_nonneg.trans (le_max_left _ _))).tendsto_at (x := ((a : ℝ),(b : ℝ))) hm
  change Tendsto (fun n => futureKernel h (T n) a b) atTop (nhds (c ((a : ℝ)+(b : ℝ)))) at hl
  exact hl

end SphericalAging.StationaryPrefixConsequences
