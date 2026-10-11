module

public import SphericalAging.StationaryResponseLimit
public import SphericalAging.StationaryReflection
public import SphericalAging.PrefixEnergyLimit

public section

/-! Stationary reflection with the response ODE proved from the translated CK
limit. FDT remains an explicit, independent hypothesis. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.StationaryReflectionFromTranslation
open CKSpecification StationaryResponseLimit ScalarConstraints PrefixRectangleStability
open StationaryReflection PrefixReflection PrefixEnergyLimit

/-- The scalar stationary input now needs only translated convergence and FDT,
with its response equation and physical/initial conditions proved from CK. -/
theorem stationaryInputs_of_uniform_translation_and_fdt {p : ℕ} {β ell : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (h : CKEquations p β d) (hT : Tendsto T atTop atTop)
    (hC : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hLam : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n a => d.multiplier (T n+a)) (fun _ => ell) atTop (Icc 0 A))
    (hFDT : ∀ t,0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t) :
    StationaryInputs (p-2) (β^2*(p : ℝ)) ell c r :=
  (stationary_response_of_uniform_translation h hT hC hR hLam).stationaryInputs h.spin_ge_three hFDT

/-- Actual uniform prefix reflection, without a limiting-response ODE premise. -/
theorem prefix_reflection_of_uniform_translation_and_fdt {p : ℕ} {β ell : ℝ} {d : CKData}
    {T : ℕ → ℝ} {c r : ℝ → ℝ} (h : CKEquations p β d) (hT : Tendsto T atTop atTop)
    (hC : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.C (T n+z.1) (T n+z.2))
      (fun z => c |z.1-z.2|) atTop (square A))
    (hR : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n (z : ℝ × ℝ) => d.R (T n+z.1) (T n+z.2))
      (fun z => r (z.1-z.2)) atTop (triangle A))
    (hLam : ∀ A,0 ≤ A → TendstoUniformlyOn
      (fun n a => d.multiplier (T n+a)) (fun _ => ell) atTop (Icc 0 A))
    (hFDT : ∀ t,0 ≤ t → HasDerivWithinAt c (-r t) (Ici 0) t) :
    ∀ A,0 ≤ A → TendstoUniformlyOn (fun n => Function.uncurry (futureKernel h (T n)))
      (fun z => c (z.1+z.2)) atTop (square A) := by
  have hS := stationaryInputs_of_uniform_translation_and_fdt h hT hC hR hLam hFDT
  intro A hA
  exact prefix_reflection_uniform_late h hS hA hT (hC A hA) (hR A hA)

/-- The full energy's constant locally uniform cluster limit follows directly
from the genuine multiplier identity and its translated convergence. -/
theorem energy_uniform_of_multiplier_uniform {p : ℕ} {β ell A : ℝ} {d : CKData}
    {T : ℕ → ℝ} (h : CKEquations p β d) (hT : Tendsto T atTop atTop)
    (hLam : TendstoUniformlyOn (fun n a => d.multiplier (T n+a))
      (fun _ => ell) atTop (Icc 0 A)) :
    TendstoUniformlyOn (fun n a => energy p β d (T n+a))
      (fun _ => (ell-1)/((p : ℝ)*β)) atTop (Icc 0 A) := by
  have hc : UniformContinuous (fun x : ℝ => (x-1)/((p : ℝ)*β)) :=
    (uniformContinuous_id.sub uniformContinuous_const).div_const' _
  have hh := hc.comp_tendstoUniformlyOn hLam
  apply hh.congr
  filter_upwards [hT.eventually (eventually_ge_atTop 0)] with n hn a ha
  exact (energy_eq_multiplier_quotient h (add_nonneg hn ha.1)).symm

end SphericalAging.StationaryReflectionFromTranslation
