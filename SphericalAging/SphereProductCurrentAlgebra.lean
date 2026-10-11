module

public import SphericalAging.SphereFDTAlgebra

public section

/-! The exact two-semigroup density product current, obtained from
the genuine forward adjoint, generator product rule and weighted sphere
integration by parts. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereProductCurrentAlgebra
open MeasureTheory FiniteModel SphereInitialLaw SphericalIntegrationByParts
open SphereEntropyDissipation SphereGeneratorIntegrationByParts SphereGeneratorAlgebra
open SphereForwardAdjoint SphereFDTAlgebra

theorem product_current_identity {N p : ℕ} {ι : Type*} [Fintype ι]
    (hN : 0<N) (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ f g : Vector N→ℝ}
    (hρ : ContDiff ℝ 2 ρ) (hpos : ∀x,0<ρ x)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    (∫x : Vector N,forwardDensitySlope κ β J A ρ x*f x*g x-
      ρ x*rotationGenerator κ β J A f x*g x+
        ρ x*f x*rotationGenerator κ β J A g x ∂sphereLaw N)=
      -2*(∫x : Vector N,ρ x*f x*rotationGamma κ A (relativeLog β J ρ) g x ∂sphereLaw N) := by
  have hdot : Continuous (forwardDensitySlope κ β J A ρ) := by
    classical
    unfold forwardDensitySlope
    exact continuous_const.mul (continuous_finsetSum _ fun i _ =>
      lieDerivative_continuous (A i) (rotationFlux_contDiff β J (A i) hρ))
  have hLf := rotationGenerator_continuous κ β J A hf
  have hLg := rotationGenerator_continuous κ β J A hg
  have hLfg := rotationGenerator_continuous κ β J A (hf.mul hg)
  have hΓ := rotationGamma_continuous κ A (hf.of_le (by norm_num)) (hg.of_le (by norm_num))
  have hi₀ := continuous_sphere_integrable hN ((hdot.mul hf.continuous).mul hg.continuous)
  have hi₁ := continuous_sphere_integrable hN ((hρ.continuous.mul hLf).mul hg.continuous)
  have hi₂ := continuous_sphere_integrable hN ((hρ.continuous.mul hf.continuous).mul hLg)
  have hi₃ := continuous_sphere_integrable hN (hρ.continuous.mul hΓ)
  have hi₄ := continuous_sphere_integrable hN (hρ.continuous.mul hLfg)
  have hadj := forward_density_adjoint hN κ β J A hA hρ hpos (hf.mul hg)
  have he₀ : (∫x : Vector N,forwardDensitySlope κ β J A ρ x*f x*g x ∂sphereLaw N)=
      (∫x : Vector N,ρ x*rotationGenerator κ β J A (fun y => f y*g y) x ∂sphereLaw N) := by
    rw [←hadj]
    apply integral_congr_ae
    exact ae_of_all _ fun x => by ring
  have he₁ : (fun x : Vector N => ρ x*rotationGenerator κ β J A (fun y => f y*g y) x-
      ρ x*rotationGenerator κ β J A f x*g x+ρ x*f x*rotationGenerator κ β J A g x)=
      (fun x => 2*(ρ x*f x*rotationGenerator κ β J A g x)+2*(ρ x*rotationGamma κ A f g x)) := by
    funext x
    rw [rotationGenerator_mul κ β J A hf hg]
    ring
  rw [integral_add (f := fun x : Vector N => forwardDensitySlope κ β J A ρ x*f x*g x-
      ρ x*rotationGenerator κ β J A f x*g x)
    (g := fun x => ρ x*f x*rotationGenerator κ β J A g x) (hi₀.sub hi₁) hi₂,
    integral_sub (f := fun x : Vector N => forwardDensitySlope κ β J A ρ x*f x*g x)
      (g := fun x => ρ x*rotationGenerator κ β J A f x*g x) hi₀ hi₁,he₀,
    ←integral_sub (f := fun x : Vector N => ρ x*rotationGenerator κ β J A (fun y => f y*g y) x)
      (g := fun x => ρ x*rotationGenerator κ β J A f x*g x) hi₄ hi₁,
    ←integral_add (f := fun x : Vector N => ρ x*rotationGenerator κ β J A (fun y => f y*g y) x-
      ρ x*rotationGenerator κ β J A f x*g x)
      (g := fun x => ρ x*f x*rotationGenerator κ β J A g x) (hi₄.sub hi₁) hi₂,he₁,
    integral_add (f := fun x : Vector N => 2*(ρ x*f x*rotationGenerator κ β J A g x))
      (g := fun x => 2*(ρ x*rotationGamma κ A f g x)) (hi₂.const_mul 2) (hi₃.const_mul 2),
    integral_const_mul,integral_const_mul]
  have hibp := weighted_generator_current_ibp hN κ β J A hA (hρ.of_le (by norm_num)) hpos
    (hf.of_le (by norm_num)) hg
  rw [hibp]
  ring

end SphericalAging.SphereProductCurrentAlgebra
