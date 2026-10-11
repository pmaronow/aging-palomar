module

public import SphericalAging.SphereGibbsGenerator

public section

/-! The genuine ground-state transform of the spherical forward operator:
L*(πu)=πLu for the constructed normalized Gibbs density. -/
noncomputable section
set_option maxHeartbeats 1800000
namespace SphericalAging.SphereGibbsForwardTransform
open FiniteModel SphereGibbsEntropy SphereGibbsGenerator SphericalIntegrationByParts
open SphereEntropyDissipation SphereGeneratorIntegrationByParts
open scoped BigOperators
variable {N p : ℕ}

theorem gibbs_lieDerivative (hN : 0<N) (hp : 1≤p) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) (A : Operator N) (x : Vector N) :
    lieDerivative A (gibbsDensity N p β J) x=
      β*gibbsDensity N p β J x*lieDerivative A (Hamiltonian N p J) x := by
  have hh := congrFun (gibbs_rotationFlux_zero hN hp hβ J A) x
  dsimp only [rotationFlux] at hh
  linarith

theorem gibbs_product_rotationFlux (hN : 0<N) (hp : 1≤p) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) (A : Operator N) {u : Vector N→ℝ} (hu : ContDiff ℝ 1 u) :
    rotationFlux β J A (fun x => gibbsDensity N p β J x*u x)=
      fun x => gibbsDensity N p β J x*lieDerivative A u x := by
  funext x
  unfold rotationFlux
  rw [lieDerivative_mul A ((gibbsDensity_contDiff β J).of_le (by simp)) hu,
    gibbs_lieDerivative hN hp hβ J A x]
  ring

theorem gibbs_product_forwardDensitySlope {ι : Type*} [Fintype ι]
    (hN : 0<N) (hp : 1≤p) (κ : ℝ) {β : ℝ} (hβ : 0≤β)
    (J : Disorder N p) (A : ι→Operator N) {u : Vector N→ℝ} (hu : ContDiff ℝ 2 u) :
    forwardDensitySlope κ β J A (fun x => gibbsDensity N p β J x*u x)=
      fun x => gibbsDensity N p β J x*rotationGenerator κ β J A u x := by
  classical
  funext x
  have hi i : lieDerivative (A i) (rotationFlux β J (A i) (fun y => gibbsDensity N p β J y*u y)) x=
      gibbsDensity N p β J x*(lieDerivative (A i) (lieDerivative (A i) u) x+
        β*lieDerivative (A i) (Hamiltonian N p J) x*lieDerivative (A i) u x) := by
    rw [gibbs_product_rotationFlux hN hp hβ J (A i) (hu.of_le (by norm_num)),
      lieDerivative_mul (A i) ((gibbsDensity_contDiff β J).of_le (by simp))
        (lieDerivative_contDiff (A i) hu),gibbs_lieDerivative hN hp hβ J (A i) x]
    ring
  unfold forwardDensitySlope rotationGenerator
  simp_rw [hi]
  rw [←Finset.mul_sum]
  ring

end SphericalAging.SphereGibbsForwardTransform
