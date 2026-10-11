module

public import SphericalAging.SphereOnlyIntrinsicCongruence

public section

/-! Differentiating the actual sphere-only forward equation in intrinsic
rotation directions. The spatial positive representative supplies local
regularity, while equality of slopes is required only on the sphere. -/
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace SphericalAging.SphereOnlyLogSlopeCongruence
open FiniteModel HardSphereDynamics SphereOnlyParameterIntegral SphericalIntegrationByParts
open SphereEntropyDissipation SphereGeneratorIntegrationByParts SphereFisherDissipation
open SmoothPositiveSpatialReplacement SphereOnlySpatialLocalization SphereOnlyGeneratorLocalization
open SphereOnlyIntrinsicCongruence
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {ι : Type*} [Fintype ι]

@[expose] def logBalanceSlope (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (ρ : Vector N→ℝ) (x : Vector N) : ℝ :=
  rotationGenerator κ β J A (relativeLog β J ρ) x+
    rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) x

theorem logBalanceSlope_eventuallyEq (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {g ρ : Vector N→ℝ} {x : Vector N} (h : g=ᶠ[𝓝 x]ρ) :
    logBalanceSlope κ β J A g=ᶠ[𝓝 x]logBalanceSlope κ β J A ρ := by
  have hψ := relativeLog_eventuallyEq β J h
  exact (rotationGenerator_eventuallyEq κ β J A hψ).add (rotationGamma_eventuallyEq κ A hψ hψ)

theorem logBalanceSlope_differentiableAt_onSphere (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {ρ : Vector N→ℝ} (hρ : ContDiff ℝ 3 ρ)
    (hpos : ∀y,y∈physicalSphere N→0<ρ y) {x : Vector N} (hx : x∈physicalSphere N) :
    DifferentiableAt ℝ (logBalanceSlope κ β J A ρ) x := by
  obtain ⟨g,hg,hgpos,hnear⟩ := exists_positive_near_sphere hρ hpos
  have hψ : ContDiff ℝ 3 (relativeLog β J g) := by
    unfold relativeLog
    exact ((hg.log (fun y => (hgpos y).ne')).sub
      (contDiff_const.mul ((Hamiltonian_contDiff J).of_le (by simp)))).add contDiff_const
  have hL := rotationGenerator_contDiff_one κ β J A hψ
  have hG : ContDiff ℝ 2 (rotationGamma κ A (relativeLog β J g) (relativeLog β J g)) :=
    rotationGamma_contDiff_order κ A hψ hψ
  have hd : DifferentiableAt ℝ (logBalanceSlope κ β J A g) x :=
    ((hL.add (hG.of_le (by norm_num))).differentiable (by norm_num)) x
  exact hd.congr_of_eventuallyEq (logBalanceSlope_eventuallyEq κ β J A (hnear x hx)).symm

theorem dot_div_density_eq_onSphere (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    {ρ ρdot : Vector N→ℝ} (hρ : ContDiff ℝ 2 ρ)
    (hpos : ∀y,y∈physicalSphere N→0<ρ y)
    (hPDE : ∀y,y∈physicalSphere N→ρdot y=forwardDensitySlope κ β J A ρ y) :
    ∀y,y∈physicalSphere N→ρdot y/ρ y=logBalanceSlope κ β J A ρ y := by
  intro y hy
  rw [hPDE y hy,forward_density_log_balance_onSphere κ β J A hρ hpos hy]
  dsimp only [logBalanceSlope]
  field_simp [(hpos y hy).ne']

theorem logSlope_lieDerivative_eq_onSphere (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ ρdot : Vector N→ℝ}
    (hρ : ContDiff ℝ 3 ρ) (hdot : ContDiff ℝ 1 ρdot)
    (hpos : ∀y,y∈physicalSphere N→0<ρ y)
    (hPDE : ∀y,y∈physicalSphere N→ρdot y=forwardDensitySlope κ β J A ρ y)
    {x : Vector N} (hx : x∈physicalSphere N) (i : ι) :
    lieDerivative (A i) (fun y => ρdot y/ρ y) x=
      lieDerivative (A i) (logBalanceSlope κ β J A ρ) x := by
  have hinv := (hasDerivAt_inv (hpos x hx).ne').hasFDerivAt.comp x
    (hρ.differentiable (by norm_num) x).hasFDerivAt
  have hf : DifferentiableAt ℝ (fun y => ρdot y/ρ y) x := by
    simpa only [Function.comp_def,div_eq_mul_inv] using
      ((hdot.differentiable (by norm_num) x).hasFDerivAt.fun_mul hinv).differentiableAt
  have hg := logBalanceSlope_differentiableAt_onSphere κ β J A hρ hpos hx
  exact lieDerivative_eq_of_eq_onSphere (A i) (hA i)
    (dot_div_density_eq_onSphere κ β J A (hρ.of_le (by norm_num)) hpos hPDE) hx hf hg

theorem rotationGamma_logSlope_eq_onSphere (κ β : ℝ) (J : Disorder N p) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {ρ ρdot : Vector N→ℝ}
    (hρ : ContDiff ℝ 3 ρ) (hdot : ContDiff ℝ 1 ρdot)
    (hpos : ∀y,y∈physicalSphere N→0<ρ y)
    (hPDE : ∀y,y∈physicalSphere N→ρdot y=forwardDensitySlope κ β J A ρ y)
    {x : Vector N} (hx : x∈physicalSphere N) :
    rotationGamma κ A (relativeLog β J ρ) (fun y => ρdot y/ρ y) x=
      rotationGamma κ A (relativeLog β J ρ)
        (fun y => rotationGenerator κ β J A (relativeLog β J ρ) y+
          rotationGamma κ A (relativeLog β J ρ) (relativeLog β J ρ) y) x := by
  classical
  unfold rotationGamma
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [logSlope_lieDerivative_eq_onSphere κ β J A hA hρ hdot hpos hPDE hx i]
  rfl

end SphericalAging.SphereOnlyLogSlopeCongruence
