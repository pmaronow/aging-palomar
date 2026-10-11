module

public import SphericalAging.SphereOnlyGeneratorLocalization

public section

/-! Intrinsic rotation derivatives depend only on the function on the
physical sphere. The skew operator flow stays on that sphere, so ordinary
one-variable derivative uniqueness suffices without ambient equality. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.SphereOnlyIntrinsicCongruence
open FiniteModel HardSphereDynamics SphericalIntegrationByParts SphereOnlyParameterIntegral
open SphereGeneratorIntegrationByParts
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem operatorFlow_mem_physicalSphere (A : Operator N) (hA : star A=-A)
    {x : Vector N} (hx : x∈physicalSphere N) (r : ℝ) :
    operatorFlow A r x∈physicalSphere N := by
  apply (onSphere_iff_norm_sq _).mpr
  rw [operatorFlow_norm A hA r x]
  exact (onSphere_iff_norm_sq _).mp hx

theorem flow_hasDerivAt_zero (A : Operator N) {f : Vector N→ℝ} {x : Vector N}
    (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun r : ℝ => f (operatorFlow A r x)) (lieDerivative A f x) 0 := by
  have hf' : DifferentiableAt ℝ f (operatorFlow A 0 x) := by simpa only [operatorFlow_zero] using hf
  simpa only [operatorFlow_zero,lieDerivative,Function.comp_def] using
    hf'.hasFDerivAt.comp_hasDerivAt 0 (operatorFlow_apply_hasDerivAt A 0 x)

theorem lieDerivative_eq_of_eq_onSphere (A : Operator N) (hA : star A=-A)
    {f g : Vector N→ℝ} (hEq : ∀y,y∈physicalSphere N→f y=g y)
    {x : Vector N} (hx : x∈physicalSphere N)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    lieDerivative A f x=lieDerivative A g x := by
  have hflow : (fun r : ℝ => f (operatorFlow A r x))=
      fun r => g (operatorFlow A r x) :=
    funext (fun r => hEq _ (operatorFlow_mem_physicalSphere A hA hx r))
  have hdf := flow_hasDerivAt_zero A hf
  have hdg := flow_hasDerivAt_zero A hg
  rw [hflow] at hdf
  exact hdf.unique hdg

theorem lieDerivative_congr_onSphere (A : Operator N) (hA : star A=-A)
    {f g : Vector N→ℝ} (hEq : ∀x,x∈physicalSphere N→f x=g x)
    (hf : ∀x,x∈physicalSphere N→DifferentiableAt ℝ f x)
    (hg : ∀x,x∈physicalSphere N→DifferentiableAt ℝ g x) :
    ∀x,x∈physicalSphere N→lieDerivative A f x=lieDerivative A g x :=
  fun x hx => lieDerivative_eq_of_eq_onSphere A hA hEq hx (hf x hx) (hg x hx)

theorem rotationGamma_eq_of_eq_onSphere {ι : Type*} [Fintype ι] (κ : ℝ) (A : ι→Operator N)
    (hA : ∀i,star (A i)=-A i) {f f' g g' : Vector N→ℝ}
    (hfEq : ∀y,y∈physicalSphere N→f y=f' y) (hgEq : ∀y,y∈physicalSphere N→g y=g' y)
    {x : Vector N} (hx : x∈physicalSphere N)
    (hf : DifferentiableAt ℝ f x) (hf' : DifferentiableAt ℝ f' x)
    (hg : DifferentiableAt ℝ g x) (hg' : DifferentiableAt ℝ g' x) :
    rotationGamma κ A f g x=rotationGamma κ A f' g' x := by
  classical
  unfold rotationGamma
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [lieDerivative_eq_of_eq_onSphere (A i) (hA i) hfEq hx hf hf',
    lieDerivative_eq_of_eq_onSphere (A i) (hA i) hgEq hx hg hg']

end SphericalAging.SphereOnlyIntrinsicCongruence
