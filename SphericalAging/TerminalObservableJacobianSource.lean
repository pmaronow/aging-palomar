module

public import SphericalAging.RandomLpHessianInitialOperator
public import SphericalAging.BoundedLpCoefficientContinuity
public import SphericalAging.FlowTerminalMomentBounds
public import SphericalAging.VectorJacobianVariationError

public section

/-! Literal Jacobian and Hessian sources of a smooth bounded observable
along the genuine terminal flow; all random classes are constructed. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal ContDiff
namespace SphericalAging.TerminalObservableJacobianSource
open HardSphereDynamics LocalSDE FlowTerminalDerivative
set_option maxHeartbeats 2500000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
section Flow
variable (D : BrownianDriver N P F) {Kb Ks K M A : ℝ≥0}
  {b : Fin N→State N→ℝ} {s : Fin N→Fin N→State N→ℝ}
  (hbg : ∀i,ContDiff ℝ ∞ (b i)) (hsg : ∀i j,ContDiff ℝ ∞ (s i j))
  (hb : ∀i,LipschitzWith Kb (b i)) (hs : ∀i j,LipschitzWith Ks (s i j))
  (hnull : ∀B : Set Ω,MeasurableSet B→P B=0→MeasurableSet[F 0] B)
  (x : State N) (T t : ℝ≥0) (ht : t≤T) (g : State N→State N) (hg : ContDiff ℝ ∞ g)
  (hK : ∀z,‖fderiv ℝ g z‖≤K) (hM : LipschitzWith M (fderiv ℝ g))

@[expose] def jacobianAction (u : State N) : Lp (State N) 2 P :=
  BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK
    (stateClass D hb hs x T t) (stateResponse D hbg hsg hb hs x T t u)

@[expose] def hessianField : Ω→State N→L[ℝ] State N→L[ℝ] State N :=
  fun q => fderiv ℝ (fderiv ℝ g) (stateClass D hb hs x T t q)

include hg in
lemma hessianField_measurable : AEStronglyMeasurable (hessianField D hb hs x T t g) P :=
  ((hg.fderiv_right (m:=∞) (by simp)).continuous_fderiv (by simp)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable _)
include hM in
lemma hessianField_bound : ∀ᵐq∂P,‖hessianField D hb hs x T t g q‖≤M :=
  .of_forall (fun _ => norm_fderiv_le_of_lipschitz ℝ hM)

@[expose] def hessianSource (u v : State N) : Lp (State N) 2 P :=
  RandomLpHessianSource.source (hessianField D hb hs x T t g)
    (hessianField_measurable D hb hs x T t g hg) M (hessianField_bound D hb hs x T t g hM)
    (stateResponse D hbg hsg hb hs x T t u) (stateResponse D hbg hsg hb hs x T t v)
    (FlowTerminalMomentBounds.response_terminal_fourthMoment D hbg hsg hb hs hnull x u T t ht).1
    (FlowTerminalMomentBounds.response_terminal_fourthMoment D hbg hsg hb hs hnull x v T t ht).1

lemma hessianSource_coe (u v : State N) :
    hessianSource D hbg hsg hb hs hnull x T t ht g hg hM u v=ᵐ[P]
      (fun q => fderiv ℝ (fderiv ℝ g) (stateClass D hb hs x T t q)
        (stateResponse D hbg hsg hb hs x T t u q) (stateResponse D hbg hsg hb hs x T t v q)) :=
  RandomLpHessianSource.source_coe _ _ _ _ _ _ _ _

@[expose] def hessianOperator (v : State N) : State N→L[ℝ] Lp (State N) 2 P :=
  RandomLpHessianInitialOperator.initialOperator (hessianField D hb hs x T t g)
    (hessianField_measurable D hb hs x T t g hg) M (hessianField_bound D hb hs x T t g hM)
    (stateResponse D hbg hsg hb hs x T t)
    (fun u => (FlowTerminalMomentBounds.response_terminal_fourthMoment D hbg hsg hb hs hnull x u T t ht).1)
    (stateResponse D hbg hsg hb hs x T t v)
    (FlowTerminalMomentBounds.response_terminal_fourthMoment D hbg hsg hb hs hnull x v T t ht).1

@[simp] lemma hessianOperator_apply (u v : State N) :
    hessianOperator D hbg hsg hb hs hnull x T t ht g hg hM v u=
      hessianSource D hbg hsg hb hs hnull x T t ht g hg hM u v := rfl

@[expose] def sourceError (y v : State N) : Lp (State N) 2 P :=
  jacobianAction D hbg hsg hb hs y T t g hK hM v-
    BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK
      (stateClass D hb hs x T t) (stateResponse D hbg hsg hb hs y T t v)-
    hessianSource D hbg hsg hb hs hnull x T t ht g hg hM (y-x) v

 theorem sourceError_pointwise_bound
    (hA : LipschitzWith A (fderiv ℝ (fderiv ℝ g))) (y v : State N) : ∀ᵐq∂P,
    ‖sourceError D hbg hsg hb hs hnull x T t ht g hg hK hM y v q‖≤
      (A:ℝ)*‖(stateClass D hb hs y T t-stateClass D hb hs x T t : Lp (State N) 2 P) q‖^2*
        ‖stateResponse D hbg hsg hb hs y T t v q‖+
      (M:ℝ)*‖(stateClass D hb hs y T t-stateClass D hb hs x T t-
        stateResponse D hbg hsg hb hs x T t (y-x) : Lp (State N) 2 P) q‖*
        ‖stateResponse D hbg hsg hb hs y T t v q‖+
      (M:ℝ)*‖stateResponse D hbg hsg hb hs x T t (y-x) q‖*
        ‖(stateResponse D hbg hsg hb hs y T t v-stateResponse D hbg hsg hb hs x T t v : Lp (State N) 2 P) q‖ := by
  let U := stateClass D hb hs x T t
  let V := stateClass D hb hs y T t
  let X := stateResponse D hbg hsg hb hs x T t v
  let Y := stateResponse D hbg hsg hb hs y T t v
  let Z := stateResponse D hbg hsg hb hs x T t (y-x)
  let B := BoundedLpCoefficientContinuity.action (fderiv ℝ g) hM.continuous K hK U Y
  let C := hessianSource D hbg hsg hb hs hnull x T t ht g hg hM (y-x) v
  let E := jacobianAction D hbg hsg hb hs y T t g hK hM v
  filter_upwards [Lp.coeFn_sub (E-B) C,Lp.coeFn_sub E B,
    BoundedLpCoefficientContinuity.action_coeFn (fderiv ℝ g) hM.continuous K hK V Y,
    BoundedLpCoefficientContinuity.action_coeFn (fderiv ℝ g) hM.continuous K hK U Y,
    hessianSource_coe D hbg hsg hb hs hnull x T t ht g hg hM (y-x) v,
    Lp.coeFn_sub V U,Lp.coeFn_sub (V-U) Z,Lp.coeFn_sub Y X] with q hr he hy hb hc hi hf hd
  change E q=fderiv ℝ g (V q) (Y q) at hy
  change B q=fderiv ℝ g (U q) (Y q) at hb
  change C q=fderiv ℝ (fderiv ℝ g) (U q) (Z q) (X q) at hc
  change ‖(E-B-C) q‖≤(A:ℝ)*‖(V-U : Lp (State N) 2 P) q‖^2*‖Y q‖+
    (M:ℝ)*‖(V-U-Z : Lp (State N) 2 P) q‖*‖Y q‖+
    (M:ℝ)*‖Z q‖*‖(Y-X : Lp (State N) 2 P) q‖
  rw [hr,Pi.sub_apply,he,Pi.sub_apply,hy,hb,hc,hi,Pi.sub_apply,hf,Pi.sub_apply,hi,Pi.sub_apply,hd,Pi.sub_apply]
  exact VectorJacobianVariationError.source_error_bound hg hM hA _ _ _ _ _
end Flow
end SphericalAging.TerminalObservableJacobianSource
