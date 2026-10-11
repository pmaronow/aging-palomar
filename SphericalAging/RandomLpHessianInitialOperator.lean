module

public import SphericalAging.RandomLpHessianSource
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

public section

/-! Actual bounded random Hessian action on a genuine initial-direction
linear response gives a true continuous linear L² operator. -/
noncomputable section
open MeasureTheory Filter
open scoped NNReal ENNReal
namespace SphericalAging.RandomLpHessianInitialOperator
open HardSphereDynamics RandomLpHessianSource
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
local instance : NormedAddCommGroup (State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N) := inferInstance
local instance : NormedAddCommGroup (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
local instance : NormedSpace ℝ (State N→L[ℝ] State N→L[ℝ] State N) := inferInstance
section Definition
variable (H : Ω→State N→L[ℝ] State N→L[ℝ] State N)
  (hH : AEStronglyMeasurable H P) (M : ℝ≥0) (hM : ∀ᵐ q ∂P,‖H q‖≤M)
  (Y : State N→L[ℝ] Lp (State N) 2 P) (hY : ∀v,MemLp (Y v : Ω→State N) 4 P)
  (V : Lp (State N) 2 P) (hV : MemLp (V : Ω→State N) 4 P)

theorem source_add (a b : State N) : source H hH M hM (Y (a+b)) V (hY _) hV=
    source H hH M hM (Y a) V (hY _) hV+source H hH M hM (Y b) V (hY _) hV := by
  apply Lp.ext
  filter_upwards [source_coe H hH M hM (Y (a+b)) V (hY _) hV,
    source_coe H hH M hM (Y a) V (hY _) hV,source_coe H hH M hM (Y b) V (hY _) hV,
    Lp.coeFn_add (Y a) (Y b),Lp.coeFn_add (source H hH M hM (Y a) V (hY _) hV)
      (source H hH M hM (Y b) V (hY _) hV)] with q hc ha hb hy hs
  rw [hc,hs,Pi.add_apply,ha,hb,Y.map_add,hy,Pi.add_apply,map_add,ContinuousLinearMap.add_apply]

theorem source_smul (c : ℝ) (a : State N) : source H hH M hM (Y (c • a)) V (hY _) hV=
    c • source H hH M hM (Y a) V (hY _) hV := by
  apply Lp.ext
  filter_upwards [source_coe H hH M hM (Y (c • a)) V (hY _) hV,
    source_coe H hH M hM (Y a) V (hY _) hV,Lp.coeFn_smul c (Y a),
    Lp.coeFn_smul c (source H hH M hM (Y a) V (hY _) hV)] with q hc ha hy hs
  rw [hc,hs,Pi.smul_apply,ha,Y.map_smul,hy,Pi.smul_apply,map_smul,ContinuousLinearMap.smul_apply]

@[expose] def initialLinearMap : State N→ₗ[ℝ] Lp (State N) 2 P where
  toFun := fun a => source H hH M hM (Y a) V (hY _) hV
  map_add' := source_add H hH M hM Y hY V hV
  map_smul' := source_smul H hH M hM Y hY V hV

@[expose] def initialOperator : State N→L[ℝ] Lp (State N) 2 P :=
  (initialLinearMap H hH M hM Y hY V hV).toContinuousLinearMap

@[simp] theorem initialOperator_apply (a : State N) :
    initialOperator H hH M hM Y hY V hV a=source H hH M hM (Y a) V (hY _) hV := rfl
end Definition
end SphericalAging.RandomLpHessianInitialOperator
