module

public import SphericalAging.FrameInverseMeasurable
public import SphericalAging.FiniteDisclosureGradientState
public import SphericalAging.SphereEulerQueryData

public section

/-! Constructed measurable Euler memory on every actual random-rank
disclosure branch. The canonical disclosed tensor remains in the correct
orthogonal subspace after each actual fresh block is read. -/
noncomputable section
open Set MeasureTheory
namespace SphericalAging.GenericEulerDisclosureMemory
open FiniteModel HardSphereDynamics AdaptiveGradientDisclosure TensorOrthogonalAction
open FiniteDisclosureTree FiniteDisclosurePhysicalState FiniteDisclosureGradientState
open FiniteDisclosureMeasurableState SphereEulerQueryData FrameInverseMeasurable
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

structure Memory (N p r : ℕ) (S : Type) [MeasurableSpace S] where
  frame : S→Frame N
  frame_measurable : Measurable (fun q : S×Vector N => frame q.1 q.2)
  disclosed : S→TensorSpace N p
  disclosed_measurable : Measurable disclosed
  disclosed_mem : ∀s,disclosed s∈(Residual N p r)ᗮ
  state : S→State N
  state_measurable : Measurable state
  increments : ℕ→S→State N
  increments_measurable : ∀j,Measurable (increments j)

variable {N p r : ℕ} {S : Type} [MeasurableSpace S]

@[expose] def observedGradient (m : Memory N p r S) (s : S) : State N :=
  hamiltonianGradient (action (m.frame s) (m.disclosed s)).ofLp (SphereEulerCoefficients.clip (m.state s))

theorem observedGradient_measurable (m : Memory N p r S) : Measurable (observedGradient m) :=
  disclosed_gradient_measurable m.frame m.frame_measurable m.disclosed_measurable
    (SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp m.state_measurable)

@[expose] def gradientQuery (m : Memory N p r S) (s : S) : Vector N := (m.frame s).symm (observedGradient m s)

theorem gradientQuery_measurable (m : Memory N p r S) : Measurable (gradientQuery m) :=
  (inverse_joint_measurable m.frame m.frame_measurable).comp
    (measurable_id.prodMk (observedGradient_measurable m))

@[expose] def nextState (m : Memory N p r S) (β h : ℝ) (k : ℕ) (s : S) : State N :=
  stepFromGradient β h (m.state s) (m.increments k s) (observedGradient m s)

theorem nextState_measurable (m : Memory N p r S) (β h : ℝ) (k : ℕ) : Measurable (nextState m β h k) := by
  have hh := stateFromData_measurable β h m.state (fun _ => m.increments k)
    (fun _ => observedGradient m) 1 m.state_measurable
    (fun _ _ => m.increments_measurable k) (fun _ _ => observedGradient_measurable m)
  exact hh

@[expose] def dependent (m : Memory N p r S) (y : S→State N) (hy : Measurable y) : Memory N p r S :=
  {m with state:=y,state_measurable:=hy}

@[expose] def fresh (m : Memory N p r S) (q : S→Vector N) (hq : Measurable q)
    (y : S→State N) (hy : Measurable y) : Memory N p (r+1) (S×Block N p r) where
  frame := freshFrame q m.frame
  frame_measurable := freshFrame_joint_measurable (p:=p) (r:=r) hq m.frame m.frame_measurable
  disclosed := freshDisclosed q m.disclosed
  disclosed_measurable := freshDisclosed_measurable hq m.disclosed_measurable
  disclosed_mem := freshDisclosed_mem q m.disclosed m.disclosed_mem
  state := y∘Prod.fst
  state_measurable := hy.comp measurable_fst
  increments := fun j => m.increments j∘Prod.fst
  increments_measurable := fun j => (m.increments_measurable j).comp measurable_fst

end SphericalAging.GenericEulerDisclosureMemory
