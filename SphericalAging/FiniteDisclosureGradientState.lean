module

public import SphericalAging.FiniteDisclosureMeasurableState
public import SphericalAging.GradientDisclosureMeasurability

public section

/-! Every queried Hamiltonian gradient is determined by the constructed
past disclosed tensor. These APIs permit literal adaptive algorithms to
build their queries before the next Gaussian block is read. -/
noncomputable section
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureGradientState
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure HardSphereDynamics
open CanonicalVectorSpan CanonicalGramSelector PredictableGramStep
open TensorOrthogonalAction TensorResidualRotation FiniteDisclosureTree
open FiniteDisclosurePhysicalState FiniteDisclosureResidual FiniteDisclosureMeasurableState

theorem freshDisclosed_measurable {N p r : ℕ} {S : Type} [MeasurableSpace S]
    {x : S→Vector N} (hx : Measurable x) {D : S→TensorSpace N p} (hD : Measurable D) :
    Measurable (freshDisclosed (p:=p) (r:=r) x D) := by
  let U : S→Frame N := fun s => frameUpdate (space N r) (direction N r) (x s)
  have hU : Measurable (fun z : S×Vector N => U z.1 z.2) :=
    frameUpdate_measurable (space N r) measurable_const (hx.comp measurable_fst) measurable_snd
  have ha : Measurable (fun h : S×Block N p r => (h.1,D h.1)) :=
    measurable_fst.prodMk (hD.comp measurable_fst)
  have hComp : Measurable ((fun z : S×TensorSpace N p => action (U z.1) z.2)∘
      (fun h : S×Block N p r => (h.1,D h.1))) := (action_measurable (p:=p) U hU).comp ha
  have hAct : Measurable (fun h : S×Block N p r => action (U h.1) (D h.1)) := by
    simpa only [Function.comp_def] using hComp
  have hBlock : Measurable (fun h : S×Block N p r => h.2.val.val) :=
    (((Residual N p r).subtypeL.comp (Block N p r).subtypeL).measurable).comp measurable_snd
  have hAdd : Measurable (fun h : S×Block N p r => action (U h.1) (D h.1)+h.2.val.val) := hAct.add hBlock
  have hEq : freshDisclosed (p:=p) (r:=r) x D=
      (fun h : S×Block N p r => action (U h.1) (D h.1)+h.2.val.val) := rfl
  rw [hEq]
  exact hAdd

theorem physical_disclosed_tensor {N p : ℕ} (W : Submodule ℝ (Vector N))
    (F : Frame N) (D : TensorSpace N p) (hD : D∈(residualTensorSpace W)ᗮ)
    (R : residualTensorSpace (p:=p) W) :
    disclosedDisorder (rotatedSpace F W) (action F (D+R.val)).ofLp=(action F D).ofLp := by
  rw [disclosedDisorder,WithLp.toLp_ofLp,Submodule.starProjection_orthogonal_val,
    frame_projection W F D hD R,map_add,add_sub_cancel_right]

theorem actual_gradient_from_disclosed {N p : ℕ} (hp : 2≤p)
    (W : Submodule ℝ (Vector N)) (F : Frame N) (D : TensorSpace N p)
    (hD : D∈(residualTensorSpace W)ᗮ) (R : residualTensorSpace (p:=p) W)
    {y : Vector N} (hy : y∈rotatedSpace F W) :
    gradient (Hamiltonian N p (action F (D+R.val)).ofLp) y=
      gradient (Hamiltonian N p (action F D).ofLp) y := by
  rw [gradient_eq_disclosed hp (rotatedSpace F W) _ hy,physical_disclosed_tensor W F D hD R]

theorem disclosed_gradient_measurable {N p : ℕ} {S : Type} [MeasurableSpace S]
    (F : S→Frame N) (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    {D : S→TensorSpace N p} (hD : Measurable D) {y : S→Vector N} (hy : Measurable y) :
    Measurable (fun s => gradient (Hamiltonian N p (action (F s) (D s)).ofLp) (y s)) := by
  have harg : Measurable (fun s => (s,D s)) := measurable_id.prodMk hD
  have hComp : Measurable ((fun z : S×TensorSpace N p => action (F z.1) z.2)∘(fun s => (s,D s))) :=
    (action_measurable (p:=p) F hF).comp harg
  have hJ : Measurable (fun s => action (F s) (D s)) := by
    simpa only [Function.comp_def] using hComp
  have hdc : Measurable ((fun J : TensorSpace N p => J.ofLp)∘(fun s => action (F s) (D s))) :=
    (PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp hJ
  have hd : Measurable (fun s : S => (action (F s) (D s)).ofLp) := by
    simpa only [Function.comp_def] using hdc
  have harg2 : Measurable (fun s : S => ((action (F s) (D s)).ofLp,y s)) := hd.prodMk hy
  have hg : Measurable ((fun z : Disorder N p×Vector N => gradient (Hamiltonian N p z.1) z.2)∘
      (fun s : S => ((action (F s) (D s)).ofLp,y s))) :=
    (GradientDisclosureMeasurability.gradient_joint_continuous N p).measurable.comp harg2
  simpa only [Function.comp_def] using hg

end SphericalAging.FiniteDisclosureGradientState
