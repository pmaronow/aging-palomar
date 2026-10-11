module

public import SphericalAging.IndependentBranchingSuccess
public import SphericalAging.GaussianLinearMixtureLaw

public section

/-! The true state/subtree product law at every prescribed node of the
independently branching tree. In particular the current state is independent
of all the fresh child noises, although different nodes retain shared ancestry. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.BranchingNodeLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess
variable {S G : Type} [MeasurableSpace S] [MeasurableSpace G]

@[expose] def Address (K : ℕ) : ℕ→Type
  | 0 => Unit
  | l+1 => Fin K×Address K l

@[expose] def childSampler (update : ℕ→S→G→S) (d : ℕ) {K : ℕ} (i : Fin K)
    (z : S×TreeSample G K (d+1)) : S×TreeSample G K d :=
  (update d z.1 (z.2 i).1,(z.2 i).2)

theorem childSampler_measurePreserving (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    (d : ℕ) {K : ℕ} (i : Fin K) :
    MeasurePreserving (childSampler update d i)
      (μ.prod (treeLaw ν K (d+1))) (μ.prod (treeLaw ν K d)) := by
  letI := treeProbability ν K (d+1)
  have he : MeasurePreserving (Function.eval i) (treeLaw ν K (d+1))
      (ν.prod (treeLaw ν K d)) := measurePreserving_eval
        (fun _ : Fin K => ν.prod (treeLaw ν K d)) i
  have ha := MeasurePreserving.symm MeasurableEquiv.prodAssoc
    (measurePreserving_prodAssoc μ ν (treeLaw ν K d))
  exact ((hu d).prod (MeasurePreserving.id (treeLaw ν K d))).comp
    (ha.comp ((MeasurePreserving.id μ).prod he))

@[expose] def nodeSampler (update : ℕ→S→G→S) {K : ℕ} (m : ℕ) :
    (l : ℕ)→Address K l→S×TreeSample G K (m+l)→S×TreeSample G K m
  | 0,_,z => z
  | l+1,w,z => nodeSampler update m l w.2 (childSampler update (m+l) w.1 z)

theorem nodeSampler_measurePreserving (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    {K : ℕ} (m l : ℕ) (w : Address K l) :
    MeasurePreserving (nodeSampler update m l w)
      (μ.prod (treeLaw ν K (m+l))) (μ.prod (treeLaw ν K m)) := by
  induction l with
  | zero => exact MeasurePreserving.id _
  | succ l ih => exact (ih w.2).comp (childSampler_measurePreserving μ ν update hu (m+l) w.1)

@[expose] def childNoises {K : ℕ} (d : ℕ) (z : TreeSample G K (d+1)) : Fin K→G :=
  fun i => (z i).1

theorem childNoises_measurePreserving (ν : Measure G) [IsProbabilityMeasure ν]
    (K d : ℕ) :
    MeasurePreserving (childNoises (G:=G) (K:=K) d) (treeLaw ν K (d+1))
      (Measure.pi (fun _ : Fin K => ν)) := by
  have hm : Measurable (childNoises (G:=G) (K:=K) d) :=
    Measurable.of_eval (fun i => ((measurable_pi_apply i).fst))
  refine ⟨hm,?_⟩
  change (Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d))).map
    (fun z i => (z i).1)=_
  rw [Measure.pi_map_pi (fun _ => measurable_fst.aemeasurable)]
  simp only [Measure.map_fst_prod,measure_univ,one_smul]

@[expose] def nodeBlock (update : ℕ→S→G→S) {K : ℕ} (m l : ℕ) (w : Address K l)
    (z : S×TreeSample G K (m+1+l)) : S×(Fin K→G) :=
  let v := nodeSampler update (m+1) l w z
  (v.1,childNoises m v.2)

theorem nodeBlock_measurePreserving (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    {K : ℕ} (m l : ℕ) (w : Address K l) :
    MeasurePreserving (nodeBlock update m l w)
      (μ.prod (treeLaw ν K (m+1+l))) (μ.prod (Measure.pi (fun _ : Fin K => ν))) :=
  ((MeasurePreserving.id μ).prod (childNoises_measurePreserving ν K m)).comp
    (nodeSampler_measurePreserving μ ν update hu (m+1) l w)

@[expose] def optionBlock {K : ℕ} (z : G×(Fin K→G)) : Option (Fin K)→G
  | none => z.1
  | some i => z.2 i

theorem optionBlock_measurePreserving (ν : Measure G) [IsProbabilityMeasure ν]
    (K : ℕ) :
    MeasurePreserving (optionBlock (G:=G) (K:=K))
      (ν.prod (Measure.pi (fun _ : Fin K => ν)))
      (Measure.pi (fun _ : Option (Fin K) => ν)) := by
  have hh : MeasurePreserving (MeasurableEquiv.piOptionEquivProd
      (fun _ : Option (Fin K) => G)).symm
      ((Measure.pi (fun _ : Fin K => ν)).prod ν)
      (Measure.pi (fun _ : Option (Fin K) => ν)) :=
    ⟨(MeasurableEquiv.piOptionEquivProd _).symm.measurable,
      Measure.pi_map_piOptionEquivProd (fun _ : Option (Fin K) => ν)⟩
  convert hh.comp Measure.measurePreserving_swap using 1
  funext z i
  cases i <;> rfl

end SphericalAging.BranchingNodeLaw
