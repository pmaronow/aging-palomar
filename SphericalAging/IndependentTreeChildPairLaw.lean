module

public import SphericalAging.BranchingNodeLaw

public section

/-! Two distinct literal child samples are independent under the actual
finite product tree law. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.IndependentTreeChildPairLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess
variable {G : Type} [MeasurableSpace G] {K : ℕ}

theorem childPair_measurePreserving (ν : Measure G) [IsProbabilityMeasure ν]
    (d : ℕ) (i j : Fin K) (hij : i≠j) :
    MeasurePreserving (fun z : TreeSample G K (d+1) => (z i,z j)) (treeLaw ν K (d+1))
      ((ν.prod (treeLaw ν K d)).prod (ν.prod (treeLaw ν K d))) := by
  letI := treeProbability ν K (d+1)
  have hm : Measurable (fun z : TreeSample G K (d+1) => (z i,z j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  refine ⟨hm,?_⟩
  have hi : iIndepFun (fun i (z : Fin K→G×TreeSample G K d) => z i)
      (treeLaw ν K (d+1)) :=
    iIndepFun_pi (fun _ : Fin K => measurable_id.aemeasurable)
  have hh := (hi.indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  change (Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d))).map (fun z => (z i,z j))=
    ((Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d))).map (Function.eval i)).prod
      ((Measure.pi (fun _ : Fin K => ν.prod (treeLaw ν K d))).map (Function.eval j)) at hh
  rw [(measurePreserving_eval (fun _ : Fin K => ν.prod (treeLaw ν K d)) i).map_eq,
    (measurePreserving_eval (fun _ : Fin K => ν.prod (treeLaw ν K d)) j).map_eq] at hh
  exact hh

end SphericalAging.IndependentTreeChildPairLaw
