module

public import SphericalAging.ActualForkCenterEnergyLimit

public section

/-! The energy and signed primitive interfaces used by the finite fork
follow from the exact preceding actual-model source3.3 clauses and the
checked source4.1. This does not assume a fork limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.CanonicalForkPrecedingBridges
open Set Filter MeasureTheory FiniteModel CKSpecification
open ActualEnergyDimensionLimit ActualEnergyUniformBridge ActualResponseWindowLimit
open ActualForkCenterEnergyLimit WeightedPrimitiveConvergence
open scoped NNReal ENNReal Topology
variable {p : ℕ}

theorem energy_bridge_from_preceding (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d)
    (hOverlap : ActualOverlapL1Convergence p β d)
    (hTrace : ActualTracePrimitiveConvergence (by have hh:=h.spin_ge_three;omega : 2≤p) β d)
    (dim : ℕ→ℕ) (hDim : ∀j,1≤dim j) (hTop : Tendsto dim atTop atTop) :
    CanonicalEnergyBridge (p:=p) β dim d := by
  have he := (proposition_4_1_from_preceding_bridges β d h hOverlap hTrace).1
  have hidx : Tendsto (fun j => dim j-1) atTop atTop := (tendsto_sub_atTop_nat 1).comp hTop
  intro t
  have hh : Tendsto (fun j => ActualEnergyDimensionLimit.modelEnergy p β t (dim j-1))
      atTop (𝓝 (CKSpecification.energy p β d t)) := by
    simpa only [Function.comp_def,Real.toNNReal_coe,CKSpecification.energy,CKSpecification.memoryMass] using
      ((he t).tendsto_at (x:=(t:ℝ)) ⟨t.coe_nonneg,le_rfl⟩).comp hidx
  apply hh.congr'
  exact Eventually.of_forall fun j => by
    exact congrArg (fun N => ActualForkEnergySubtraction.modelEnergy N p β t)
      (Nat.sub_add_cancel (hDim j))


theorem primitive_bridge_from_preceding (β : ℝ≥0) {d : CKData}
    (h : CKEquations p β d)
    (hTrace : ActualTracePrimitiveConvergence (by have hh:=h.spin_ge_three;omega : 2≤p) β d)
    (dim : ℕ→ℕ) (hTop : Tendsto dim atTop atTop) :
    ResponsePrimitiveBridge (by have hh:=h.spin_ge_three;omega : 2≤p) β dim d := by
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  have hidx : Tendsto (fun j => dim j-1) atTop atTop := (tendsto_sub_atTop_nat 1).comp hTop
  intro T
  have hh := prefix_primitives_of_tail_primitives
    (fun n t u => responseRow hp β n t u-d.R t u)
    (by
      intro n t ht
      have hR : ContinuousOn (fun u => d.R t u) (Icc 0 t) :=
        h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun u hu => ⟨hu.1,hu.2⟩)
      exact (responseRow_integrable hp β n ht.1).sub (hR.intervalIntegrable_of_Icc ht.1))
    (hTrace T)
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact hidx.eventually (Metric.tendstoUniformlyOn_iff.mp hh ε hε)

end SphericalAging.CanonicalForkPrecedingBridges
