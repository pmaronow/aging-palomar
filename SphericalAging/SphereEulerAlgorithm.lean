module

public import SphericalAging.SphereEulerMeshRate
public import SphericalAging.SphereEulerQueryData

public section

/-! Literal ball-valued Euler output under the actual Brownian driver. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.SphereEulerAlgorithm
open FiniteModel HardSphereDynamics SphereEulerPredictable SphereEulerMeshRate
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def endpoint (D : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ)
    (J : Disorder N p) (x : State N) (omega : Ω) : State N :=
  SphereEulerCoefficients.clip (node D β (mesh T M) J x M omega)

theorem endpoint_norm_le (D : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ)
    (J : Disorder N p) (x : State N) (omega : Ω) :
    ‖endpoint D β T M J x omega‖≤Real.sqrt N :=
  SphereEulerCoefficients.clip_norm_le _

theorem endpoint_joint_measurable (D : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ) :
    Measurable (fun q : Ω×(Disorder N p×State N) => endpoint D β T M q.2.1 q.2.2 q.1) := by
  have hi (k : ℕ) : Measurable (increment D (mesh T M) k) :=
    ((increment_stronglyMeasurable D (mesh T M) k).mono (F.le _)).measurable
  have hh := SphereEulerQuerySpan.state_measurable (β:ℝ) (mesh T M:ℝ)
    (fun q : Ω×(Disorder N p×State N) => q.2.1) (fun q => q.2.2)
    (fun k q => increment D (mesh T M) k q.1)
    (measurable_fst.comp measurable_snd) (measurable_snd.comp measurable_snd)
    (fun k => (hi k).comp measurable_fst) M
  exact SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp hh

theorem endpoint_measurable (D : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ)
    (J : Disorder N p) (x : State N) : Measurable (endpoint D β T M J x) := by
  change Measurable (fun omega => SphereEulerCoefficients.clip (node D β (mesh T M) J x M omega))
  exact SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp
    (node_measurable D β (mesh T M) J x M)

theorem endpoint_mem_querySpace (D : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ)
    (J : Disorder N p) (x : State N) (omega : Ω) :
    endpoint D β T M J x omega∈SphereEulerQuerySpan.querySpace β (mesh T M) J x
      (fun k => increment D (mesh T M) k omega) M :=
  SphereEulerQuerySpan.output_mem β (mesh T M) J x _ M

theorem endpoint_memLp (D : BrownianDriver N P F) (β T : ℝ≥0) (M : ℕ)
    (J : Disorder N p) (x : State N) : MemLp (endpoint D β T M J x) 2 P :=
  MemLp.of_bound (endpoint_measurable D β T M J x).aestronglyMeasurable (Real.sqrt N)
    (.of_forall (endpoint_norm_le D β T M J x))

end SphericalAging.SphereEulerAlgorithm
