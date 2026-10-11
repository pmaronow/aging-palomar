module

public import SphericalAging.ActualAlgorithmTreeEnergy

public section

/-! The actual original-disorder field success probability produces the
literal high-energy tree, with uniform Euclidean coefficient algorithms. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.BallFieldAlgorithmTreeSuccess
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ExternalFieldUniformCost ExternalFieldProbabilityTransfer HamiltonianBranchingNodeLaw
open ActualAlgorithmTree ActualAlgorithmTreeEnergy IndependentBranchingSuccess
open IndependentBranchingSuccessEvent GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open HamiltonianTreeFieldBand
open scoped InnerProductSpace NNReal
variable {N p K : ℕ} {L : ℝ≥0}

@[expose] def output (A : BallFieldAlgorithm N p L) : TensorSpace N p→Vector N :=
  fun s => A.output (tensorDecode s)

@[expose] def success (A : BallFieldAlgorithm N p L) (κ E : ℝ) : Set (Disorder N p) :=
  {J | E≤ballEnergy A.output J+κ*ballOverlap A.direction A.output J}

theorem success_measurable (A : BallFieldAlgorithm N p L) (κ E : ℝ) :
    MeasurableSet (success A κ E) :=
  measurableSet_le measurable_const ((ballEnergy_measurable A.measurable_output).add
    ((ballOverlap_measurable A.direction A.measurable_output).const_mul κ))

theorem success_probability_eq (A : BallFieldAlgorithm N p L) (κ E : ℝ) :
    (stdGaussian (TensorSpace N p)).real (fieldSuccess (output A) (κ • A.direction) E)=
      (disorderLaw N p).real (success A κ E) := by
  have hlaw : HasLaw (tensorDecode (N:=N) (p:=p)) (disorderLaw N p) (stdGaussian (TensorSpace N p)) :=
    ⟨tensorDecode_measurePreserving.measurable.aemeasurable,tensorDecode_measurePreserving.map_eq⟩
  have he : fieldSuccess (output A) (κ • A.direction) E=tensorDecode ⁻¹' success A κ E := by
    ext s
    simp only [fieldSuccess,output,success,mem_setOf_eq,mem_preimage,ballEnergy,ballOverlap,
      real_inner_smul_left,mul_div_assoc]
  rw [he]
  exact hlaw.measureReal_eq (success_measurable A κ E)

theorem actual_original_disorder_tree_success (hK : 0<K) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) (hV0 : V 0=1)
    (A : BallFieldAlgorithm N p L) (κ E : ℝ) (d : ℕ) :
    let Z := event K (update (parentCoefficient V) (freshCoefficient V))
      (fieldSuccess (output A) (κ • A.direction) E) d
    MeasurableSet Z ∧ ((disorderLaw N p).real (success A κ E))^(K^d)≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real Z ∧
    ∀z∈Z,E≤totalLeafEnergy V d (κ • A.direction)
      (outputTree (output A) (update (parentCoefficient V) (freshCoefficient V)) d z.1 z.2) z := by
  have hh := actual_algorithm_high_energy_tree hK V hV hVm hV0 (output A)
    (A.measurable_output.comp tensorDecode.continuous.measurable) (κ • A.direction) E d
  dsimp only at hh
  rw [success_probability_eq A κ E] at hh
  exact hh

end SphericalAging.BallFieldAlgorithmTreeSuccess
