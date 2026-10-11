module

public import SphericalAging.PurePActualPublishedFieldThreshold
public import SphericalAging.HamiltonianBranchingNodeLaw

public section

/-! The pure-p field threshold in the manuscript's literal coefficient
coordinates. Lipschitz continuity alone constructs the measurable algorithm;
the direction and algorithm are quantified after the uniform constants. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace SphericalAging.PurePFieldThresholdLiteral

open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ExternalFieldUniformCost ExternalFieldProbabilityTransfer
open ExternalFieldElementaryPenalty HamiltonianBranchingNodeLaw
open SphereGibbsEntropy
open scoped InnerProductSpace NNReal ENNReal

variable {N p : ℕ} {L : ℝ≥0}

/-- A Lipschitz map on the genuine coefficient Hilbert space gives the
algorithm record without an additional measurability assumption. -/
@[expose] def ofTensorAlgorithm (A : TensorSpace N p → Vector N)
    (hA : LipschitzWith L A) (hBall : ∀J, ‖A J‖ ≤ Real.sqrt N)
    (w : Vector N) (hw : ‖w‖ = Real.sqrt N) : BallFieldAlgorithm N p L where
  output J := A (WithLp.toLp 2 J)
  measurable_output := hA.continuous.measurable.comp
    (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable
  lipschitz_output := by simpa only [WithLp.toLp_ofLp] using hA
  ball_output J := hBall (WithLp.toLp 2 J)
  direction := w
  norm_direction := hw

/-- The same constructor in raw ordered-disorder coordinates. The specified
Lipschitz norm is the coefficient Hilbert norm, as in the source. -/
@[expose] def ofOrderedAlgorithm (A : Disorder N p → Vector N)
    (hA : LipschitzWith L (fun J : TensorSpace N p => A J.ofLp))
    (hBall : ∀J, ‖A J‖ ≤ Real.sqrt N)
    (w : Vector N) (hw : ‖w‖ = Real.sqrt N) : BallFieldAlgorithm N p L where
  output := A
  measurable_output := by
    have h := hA.continuous.measurable.comp
      (PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable
    simpa only [Function.comp_def, WithLp.ofLp_toLp] using h
  lipschitz_output := hA
  ball_output := hBall
  direction := w
  norm_direction := hw

/-- Literal source 10.1 under the product of ordered independent standard
Gaussian coefficients. The constants are chosen before the dimension,
deterministic direction, and algorithm. -/
theorem source10_1_ordered (hp : 3 ≤ p) (L : ℝ≥0)
    {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) :
    ∃c > 0, ∃N0 : ℕ, ∀N, N0 ≤ N →
      ∀w : Vector N, ‖w‖ = Real.sqrt N →
      ∀A : Disorder N p → Vector N,
        LipschitzWith L (fun J : TensorSpace N p => A J.ofLp) →
        (∀J, ‖A J‖ ≤ Real.sqrt N) →
        (disorderLaw N p).real {J | algorithmicField p κ + η ≤
          (Hamiltonian N p J (A J) + κ * ⟪w, A J⟫_ℝ) / (N : ℝ)} ≤
            Real.exp (-c * (N : ℝ)) := by
  obtain ⟨c, hc, M, hM⟩ :=
    PurePActualPublishedFieldThreshold.actual_published_field_threshold hp L κ hκ η hη
  refine ⟨c, hc, max M 1, ?_⟩
  intro N hN w hw A hA hBall
  have hb := hM N ((le_max_left M 1).trans hN)
    ((le_max_right M 1).trans hN) (ofOrderedAlgorithm A hA hBall w hw)
  have he : {J : Disorder N p | algorithmicField p κ + η ≤
      ballEnergy (ofOrderedAlgorithm A hA hBall w hw).output J +
        κ * ballOverlap (ofOrderedAlgorithm A hA hBall w hw).direction
          (ofOrderedAlgorithm A hA hBall w hw).output J} =
      {J | algorithmicField p κ + η ≤
        (Hamiltonian N p J (A J) + κ * ⟪w, A J⟫_ℝ) / (N : ℝ)} := by
    ext J
    change (algorithmicField p κ + η ≤
      Hamiltonian N p J (A J) / (N : ℝ) + κ * (⟪w, A J⟫_ℝ / (N : ℝ))) ↔ _
    rw [show Hamiltonian N p J (A J) / (N : ℝ) +
      κ * (⟪w, A J⟫_ℝ / (N : ℝ)) =
      (Hamiltonian N p J (A J) + κ * ⟪w, A J⟫_ℝ) / (N : ℝ) by ring]
    rfl
  rw [he] at hb
  exact hb

/-- Literal source 10.1 on the standard Gaussian coefficient Hilbert space.
No algorithm record or separate measurability hypothesis is supplied. -/
theorem source10_1_tensor (hp : 3 ≤ p) (L : ℝ≥0)
    {κ η : ℝ} (hκ : 0 ≤ κ) (hη : 0 < η) :
    ∃c > 0, ∃N0 : ℕ, ∀N, N0 ≤ N →
      ∀w : Vector N, ‖w‖ = Real.sqrt N →
      ∀A : TensorSpace N p → Vector N, LipschitzWith L A →
        (∀J, ‖A J‖ ≤ Real.sqrt N) →
        (stdGaussian (TensorSpace N p)).real {J | algorithmicField p κ + η ≤
          (Hamiltonian N p J.ofLp (A J) + κ * ⟪w, A J⟫_ℝ) / (N : ℝ)} ≤
            Real.exp (-c * (N : ℝ)) := by
  obtain ⟨c, hc, N0, hN0⟩ := source10_1_ordered hp L hκ hη
  refine ⟨c, hc, N0, ?_⟩
  intro N hN w hw A hA hBall
  let B : Disorder N p → Vector N := fun J => A (WithLp.toLp 2 J)
  have hB : LipschitzWith L (fun J : TensorSpace N p => B J.ofLp) := by
    simpa only [B, WithLp.toLp_ofLp] using hA
  have hBallB : ∀J, ‖B J‖ ≤ Real.sqrt N := fun J => hBall (WithLp.toLp 2 J)
  have hMeas : Measurable B :=
    (ofTensorAlgorithm A hA hBall w hw).measurable_output
  have hEvent : MeasurableSet {J : Disorder N p | algorithmicField p κ + η ≤
      (Hamiltonian N p J (B J) + κ * ⟪w, B J⟫_ℝ) / (N : ℝ)} := by
    have hH : Measurable (fun J : Disorder N p => Hamiltonian N p J (B J)) :=
      (Hamiltonian_joint_continuous N p).measurable.comp (measurable_id.prodMk hMeas)
    have hW : Measurable (fun J : Disorder N p => ⟪w, B J⟫_ℝ) :=
      (continuous_const.inner continuous_id).measurable.comp hMeas
    apply measurableSet_le measurable_const
    exact (hH.add (hW.const_mul κ)).div_const _
  have hEq := (tensorDecode_measurePreserving (N := N) (p := p)).hasLaw.measureReal_eq hEvent
  have hb := hN0 N hN w hw B hB hBallB
  calc
    (stdGaussian (TensorSpace N p)).real {J | algorithmicField p κ + η ≤
        (Hamiltonian N p J.ofLp (A J) + κ * ⟪w, A J⟫_ℝ) / (N : ℝ)} =
        (disorderLaw N p).real {J | algorithmicField p κ + η ≤
          (Hamiltonian N p J (B J) + κ * ⟪w, B J⟫_ℝ) / (N : ℝ)} := by
      change (stdGaussian (TensorSpace N p)).real
        {J : TensorSpace N p | algorithmicField p κ + η ≤
          (Hamiltonian N p J.ofLp (B J.ofLp) + κ * ⟪w, B J.ofLp⟫_ℝ) / (N : ℝ)} =
        (disorderLaw N p).real {J | algorithmicField p κ + η ≤
          (Hamiltonian N p J (B J) + κ * ⟪w, B J⟫_ℝ) / (N : ℝ)} at hEq
      simpa only [B, WithLp.toLp_ofLp] using hEq
    _ ≤ Real.exp (-c * (N : ℝ)) := hb

end SphericalAging.PurePFieldThresholdLiteral
