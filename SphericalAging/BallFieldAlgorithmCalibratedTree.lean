module

public import SphericalAging.BallFieldAlgorithmTreeSuccess
public import SphericalAging.ActualAlgorithmTreeGlobalEvent
public import SphericalAging.ClampedUniformOverlapMesh

public section

/-! Construct the real calibrated Gaussian tree for every ball field
algorithm. Its literal global overlap event and complete variance schedule
are derived from the algorithm, with uniform deterministic mesh spacing. -/
noncomputable section
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.BallFieldAlgorithmCalibratedTree
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ExternalFieldUniformCost BallFieldAlgorithmTreeSuccess AlgorithmicCorrelationContinuity
open ClampedUniformOverlapMesh ActualAlgorithmTreeGlobalEvent ActualAlgorithmTree
open IndependentBranchingSuccess GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open AlgorithmicOverlapConcentration RegularTreeGlobalToLocal
open scoped NNReal
variable {N p K : ℕ} {L : ℝ≥0}

theorem output_lipschitz (A : BallFieldAlgorithm N p L) : LipschitzWith L (output A) :=
  A.lipschitz_output

theorem output_ball (A : BallFieldAlgorithm N p L) : ∀s,‖output A s‖≤Real.sqrt N :=
  fun s => A.ball_output _

@[expose] def overlapMesh (A : BallFieldAlgorithm N p L) (D : ℕ) : ℕ→ℝ :=
  mesh (correlation (output A) 0) (correlation (output A) 1) D

@[expose] def variance (hN : 0<N) (A : BallFieldAlgorithm N p L) (D : ℕ) : ℕ→ℝ :=
  AlgorithmicNoiseCalibration.varianceSchedule (correlation (output A))
    (AlgorithmicCorrelationContinuity.correlation_continuous hN (output A)
      (output_lipschitz A).continuous (output_ball A)).continuousOn (overlapMesh A D) D

theorem actual_calibrated_global_tree (hN : 0<N) (A : BallFieldAlgorithm N p L)
    (D : ℕ) (hD : 0<D) (ε : ℝ) (hε : 0≤ε) :
    let q := overlapMesh A D
    let V := variance hN A D
    Monotone q ∧ (∀l,q l∈Icc (0:ℝ) 1) ∧ (∀l,q (l+1)-q l≤1/(D:ℝ)) ∧
    V 0=1 ∧ V D=0 ∧ (∀j,V j∈Icc (0:ℝ) 1) ∧ (∀j,V (j+1)≤V j) ∧
    MeasurableSet (goodEvent (K:=K) (output A) V D ε) ∧
    1-unionBudget K D (2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ))))≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)).real
        (goodEvent (K:=K) (output A) V D ε) ∧
    ∀z∈goodEvent (K:=K) (output A) V D ε,
      GlobalOverlapTree q ε D (outputTree (output A) (update (parentCoefficient V) (freshCoefficient V)) D z.1 z.2) := by
  obtain ⟨hc,hm,hr,_h0,_h1⟩ := AlgorithmicCorrelationMonotonicity.actual_source_HS_2_1 hN
    (output A) (output_lipschitz A).continuous (output_ball A)
  have hh := actual_uniform_calibration (correlation (output A)) hc.continuousOn hm hr D hD
  dsimp only at hh
  obtain ⟨hq,hq0,hqD,hqrange,hmesh,hV0,hVD,hV,hVm,hspec⟩ := hh
  have hqd : overlapMesh A D D=correlation (output A) 1 := hqD
  have hqs : ∀j : Fin D,overlapMesh A D j.val=correlation (output A) (variance hN A D (D-j.val)) :=
    fun j => (hspec j.val j.isLt.le).symm
  have he := actual_global_overlap_event (K:=K) hN (variance hN A D) (fun j => (hV j).1) hVm hV0
    (fun j => (hV j).2) (output A) (output_lipschitz A) (output_ball A) D (overlapMesh A D) hqd hqs ε hε
  refine ⟨hq,?_,hmesh,hV0,hVD,hV,hVm,he⟩
  intro l
  exact ⟨(hr 0 (by norm_num)).1.trans (hqrange l).1,(hqrange l).2.trans (hr 1 (by norm_num)).2⟩

end SphericalAging.BallFieldAlgorithmCalibratedTree
