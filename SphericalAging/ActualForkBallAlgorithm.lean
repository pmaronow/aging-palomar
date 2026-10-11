module

public import SphericalAging.AdditiveSphereFiniteFamilyAlgorithm
public import SphericalAging.ForkWienerSampler
public import SphericalAging.FiniteForkMoments

public section

/-! Source10.4's actual finite-fork Lipschitz algorithms. The branch is
the literal physical endpoint from its true initial point and a complete
trunk/future-spliced Wiener path. The projected-mean approximation error
is proved to converge to zero from the genuine additive strong error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualForkBallAlgorithm
open FiniteModel HardSphereDynamics LocalSDE LandscapeMetricProjection ActualSphereTransition
open AdditiveSphereGaussianApproximation AdditiveSphereFiniteFamilyAlgorithm
open FiniteFamilyBallApproximation AnnealedHamiltonianEnergyStein
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkWienerSampler
set_option maxHeartbeats 150000
set_option backward.isDefEq.respectTransparency false
variable {N p K : ℕ}

/-- Literal physical branch endpoint; its entire path shares the trunk before T. -/
@[expose] def branch (β : ℝ≥0) (t T : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) : State N :=
  jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
    (modelRadius_pos N) z.1.1 t (WienerSplice.splice T z.2 (z.1.2 b))

theorem seeded_branch_eq_endpoint (β : ℝ≥0) (t T : ℝ≥0) (b : Fin K)
    (z : Seed N K×Disorder N p) :
    branch β t T b (toFork z)=endpoint β t (initialBranch T b) z := rfl

theorem projected_seededMean_eq_output (β : ℝ≥0) (t T : ℝ≥0) (Q : ℝ)
    (z : Seed N K×Disorder N p) :
    ForkNormalizedEnergy.projected Q (seededMean (branch β t T)) z=
      output Q (fun b => endpoint β t (initialBranch T b) z) := rfl

/-- Genuine source10.4(i) approximation, for fixed times before the
large-dimensional limit and the true independent finite-fork seed. -/
theorem exists_actual_fork_ball_algorithm (hK : 0<K) {p : ℕ} (hp : 2≤p)
    (dim : ℕ→ℕ) (hDim : ∀n,2≤dim n) (hDimTop : Tendsto dim atTop atTop)
    (β : ℝ≥0) (L T : ℝ≥0) (Q : ℝ) (hQ : 0<Q) :
    ∃ Lip : ℝ≥0,∃ A : ∀n,Seed (dim n) K×Disorder (dim n) p→State (dim n),
      (∀n,Measurable (A n)) ∧
      (∀n ξ,LipschitzWith Lip (fun J : CoefficientSpace (dim n) p => A n (ξ,J.ofLp))) ∧
      (∀n ξ J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧
      Tendsto (fun n => (∫z,‖A n z-ForkNormalizedEnergy.projected Q
        (seededMean (branch β (T+L) T)) z‖^2 ∂measure (dim n) p K)/(dim n:ℝ)) atTop (𝓝 0) := by
  obtain ⟨A,hA,hLip,hBall,hError⟩ := exists_finite_family_algorithm hK hp dim hDim hDimTop
    (fun n => Seed (dim n) K) (fun n => ForkSeedCoordinates.law (dim n) K)
      (fun _n b => initialBranch T b) (fun _n b => initialBranch_measurePreserving T b)
        β (T+L) (T+L) le_rfl Q hQ
  refine ⟨normalizedRate (AdditiveSphereJointParameter.jointRate p β (landscapeCutoff p) (T+L)) Q,
    A,hA,hLip,hBall,?_⟩
  apply hError.congr'
  exact .of_forall (fun n => by
    congr 1)

end SphericalAging.ActualForkBallAlgorithm
