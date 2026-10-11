module

public import SphericalAging.PhysicalForkNormalizationLimits
public import SphericalAging.PhysicalForkPastLaw
public import SphericalAging.ActualForkBallAlgorithm

public section

/-! The completed non-energy clauses of source10.4, all for the literal
whole-path physical forks. Energy subtraction and the threshold ceiling
are separate analytic clauses. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkNormTheorem
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open WienerForkTransfer ForkSeedCoordinates FiniteForkMoments ForkNormalizedEnergy
open PhysicalForkConstruction PhysicalForkPastLaw PhysicalForkWaitingTransfer
open PhysicalForkCenterConcentration PhysicalForkNormalizationLimits
open AnnealedHamiltonianEnergyStein ForkParameterBounds
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints
open scoped NNReal ENNReal Topology

/-- Source10.4(c)'s literal fixed-time finite-fork algorithm statement,
with a stronger every-seed coefficient Lipschitz and ball bound and an
actual approximation limit equal to zero. -/
theorem actual_fork_approximation {p K : ℕ} (hK : 0<K) (hp : 2≤p)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (β : ℝ≥0) {Q : ℝ} (hQ : 0<Q) (L T : ℝ≥0) (ε : ℝ) :
    ∃Lip : ℝ≥0,∃A : ∀j,Seed (dim j) K×Disorder (dim j) p→Vector (dim j),
      (∀j,Measurable (A j)) ∧
      (∀j,∀ᵐξ ∂ForkSeedCoordinates.law (dim j) K,
        LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (dim j) p) => A j (ξ,J.ofLp)) ∧
          ∀J,‖A j (ξ,J)‖≤Real.sqrt (dim j)) ∧
      limsup (fun j => (∫z,‖A j z-projected Q
        (seededMean (branch β (T+L) T)) z‖^2 ∂measure (dim j) p K)/(dim j:ℝ)) atTop≤ε^2 := by
  obtain ⟨Lip,A,hA,hLip,hBall,hError⟩ :=
    ActualForkBallAlgorithm.exists_actual_fork_ball_algorithm hK hp dim hDim hTop β L T Q hQ
  refine ⟨Lip,A,hA,fun j => Eventually.of_forall (fun ξ => ⟨hLip j ξ,hBall j ξ⟩),?_⟩
  have he : Tendsto (fun j => (∫z,‖A j z-projected Q
      (seededMean (branch β (T+L) T)) z‖^2 ∂measure (dim j) p K)/(dim j:ℝ)) atTop (𝓝 0) := by
    exact hError
  rw [he.limsup_eq]
  exact sq_nonneg ε

/-- All source10.4 clauses concerning the common past, norm concentration,
the actual Lipschitz algorithms, and both additional normalization
replacements. Only the exact preceding CK mean and Fisher extraction
interfaces are inputs; no finite-fork conclusion is an input. -/
theorem source10_4_non_energy {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) :
    (∀j (S : ℝ≥0),SphericalAging.WienerForkTransfer.ForkJointLaw β (S+L) S
      (branch (N:=dim j) (p:=p) (K:=K) β (S+L) S)) ∧
    (∀j (S s : ℝ≥0),s≤S→PhysicalPastLaw β (S+L) s
      (branch (N:=dim j) (p:=p) (K:=K) β (S+L) S)) ∧
    Tendsto (fun n => FiniteForkStanding.normError (forkNorm c K L)
      (fun j => branch (N:=dim j) (p:=p) (K:=K) β
        ((T n).toNNReal+L) (T n).toNNReal)) atTop (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => normalizationError (forkNorm c K L)
      (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
    Tendsto (fun n => limsup (fun j => radialError (forkNorm c K L)
      (branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal)) atTop)
        atTop (𝓝 0) ∧
    (∀S : ℝ≥0,∀ε : ℝ,0<ε→
      ∃Lip : ℝ≥0,∃A : ∀j,Seed (dim j) K×Disorder (dim j) p→Vector (dim j),
        (∀j,Measurable (A j)) ∧
        (∀j,∀ᵐξ ∂ForkSeedCoordinates.law (dim j) K,
          LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (dim j) p) => A j (ξ,J.ofLp)) ∧
            ∀J,‖A j (ξ,J)‖≤Real.sqrt (dim j)) ∧
        limsup (fun j => (∫z,‖A j z-projected (forkNorm c K L)
          (seededMean (branch β (S+L) S)) z‖^2 ∂measure (dim j) p K)/(dim j:ℝ)) atTop≤ε^2) := by
  have hm := actual_normalization_errors H hT dim hDim hTop E hLaw hbridge hi hn hL1 hK L
  refine ⟨fun j S => fork_joint_law β (S+L) S,
    fun j S s hs => physical_past_law β (S+L) S s hs,
    actual_normError_tendsto H hT dim hDim hTop E hLaw hbridge hi hn hL1 hK L,
    hm.1,hm.2,?_⟩
  intro S ε _hε
  exact actual_fork_approximation hK (by have hp:=h.spin_ge_three;omega) dim hDim hTop β
    (forkNorm_pos_of_profile H.profile hK L) L S ε

end SphericalAging.PhysicalForkNormTheorem
