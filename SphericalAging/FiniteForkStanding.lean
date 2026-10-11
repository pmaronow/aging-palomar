module

public import SphericalAging.RemoteResponseFixedTime
public import SphericalAging.ForkParameterBounds

public section

/-! The literal preceding source 10.4 finite-fork standing input, on the
actual independent initial/disorder/trunk/future probability space. This
interface records only 10.4; it contains no remote-response conclusion. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace SphericalAging.FiniteForkStanding
open FiniteModel CKSpecification WienerForkTransfer ForkSeedCoordinates FiniteForkMoments
open ForkParameterBounds ForkNormalizedEnergy ExternalFieldElementaryPenalty

@[expose] def energyError {p K : ℕ} (dim : ℕ→ℕ) (e : ℝ)
    (Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)) : ℝ :=
  limsup (fun n => |(∫z,Hamiltonian (dim n) p z.1.1.1 (mean (Y n) z)
    ∂forkLaw (dim n) p K)/(dim n:ℝ)-e|) atTop
@[expose] def normError {p K : ℕ} {dim : ℕ→ℕ} (Q : ℝ)
    (Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)) : ℝ :=
  limsup (fun n => ∫z,(‖mean (Y n) z‖^2/(dim n:ℝ)-Q)^2
    ∂forkLaw (dim n) p K) atTop

/-- The source 10.4 construction and its three printed conclusions, with
the outer time sequence allowed to be any realizing diverging sequence. -/
structure Forks (dim : ℕ→ℕ) (p : ℕ) (β e : ℝ) (c r : ℝ→ℝ) where
  branches : ∀(K : ℕ) (L T : ℝ≥0),∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)
  branch_law : ∀K L T n,ForkJointLaw β (T+L) T (branches K L T n)
  energy_limit : ∀K,1≤K→∀L : ℝ≥0,∀t : ℕ→ℝ≥0,
    (∀n,0<t n)→Tendsto (fun n => (t n:ℝ)) atTop atTop→
      Tendsto (fun n => energyError dim (forkEnergy p β e c r K L) (branches K L (t n))) atTop (𝓝 0)
  concentration_limit : ∀K,1≤K→∀L : ℝ≥0,∀t : ℕ→ℝ≥0,
    (∀n,0<t n)→Tendsto (fun n => (t n:ℝ)) atTop atTop→
      Tendsto (fun n => normError (forkNorm c K L) (branches K L (t n))) atTop (𝓝 0)
  ceiling : ∀K,1≤K→∀L : ℝ≥0,
    forkEnergy p β e c r K L≤thresholdEnergy p*(forkNorm c K L)^((p:ℝ)/2)
  approximation : ∀K,1≤K→∀L T : ℝ≥0,0<T→∀ε : ℝ,0<ε→
    ∃Lip : ℝ≥0,∃A : ∀n,Seed (dim n) K×Disorder (dim n) p→Vector (dim n),
      (∀n,Measurable (A n)) ∧
      (∀n,∀ᵐξ ∂ForkSeedCoordinates.law (dim n) K,
        LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => A n (ξ,J.ofLp)) ∧
          ∀J,‖A n (ξ,J)‖≤Real.sqrt (dim n)) ∧
      limsup (fun n => (∫z,‖A n z-projected (forkNorm c K L)
        (seededMean (branches K L T n)) z‖^2 ∂measure (dim n) p K)/(dim n:ℝ)) atTop≤ε^2

end SphericalAging.FiniteForkStanding
