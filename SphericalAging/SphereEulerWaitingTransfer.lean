module

public import SphericalAging.SphereEulerStoppedSeed
public import SphericalAging.PhysicalForkWaitingTransfer
public import SphericalAging.WaitingAlgorithmOrthogonality

public section

/-! Actual Euler approximation on every fork seed space. The physical
waiting state and Euler output are pulled back together by the genuine
measure-preserving original-trunk sampler. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
namespace SphericalAging.SphereEulerWaitingTransfer
open FiniteModel HardSphereDynamics SphereEulerModelApproximation
open SphereEulerSourceEstimate SphereEulerDimensionRate SphereEulerRandomInitialApproximation
open AdditiveSphereGaussianApproximation PhysicalForkWaitingTransfer
open AnnealedHamiltonianEnergyStein ForkOrderedParameters ActualWeightedWiener
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p K : ℕ}

@[expose] def originalSample (z : ForkSeedCoordinates.Seed N K×Disorder N p) : Sample N p :=
  originalTrunk (ForkSeedCoordinates.toFork z)

theorem originalSample_measurePreserving (N p K : ℕ) :
    MeasurePreserving (originalSample (N:=N) (p:=p) (K:=K))
      (FiniteForkMoments.measure N p K) (AnnealedModelLaw.law N p) :=
  (originalTrunk_measurePreserving N p K).comp (ForkSeedCoordinates.toFork_measurePreserving N p K)

@[expose] def eulerWaiting (β s : ℝ≥0) (M : ℕ) (z : ForkSeedCoordinates.Seed N K×Disorder N p) : State N :=
  output β s M (originalSample z)

theorem eulerWaiting_measurable (β s : ℝ≥0) (M : ℕ) :
    Measurable (eulerWaiting (N:=N) (p:=p) (K:=K) β s M) :=
  (output_measurable β s M).comp (originalSample_measurePreserving N p K).measurable

theorem eulerWaiting_norm_le (β s : ℝ≥0) (M : ℕ) (z : ForkSeedCoordinates.Seed N K×Disorder N p) :
    ‖eulerWaiting β s M z‖≤Real.sqrt N := output_norm_le β s M _

theorem waiting_error_integral_eq (β s : ℝ≥0) (M : ℕ) :
    (∫z,‖seededWaiting (N:=N) (p:=p) (K:=K) β s z-eulerWaiting β s M z‖^2/(N:ℝ)
      ∂FiniteForkMoments.measure N p K)=normalizedError N p β s M := by
  let f : Sample N p→ℝ := fun q => ‖modelProcess N p β s q-output β s M q‖^2/(N:ℝ)
  have hm : AEStronglyMeasurable f (AnnealedModelLaw.law N p) := by
    exact (continuous_id.div_const (N:ℝ)).comp_aestronglyMeasurable
      (((model_memLp N p β s).aestronglyMeasurable.sub
        (output_measurable β s M).aestronglyMeasurable).norm.pow 2)
  exact (originalSample_measurePreserving N p K).hasLaw.integral_comp hm

theorem waiting_error_le (hN : 2≤N) (hp : 2≤p) (β s : ℝ≥0) {M : ℕ} (hM : M≠0) :
    (∫z,‖seededWaiting (N:=N) (p:=p) (K:=K) β s z-eulerWaiting β s M z‖^2/(N:ℝ)
      ∂FiniteForkMoments.measure N p K)≤annealedBound N p β s M := by
  rw [waiting_error_integral_eq]
  exact actual_model_error_le hN hp β s hM

@[expose] def family (dim : ℕ→ℕ) (p : ℕ) (β s : ℝ≥0) (M : ℕ) :
    ∀θ n,WaitingAlgorithmOrthogonality.Space dim p θ n→State (dim n) :=
  fun θ n => eulerWaiting β s M

theorem family_measurable (dim : ℕ→ℕ) (p : ℕ) (β s : ℝ≥0) (M : ℕ) (θ : WaitingAlgorithmOrthogonality.Index) (n : ℕ) :
    Measurable (family dim p β s M θ n) := eulerWaiting_measurable β s M

theorem family_norm_le (dim : ℕ→ℕ) (p : ℕ) (β s : ℝ≥0) (M : ℕ) (θ : WaitingAlgorithmOrthogonality.Index) (n : ℕ)
    (z : WaitingAlgorithmOrthogonality.Space dim p θ n) :
    ‖family dim p β s M θ n z‖≤Real.sqrt (dim n) := eulerWaiting_norm_le β s M z

theorem family_dimension_limsup_le (dim : ℕ→ℕ) (hDim : Tendsto dim atTop atTop)
    (p : ℕ) (hp : 2≤p) (β s : ℝ≥0) {M : ℕ} (hM : M≠0) (θ : WaitingAlgorithmOrthogonality.Index) :
    limsup (fun n => ∫z,
      ‖seededWaiting (K:=branches θ.1) β s z-family dim p β s M θ n z‖^2/(dim n:ℝ)
        ∂WaitingAlgorithmOrthogonality.measure dim p θ n) atTop≤
      (globalRate p β (landscapeCutoff p) s:ℝ)*(s:ℝ)/(M:ℝ) := by
  have ht := (annealedBound_tendsto p β s M).comp hDim
  have hb : ∀ᶠn : ℕ in atTop,(∫z,
      ‖seededWaiting (K:=branches θ.1) β s z-family dim p β s M θ n z‖^2/(dim n:ℝ)
        ∂WaitingAlgorithmOrthogonality.measure dim p θ n)≤annealedBound (dim n) p β s M := by
    filter_upwards [hDim.eventually (eventually_ge_atTop 2)] with n hn
    exact waiting_error_le hn hp β s hM
  exact (limsup_le_limsup hb
    (isCoboundedUnder_le_of_le atTop (fun n => integral_nonneg
      (fun _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)))) ht.isBoundedUnder_le).trans_eq ht.limsup_eq

end SphericalAging.SphereEulerWaitingTransfer
