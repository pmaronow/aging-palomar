module

public import SphericalAging.SphereEulerTensorSourceHistory
public import SphericalAging.FiniteGeneratorProjectionMeasurable
public import SphericalAging.SphereEulerWaitingTransfer
public import SphericalAging.AdaptiveSourceProjectionMoments

public section

/-! The actual stopped Euler query stream on independent fork seed spaces.
Its initial span and every new gradient direction are measurable in the
literal tensor disclosure history. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereEulerForkTensorHistory
open Set MeasureTheory FiniteModel HardSphereDynamics AdaptiveGradientDisclosure
open SphereEulerTensorSourceHistory AdaptiveTensorDisclosureSource
open SphereEulerPredictable AdditiveSphereGaussianApproximation
open scoped NNReal InnerProductSpace
variable {N p K : ℕ}

@[expose] def initialVector (ξ : ForkSeedCoordinates.Seed N K) : State N := ξ.1.1

@[expose] def seedIncrement (T : ℝ≥0) (M j : ℕ) (ξ : ForkSeedCoordinates.Seed N K) : State N :=
  increment (NullAugmentation.driver (VectorBrownian.driver N)) (SphereEulerMeshRate.mesh T M) j ξ.2

@[expose] def seedColumns (T : ℝ≥0) (M : ℕ) (i : Fin (M+1)) (ξ : ForkSeedCoordinates.Seed N K) : State N :=
  Fin.cases (initialVector ξ) (fun j : Fin M => seedIncrement T M j ξ) i

theorem initialVector_measurable : Measurable (initialVector (N:=N) (K:=K)) :=
  measurable_fst.comp measurable_fst

theorem seedIncrement_measurable (T : ℝ≥0) (M j : ℕ) :
    Measurable (seedIncrement (N:=N) (K:=K) T M j) := by
  exact (SphereEulerSourceApproximation.seed_increment_measurable T M j).comp
    (initialVector_measurable.prodMk measurable_snd)

theorem seedColumns_measurable (T : ℝ≥0) (M : ℕ) (i : Fin (M+1)) :
    Measurable (seedColumns (N:=N) (K:=K) T M i) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact initialVector_measurable
  · exact seedIncrement_measurable T M j

theorem seedColumns_range (T : ℝ≥0) (M : ℕ) (ξ : ForkSeedCoordinates.Seed N K) :
    Set.range (fun i => seedColumns T M i ξ)=
      (SphereEulerSeedSpan.seedGenerators (initialVector ξ) (fun j => seedIncrement T M j ξ) M : Set (State N)) := by
  classical
  ext v
  constructor
  · rintro ⟨i,rfl⟩
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [seedColumns,Fin.cases_zero,SphereEulerSeedSpan.seedGenerators,
        Finset.mem_coe,Finset.mem_union,Finset.mem_singleton,true_or]
    · simp only [seedColumns,Fin.cases_succ,SphereEulerSeedSpan.seedGenerators,
        Finset.mem_coe,Finset.mem_union]
      exact Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr j.isLt,rfl⟩)
  · intro hv
    simp only [SphereEulerSeedSpan.seedGenerators,Finset.mem_coe,Finset.mem_union,Finset.mem_singleton] at hv
    rcases hv with rfl | hv
    · exact ⟨0,rfl⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hv
      exact ⟨(⟨j,Finset.mem_range.mp hj⟩ : Fin M).succ,rfl⟩

@[expose] def W0 (T : ℝ≥0) (M : ℕ) : ForkSeedCoordinates.Seed N K→Submodule ℝ (State N) :=
  initial initialVector (seedIncrement T M) M

theorem W0_projection_measurable (T : ℝ≥0) (M : ℕ) :
    Measurable (fun z : ForkSeedCoordinates.Seed N K×State N => (W0 T M z.1).starProjection z.2) := by
  have hh := FiniteGeneratorProjectionMeasurable.measurable_span_starProjection
    (seedColumns (N:=N) (K:=K) T M) (seedColumns_measurable T M)
  simpa only [W0,initial,seedColumns_range] using hh

theorem W0_finrank_le (T : ℝ≥0) (M : ℕ) (ξ : ForkSeedCoordinates.Seed N K) :
    Module.finrank ℝ (W0 T M ξ)≤M+1 := by
  classical
  change Module.finrank ℝ (Submodule.span ℝ
    (SphereEulerSeedSpan.seedGenerators (initialVector ξ) (fun j => seedIncrement T M j ξ) M : Set (State N)))≤M+1
  refine (finrank_span_finset_le_card (R:=ℝ)
    (SphereEulerSeedSpan.seedGenerators (initialVector ξ) (fun j => seedIncrement T M j ξ) M)).trans ?_
  unfold SphereEulerSeedSpan.seedGenerators
  exact (Finset.card_union_le _ _).trans
    (by simpa only [Finset.card_singleton,Nat.add_comm] using
      Nat.add_le_add_left ((Finset.card_image_le (s:=Finset.range M)
        (f:=fun j => seedIncrement T M j ξ)).trans_eq (Finset.card_range M)) 1)

@[expose] def u (β T : ℝ≥0) (M : ℕ) : ℕ→ForkSeedCoordinates.Seed N K×TensorSpace N p→State N :=
  direction β (SphereEulerMeshRate.mesh T M) initialVector (seedIncrement T M) M

theorem u_history_measurable (hp : 2≤p) (β T : ℝ≥0) (M j : ℕ) :
    Measurable[MeasurableSpace.comap (History (W0 (N:=N) (K:=K) T M) (u (N:=N) (p:=p) (K:=K) β T M) j) inferInstance]
      (u (N:=N) (p:=p) (K:=K) β T M j) :=
  direction_history_measurable hp β _ initialVector (seedIncrement T M) M
    initialVector_measurable (seedIncrement_measurable T M) (W0_projection_measurable T M) j

theorem u_orthogonal (β T : ℝ≥0) (M j : ℕ) (z : ForkSeedCoordinates.Seed N K×TensorSpace N p) :
    u β T M j z∈(Space (W0 T M) (u β T M) j z)ᗮ :=
  direction_orthogonal β _ initialVector (seedIncrement T M) M j z

theorem u_zero_or_unit (β T : ℝ≥0) (M j : ℕ) (z : ForkSeedCoordinates.Seed N K×TensorSpace N p) :
    u β T M j z=0 ∨ ‖u β T M j z‖=1 :=
  direction_zero_or_unit β _ initialVector (seedIncrement T M) M j z

theorem eulerWaiting_mem (β T : ℝ≥0) (M : ℕ) (z : ForkSeedCoordinates.Seed N K×Disorder N p) :
    SphereEulerWaitingTransfer.eulerWaiting β T M z∈
      Space (W0 T M) (u β T M) M (AdaptiveSourceProjectionMoments.sample z) := by
  exact rawQuery_mem β _ initialVector (seedIncrement T M) M M le_rfl
    (AdaptiveSourceProjectionMoments.sample z)

end SphericalAging.SphereEulerForkTensorHistory
