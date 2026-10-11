module

public import SphericalAging.RandomLinearStrongOperations
public import SphericalAging.RandomInitialDependence
public import SphericalAging.CausalTerminalDuhamel

public section

/-! Actual random-initial terminal propagation is a continuous linear map
on the full initial-filtration L² space. Bounded random initial scalars
propagate with the same scalar, through the genuine full-driver Itô SDE. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RandomLinearTerminalOperations
open HardSphereDynamics LocalSDE PredictableLinearCoefficient RandomInitialDependence
open CausalTerminalDuhamel RandomLinearVariationalSDE
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {Kb Ks : ℝ≥0}

/-- True terminal propagation on all correlated F₀ random initial states. -/
@[expose] def terminalOperator (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks) (T t : ℝ≥0) :
    InitialSpace N F P →L[ℝ] Lp (State N) 2 P :=
  (lpMeas (State N) ℝ (F 0) 2 P).subtypeL+
    (terminalEvolution D a sigma T t).comp (RandomInitialDependence.response D a sigma T)

theorem terminalOperator_initialStateClass (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P) (T t : ℝ≥0) :
    terminalOperator D a sigma T t (initialStateClass Z0 hZ0 hmem)=
      terminalClass D a sigma Z0 hZ0 hmem T t := by
  simp only [terminalOperator,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    response_initialStateClass,terminalEvolution_apply]
  rfl

/-- The true random-initial terminal map depends only on the initial L² class. -/
theorem terminalClass_initial_congr (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 W0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hW0 : StronglyMeasurable[F 0] W0)
    (hmZ : MemLp Z0 2 P) (hmW : MemLp W0 2 P) (he : Z0=ᵐ[P] W0) (T t : ℝ≥0) :
    terminalClass D a sigma Z0 hZ0 hmZ T t=terminalClass D a sigma W0 hW0 hmW T t := by
  rw [← terminalOperator_initialStateClass,← terminalOperator_initialStateClass]
  congr 1
  apply Subtype.ext
  apply Lp.ext
  exact hmZ.coeFn_toLp.trans (he.trans hmW.coeFn_toLp.symm)

lemma bounded_scalar_memLp (Z0 : Ω → State N) (hmem : MemLp Z0 2 P)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F 0] C) (K : ℝ≥0) (hK : ∀ omega,‖C omega‖≤K) :
    MemLp (fun omega => C omega • Z0 omega) 2 P := by
  apply hmem.of_le_mul (c := (K : ℝ))
    ((hC.mono (F.le 0)).aestronglyMeasurable.smul hmem.aestronglyMeasurable)
  filter_upwards [] with omega
  change ‖C omega • Z0 omega‖≤(K : ℝ)*‖Z0 omega‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hK omega) (norm_nonneg _)

/-- Genuine propagation of a bounded correlated random scalar. -/
theorem terminalClass_bounded_scalar (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (C : Ω → ℝ) (hC : StronglyMeasurable[F 0] C) (K : ℝ≥0) (hK : ∀ omega,‖C omega‖≤K)
    (T t : ℝ≥0) (ht : t≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    terminalClass D a sigma (fun omega => C omega • Z0 omega) (hC.smul hZ0)
      (bounded_scalar_memLp Z0 hmem C hC K hK) T t =ᵐ[P]
      (fun omega => C omega • terminalClass D a sigma Z0 hZ0 hmem T t omega) := by
  have hscaled := RandomLinearStrongOperations.bounded_initial_scalar_mul
    (process_strongSolution D a sigma Z0 hZ0 hmem T) C hC K hK
  have hcanonical := process_strongSolution D a sigma (fun omega => C omega • Z0 omega)
    (hC.smul hZ0) (bounded_scalar_memLp Z0 hmem C hC K hK) T
  have he := pathwise_uniqueness hcanonical hscaled hnull
  filter_upwards [terminalClass_ae D a sigma (fun omega => C omega • Z0 omega)
    (hC.smul hZ0) (bounded_scalar_memLp Z0 hmem C hC K hK) T t,
    terminalClass_ae D a sigma Z0 hZ0 hmem T t,he] with omega hc h0 he
  rw [hc,h0]
  exact he t ht

/-- Actual initial L² classes respect a finite pointwise decomposition. -/
theorem initialStateClass_eq_sum {ι : Type*} [Fintype ι]
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (W : ι → Ω → State N) (hW : ∀ i,StronglyMeasurable[F 0] (W i))
    (hmW : ∀ i,MemLp (W i) 2 P) (he : Z0=ᵐ[P] (fun omega => ∑ i,W i omega)) :
    initialStateClass Z0 hZ0 hmem=∑ i,initialStateClass (W i) (hW i) (hmW i) := by
  classical
  apply Subtype.ext
  apply Lp.ext
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i => (hmW i).toLp (W i))
  have hi := ae_all_iff.mpr (fun i => (hmW i).coeFn_toLp)
  filter_upwards [hmem.coeFn_toLp,hs,hi,he] with omega h0 hs hi he
  simp only [Submodule.coe_sum]
  change (hmem.toLp Z0) omega=(∑ i,(hmW i).toLp (W i) : Lp (State N) 2 P) omega
  rw [h0,hs,he]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => (hi i).symm)

/-- Finite random initial coordinates propagate through the genuine
terminal SDE with their actual bounded initial-filtration coefficients. -/
theorem terminalClass_bounded_sum {ι : Type*} [Fintype ι]
    (D : BrownianDriver N P F)
    (a : Fin N → Coefficient (N := N) (F := F) (P := P) Kb)
    (sigma : Fin N → Fin N → Coefficient (N := N) (F := F) (P := P) Ks)
    (Z0 : Ω → State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hmem : MemLp Z0 2 P)
    (Z : ι → Ω → State N) (hZ : ∀ i,StronglyMeasurable[F 0] (Z i)) (hmZ : ∀ i,MemLp (Z i) 2 P)
    (C : ι → Ω → ℝ) (hC : ∀ i,StronglyMeasurable[F 0] (C i))
    (K : ℝ≥0) (hK : ∀ i omega,‖C i omega‖≤K)
    (he : Z0=ᵐ[P] (fun omega => ∑ i,C i omega • Z i omega))
    (T t : ℝ≥0) (ht : t≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    terminalClass D a sigma Z0 hZ0 hmem T t =ᵐ[P]
      (fun omega => ∑ i,C i omega • terminalClass D a sigma (Z i) (hZ i) (hmZ i) T t omega) := by
  classical
  let W := fun i omega => C i omega • Z i omega
  let hW := fun i => (hC i).smul (hZ i)
  let hmW := fun i => bounded_scalar_memLp (Z i) (hmZ i) (C i) (hC i) K (hK i)
  have heclass := initialStateClass_eq_sum Z0 hZ0 hmem W hW hmW he
  have heterminal : terminalClass D a sigma Z0 hZ0 hmem T t=
      ∑ i,terminalClass D a sigma (W i) (hW i) (hmW i) T t := by
    rw [← terminalOperator_initialStateClass,heclass,map_sum]
    exact Finset.sum_congr rfl (fun i _ => terminalOperator_initialStateClass D a sigma (W i) (hW i) (hmW i) T t)
  rw [heterminal]
  have hs := Lp.coeFn_finsetSum Finset.univ (fun i => terminalClass D a sigma (W i) (hW i) (hmW i) T t)
  have hi := ae_all_iff.mpr (fun i => terminalClass_bounded_scalar D a sigma
    (Z i) (hZ i) (hmZ i) (C i) (hC i) K (hK i) T t ht hnull)
  filter_upwards [hs,hi] with omega hs hi
  rw [hs]
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun i _ => hi i)

end SphericalAging.RandomLinearTerminalOperations
