module

public import SphericalAging.FiniteForkMoments
public import SphericalAging.FiniteStateOrthogonalityTheorem

public section

/-! The literal physical waiting state on the fork trunk. Endpoint / waiting-state
joint law is the exact stronger marginal of source10.4's common physical past;
endpoint / Brownian history alone does not identify this disorder-dependent state. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.PhysicalForkWaitingTransfer
open MeasureTheory ProbabilityTheory FiniteModel WienerForkTransfer ForkSeedCoordinates
  FiniteForkMoments RandomGaussianPairing ActualWeightedWiener AnnealedHamiltonianEnergyStein
open scoped NNReal ENNReal InnerProductSpace BigOperators

@[expose] def originalTrunk {N p K : ℕ} (z : ForkSpace N p K) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N := (z.1.1,z.2)

theorem originalTrunk_measurePreserving (N p K : ℕ) :
    MeasurePreserving (originalTrunk (N:=N) (p:=p) (K:=K))
      (forkLaw N p K) (AnnealedModelLaw.law N p) := by
  exact ((MeasurePreserving.id (AnnealedModelLaw.parameterLaw N p)).prod
    (measurePreserving_snd (μ:=futureLaw N K) (ν:=VectorBrownian.law N))).comp
      (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
        (futureLaw N K) (VectorBrownian.law N))

@[expose] def waiting {N p K : ℕ} (β : ℝ) (s : ℝ≥0) (z : ForkSpace N p K) : Vector N :=
  modelProcess N p β s (originalTrunk z)

@[expose] def seededWaiting {N p K : ℕ} (β : ℝ) (s : ℝ≥0)
    (z : Seed N K×Disorder N p) : Vector N := waiting β s (toFork z)

theorem waiting_memLp (N p K : ℕ) (β : ℝ) (s : ℝ≥0) :
    MemLp (waiting (N:=N) (p:=p) (K:=K) β s) 2 (forkLaw N p K) :=
  (model_memLp N p β s).comp_measurePreserving (originalTrunk_measurePreserving N p K)

theorem seededWaiting_memLp (N p K : ℕ) (β : ℝ) (s : ℝ≥0) :
    MemLp (seededWaiting (N:=N) (p:=p) (K:=K) β s) 2 (measure N p K) :=
  (waiting_memLp N p K β s).comp_measurePreserving (toFork_measurePreserving N p K)

theorem seededWaiting_bound {N p K : ℕ} (hN : 0<N) (β : ℝ) (s : ℝ≥0) :
    ∀ᵐz ∂measure N p K,‖seededWaiting (N:=N) (p:=p) (K:=K) β s z‖≤Real.sqrt N :=
  (toFork_measurePreserving N p K).quasiMeasurePreserving.ae
    ((originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae
      (FiniteStateOrthogonalityTheorem.actual_model_waiting_state_ball hN β s))

@[expose] def originalPair (N p : ℕ) (β : ℝ) (t s : ℝ≥0)
    (z : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : Vector N×Vector N :=
  (modelProcess N p β t z,modelProcess N p β s z)

theorem originalPair_aemeasurable (N p : ℕ) (β : ℝ) (t s : ℝ≥0) :
    AEMeasurable (originalPair N p β t s) (AnnealedModelLaw.law N p) :=
  (model_memLp N p β t).aestronglyMeasurable.aemeasurable.prodMk
    (model_memLp N p β s).aestronglyMeasurable.aemeasurable

/-- The exact endpoint/common-physical-past marginal of the finite fork. -/
@[expose] def PhysicalPastLaw {N p K : ℕ} (β : ℝ) (t s : ℝ≥0)
    (Y : Fin K→ForkSpace N p K→Vector N) : Prop :=
  ∀b,HasLaw (fun z => (Y b z,waiting β s z))
    ((AnnealedModelLaw.law N p).map (originalPair N p β t s)) (forkLaw N p K)

@[expose] def expectedOverlap (N p : ℕ) (β : ℝ) (t s : ℝ≥0) : ℝ :=
  pairing (μ:=AnnealedModelLaw.law N p) (modelProcess N p β t) (modelProcess N p β s)

theorem branch_waiting_pairing {N p K : ℕ} {β : ℝ} {t s : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hPast : PhysicalPastLaw β t s Y) (b : Fin K) :
    pairing (μ:=forkLaw N p K) (Y b) (waiting β s)=expectedOverlap N p β t s := by
  let test : Vector N×Vector N→ℝ := fun z => inner ℝ z.1 z.2
  have hm : AEStronglyMeasurable test
      ((AnnealedModelLaw.law N p).map (originalPair N p β t s)) :=
    (continuous_fst.inner continuous_snd).measurable.aestronglyMeasurable
  have he := (hPast b).integral_comp hm
  have ho := (hasLaw_map (originalPair_aemeasurable N p β t s)).integral_comp hm
  exact congrArg (fun x : ℝ => x/(N:ℝ)) (he.trans ho.symm)

theorem mean_waiting_pairing {N p K : ℕ} (hK : 0<K) {β : ℝ} {t T s : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N}
    (hY : ForkJointLaw β t T Y) (hPast : PhysicalPastLaw β t s Y) :
    pairing (μ:=measure N p K) (seededMean Y) (seededWaiting β s)=
      expectedOverlap N p β t s := by
  have hKn : (K:ℝ)≠0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hK)
  have hi b := inner_integrable (branch_memLp hY b) (waiting_memLp N p K β s)
  have he : (∫z,inner ℝ (mean Y z) (waiting β s z) ∂forkLaw N p K)=
      (K:ℝ)⁻¹*∑b : Fin K,(∫z,inner ℝ (Y b z) (waiting β s z) ∂forkLaw N p K) := by
    simp only [mean,real_inner_smul_left,sum_inner]
    rw [integral_const_mul,integral_finset_sum Finset.univ (fun b _ => hi b)]
  have hf : pairing (μ:=forkLaw N p K) (mean Y) (waiting β s)=expectedOverlap N p β t s := by
    unfold pairing
    rw [he]
    have hb : ∀b : Fin K,(∫z,inner ℝ (Y b z) (waiting β s z) ∂forkLaw N p K)/(N:ℝ)=
        expectedOverlap N p β t s := fun b => branch_waiting_pairing hPast b
    rw [mul_div_assoc,Finset.sum_div]
    simp only [hb,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
    field_simp
  unfold pairing seededMean seededWaiting FiniteForkMoments.measure
  rw [toFork_integral (fun z => inner ℝ (mean Y z) (waiting β s z))]
  exact hf

end SphericalAging.PhysicalForkWaitingTransfer
