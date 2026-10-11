module

public import SphericalAging.BrownianFuturePath

public section

/-! The literal entire stopped Wiener path is genuinely measurable from
the actual past filtration. It therefore has true independence from the
entire future increment path; this supports exact trunk/future splicing. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory MeasurableSpace
open scoped NNReal ENNReal
namespace SphericalAging.WienerStoppedPath
open VectorBrownian BrownianFuturePath
set_option maxHeartbeats 1200000

/-- Stop a continuous scalar path at the deterministic trunk time. -/
@[expose] def scalarStopped (T : ℝ≥0) (omega : Path) : Path :=
  ⟨fun t => omega (min t T),omega.continuous.comp (continuous_id.min continuous_const)⟩

theorem scalarStopped_measurable (T : ℝ≥0) : Measurable (scalarStopped T) := by
  rw [ContinuousMap.measurable_iff_eval]
  exact fun t => scalar_eval_measurable (min t T)

/-- The full coordinate vector of stopped continuous paths. -/
@[expose] def stopped {N : ℕ} (T : ℝ≥0) (omega : Space N) : Space N :=
  fun i => scalarStopped T (omega i)

theorem stopped_measurable {N : ℕ} (T : ℝ≥0) : Measurable (stopped (N:=N) T) :=
  measurable_pi_iff.mpr (fun i => (scalarStopped_measurable T).comp (measurable_pi_apply i))

theorem stopped_apply {N : ℕ} (T t : ℝ≥0) (omega : Space N) (i : Fin N) :
    stopped T omega i t=omega i (min t T) := rfl

theorem stopped_apply_of_le {N : ℕ} (T t : ℝ≥0) (ht : t≤T) (omega : Space N) (i : Fin N) :
    stopped T omega i t=omega i t := by simp only [stopped_apply,min_eq_left ht]

theorem stopped_idempotent {N : ℕ} (T : ℝ≥0) (omega : Space N) :
    stopped T (stopped T omega)=stopped T omega := by
  funext i
  apply ContinuousMap.ext
  intro t
  simp only [stopped_apply,min_assoc,min_self]

/-- Every evaluation of the stopped wholepath is actually observed at T. -/
theorem stopped_filtered {N : ℕ} (T : ℝ≥0) :
    @Measurable (Space N) (Space N) (filtration N T) inferInstance (stopped T) := by
  letI : MeasurableSpace (Space N) := filtration N T
  apply measurable_pi_iff.mpr
  intro i
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact ((coordinate_stronglyAdapted i (min t T)).mono
    ((filtration N).mono (min_le_right t T))).measurable

theorem stopped_comap_le {N : ℕ} (T : ℝ≥0) :
    MeasurableSpace.comap (stopped (N:=N) T) inferInstance≤filtration N T :=
  (stopped_filtered T).comap_le

/-- The actual stopped trunk path and full future increment path are independent. -/
theorem stopped_indep_future {N : ℕ} (T : ℝ≥0) :
    IndepFun (stopped (N:=N) T) (future T) (law N) := by
  rw [IndepFun_iff_Indep]
  exact (indep_of_indep_of_le_right (future_indep_filtration T) (stopped_comap_le T)).symm

theorem stopped_future_measurePreserving {N : ℕ} (T : ℝ≥0) :
    MeasurePreserving (fun omega : Space N => (stopped T omega,future T omega))
      (law N) (((law N).map (stopped T)).prod (law N)) := by
  refine ⟨(stopped_measurable T).prodMk (future_measurable T),?_⟩
  rw [(stopped_indep_future T).map_prod_eq_prod_map_map
    (stopped_measurable T).aemeasurable (future_measurable T).aemeasurable,future_map]

end SphericalAging.WienerStoppedPath
