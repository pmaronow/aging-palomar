module

public import SphericalAging.WienerStoppedPath

public section

/-! A genuine full Wiener path obtained by joining a trunk and an
independent future. The law follows from the exact stopped/future
decomposition of Wiener measure and pointwise reconstruction. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace SphericalAging.WienerSplice
open VectorBrownian BrownianFuturePath WienerStoppedPath
set_option maxHeartbeats 800000

@[expose] def scalarSplice (T : ℝ≥0) (trunk next : Path) : Path :=
  ⟨fun t => trunk (min t T)+next (t-T)-next 0,
    ((trunk.continuous.comp (continuous_id.min continuous_const)).add
      (next.continuous.comp (continuous_id.sub continuous_const))).sub continuous_const⟩

@[expose] def splice {N : ℕ} (T : ℝ≥0) (trunk next : Space N) : Space N :=
  fun i => scalarSplice T (trunk i) (next i)

theorem splice_apply {N : ℕ} (T t : ℝ≥0) (trunk next : Space N) (i : Fin N) :
    splice T trunk next i t=trunk i (min t T)+next i (t-T)-next i 0 := rfl

theorem splice_measurable {N : ℕ} (T : ℝ≥0) :
    Measurable (fun z : Space N×Space N => splice T z.1 z.2) := by
  apply measurable_pi_iff.mpr
  intro i
  rw [ContinuousMap.measurable_iff_eval]
  intro t
  exact (((scalar_eval_measurable (min t T)).comp
    ((measurable_pi_apply i).comp measurable_fst)).add
    ((scalar_eval_measurable (t-T)).comp ((measurable_pi_apply i).comp measurable_snd))).sub
    ((scalar_eval_measurable 0).comp ((measurable_pi_apply i).comp measurable_snd))

theorem splice_stopped {N : ℕ} (T : ℝ≥0) (trunk next : Space N) :
    splice T (stopped T trunk) next=splice T trunk next := by
  funext i
  apply ContinuousMap.ext
  intro t
  simp only [splice_apply,stopped_apply,min_assoc,min_self]

theorem splice_reconstruct {N : ℕ} (T : ℝ≥0) (omega : Space N) :
    splice T (stopped T omega) (future T omega)=omega := by
  funext i
  apply ContinuousMap.ext
  intro t
  simp only [splice_apply,stopped_apply,min_assoc,min_self,future,scalarFuture,
    ContinuousMap.coe_mk,add_zero,sub_self,sub_zero]
  by_cases ht : t≤T
  · simp only [min_eq_left ht,tsub_eq_zero_of_le ht,add_zero,sub_self,add_zero,sub_zero]
  · have hT : T≤t := le_of_not_ge ht
    rw [min_eq_right hT,add_tsub_cancel_of_le hT]
    ring

theorem stoppedSplice_measurePreserving {N : ℕ} (T : ℝ≥0) :
    MeasurePreserving (fun z : Space N×Space N => splice T z.1 z.2)
      (((law N).map (stopped T)).prod (law N)) (law N) := by
  refine ⟨splice_measurable T,?_⟩
  rw [←(stopped_future_measurePreserving (N:=N) T).map_eq,
    Measure.map_map (splice_measurable T) (stopped_future_measurePreserving T).measurable]
  simp only [Function.comp_def,splice_reconstruct]
  change (law N).map id=law N
  exact Measure.map_id

/-- Independent complete trunk and future Wiener samples give a true
complete Wiener sample, with the entire trunk unchanged before T. -/
theorem splice_measurePreserving {N : ℕ} (T : ℝ≥0) :
    MeasurePreserving (fun z : Space N×Space N => splice T z.1 z.2)
      ((law N).prod (law N)) (law N) := by
  have hstop : MeasurePreserving (stopped (N:=N) T) (law N) ((law N).map (stopped T)) :=
    ⟨stopped_measurable T,rfl⟩
  have hh := (stoppedSplice_measurePreserving (N:=N) T).comp
    (hstop.prod (MeasurePreserving.id (law N)))
  simpa only [Function.comp_def,Prod.map_fst,Prod.map_snd,id_eq,splice_stopped] using hh

theorem splice_apply_of_le {N : ℕ} (T t : ℝ≥0) (ht : t≤T) (trunk next : Space N)
    (i : Fin N) : splice T trunk next i t=trunk i t := by
  simp only [splice_apply,min_eq_left ht,tsub_eq_zero_of_le ht,add_sub_cancel_right]

end SphericalAging.WienerSplice
