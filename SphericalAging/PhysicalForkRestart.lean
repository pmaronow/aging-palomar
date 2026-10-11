module

public import SphericalAging.PhysicalForkPastLaw

public section

/-! The constructed whole-path branch is the literal independent-future
physical restart from the common waiting state. The identity uses actual
conditional restart and the exact common-prefix construction. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal
namespace SphericalAging.PhysicalForkRestart
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
  PhysicalForkConstruction PhysicalForkPastLaw PhysicalForkWaitingTransfer
  WienerForkTransfer WienerSplice BrownianFuturePath AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p K : ℕ}

theorem future_splice {N : ℕ} (T : ℝ≥0) (trunk next : VectorBrownian.Space N)
    (hnext : ∀i,next i 0=0) : future T (splice T trunk next)=next := by
  funext i
  apply ContinuousMap.ext
  intro t
  change splice T trunk next i (T+t)-splice T trunk next i T=next i t
  rw [splice_apply,splice_apply,min_eq_right (le_self_add),min_self,
    add_tsub_cancel_left,tsub_self,hnext i]
  ring

theorem wiener_zero {N : ℕ} : ∀ᵐomega ∂VectorBrownian.law N,∀i,omega i 0=0 := by
  exact ae_all_iff.mpr (fun i =>
    (VectorBrownian.coordinate_isPreBrownian i).eval_zero_ae_eq_zero)

theorem branchFuture_measurePreserving (b : Fin K) :
    MeasurePreserving (fun z : ForkSpace N p K => z.1.2 b) (forkLaw N p K) (VectorBrownian.law N) := by
  exact (measurePreserving_eval (fun _ : Fin K => VectorBrownian.law N) b).comp
    ((measurePreserving_snd (μ:=AnnealedModelLaw.parameterLaw N p) (ν:=futureLaw N K)).comp
      (measurePreserving_fst (μ:=seedLaw N p K) (ν:=VectorBrownian.law N)))

@[expose] def jointRestart (β : ℝ) (T L : ℝ≥0)
    (z : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : State N :=
  jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
    (z.1.1,jointEndpoint β T z) L (future T z.2)

theorem jointRestart_measurable (β : ℝ) (T L : ℝ≥0) :
    Measurable (jointRestart (N:=N) (p:=p) β T L) := by
  have hparam : Measurable (fun z : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N =>
      (z.1.1,jointEndpoint β T z)) := (measurable_fst.comp measurable_fst).prodMk
    (jointEndpoint_measurable β T)
  have htime : Measurable (fun z : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N =>
      (L,future T z.2)) := measurable_const.prodMk ((future_measurable T).comp measurable_snd)
  exact (jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N))
    β (N+1) (modelRadius_pos N)).measurable.comp (hparam.prodMk htime)

theorem jointEndpoint_restart (hN : 0<N) (β : ℝ) (T L : ℝ≥0) :
    jointEndpoint (N:=N) (p:=p) β (T+L)=ᵐ[AnnealedModelLaw.law N p] jointRestart β T L := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_eq_fun
    (jointEndpoint_measurable β (T+L)) (jointRestart_measurable β T L))).mpr
  filter_upwards [AnnealedModelLaw.parameter_initial_onSphere (by omega : 1≤N) p] with q hq
  exact actual_future_eq_joint (Nat.ne_of_gt hN) β (N+1) (modelRadius_pos N) (modelRadius_sq N)
    q.1 (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N) q)
    (fun horizon => jointProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N)
      β (N+1) (modelRadius_pos N) (modelRadius_sq N) q.1 q.2 hq horizon)
    (jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N)
      β (N+1) (modelRadius_pos N) (modelRadius_sq N) q.1 q.2 hq) T L

@[expose] def restartedBranch (β : ℝ) (T L : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) : State N :=
  jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
    (z.1.1.1,jointEndpoint β T (originalTrunk z)) L (z.1.2 b)

/-- The literal branch law is identified with its actual independent
future path and common canonical waiting state. -/
theorem branch_eq_restarted (hN : 0<N) (β : ℝ) (T L : ℝ≥0) (b : Fin K) :
    branch (N:=N) (p:=p) β (T+L) T b=ᵐ[forkLaw N p K] restartedBranch β T L b := by
  have hr := (branchForward_measurePreserving (N:=N) (p:=p) T b).quasiMeasurePreserving.ae
    (jointEndpoint_restart hN β T L)
  have hp := jointEndpoint_prefix_eq (N:=N) (p:=p) β T T le_rfl b
  have hz := (branchFuture_measurePreserving (N:=N) (p:=p) b).quasiMeasurePreserving.ae wiener_zero
  filter_upwards [hr,hp,hz] with z hr hp hz
  change branch β (T+L) T b z=jointRestart β T L (branchForward T b z) at hr
  rw [hr]
  change jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1) (modelRadius_pos N)
    (z.1.1.1,jointEndpoint β T (branchForward T b z)) L (future T (splice T z.2 (z.1.2 b)))=_
  rw [future_splice T z.2 (z.1.2 b) hz,hp]
  rfl

theorem branch_eq_physical_restart (hN : 0<N) (β : ℝ) (T L : ℝ≥0) (b : Fin K) :
    branch (N:=N) (p:=p) β (T+L) T b=ᵐ[forkLaw N p K]
      (fun z => jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
        β (N+1) (modelRadius_pos N) (z.1.1.1,waiting β T z) L (z.1.2 b)) := by
  have hr := branch_eq_restarted (N:=N) (p:=p) hN β T L b
  have hm := (originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae
    (model_eq_jointEndpoint (N:=N) (p:=p) β T)
  filter_upwards [hr,hm] with z hr hm
  rw [hr]
  unfold restartedBranch
  rw [←hm]
  rfl

end SphericalAging.PhysicalForkRestart
