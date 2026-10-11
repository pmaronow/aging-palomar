module

public import SphericalAging.ForkWienerSampler
public import SphericalAging.ActualSphereMarkovRestart

public section

/-! Actual finite physical fork endpoints from a common initial point
and literal complete spliced Wiener paths. The parameter and whole trunk
Brownian history retain the exact original annealed joint law. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal
namespace SphericalAging.PhysicalForkConstruction
open FiniteModel HardSphereDynamics WienerForkTransfer ForkSeedCoordinates
  ForkWienerSampler WienerSplice WienerStoppedPath ActualSphereTransition
  ActualSphereMarkovRestart AnnealedHamiltonianEnergyStein ActualWeightedWiener
variable {N p K : ℕ}

@[expose] def branchForward (T : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N :=
  (z.1.1,splice T z.2 (z.1.2 b))

theorem branchForward_measurePreserving (T : ℝ≥0) (b : Fin K) :
    MeasurePreserving (branchForward (N:=N) (p:=p) T b) (forkLaw N p K)
      (AnnealedModelLaw.law N p) := by
  have h1 := (MeasurePreserving.id (AnnealedModelLaw.parameterLaw N p)).prod
    ((splice_measurePreserving (N:=N) T).comp (trunk_future_measurePreserving (N:=N) b))
  have hh := h1.comp (measurePreserving_prodAssoc (AnnealedModelLaw.parameterLaw N p)
    (futureLaw N K) (VectorBrownian.law N))
  convert hh using 1 <;> rfl

@[expose] def jointEndpoint (β : ℝ) (t : ℝ≥0)
    (z : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : Vector N :=
  jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β (N+1)
    (modelRadius_pos N) z.1 t z.2

@[expose] def branch (β : ℝ) (t T : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) : Vector N :=
  jointEndpoint β t (branchForward T b z)

theorem jointEndpoint_measurable (β : ℝ) (t : ℝ≥0) :
    Measurable (jointEndpoint (N:=N) (p:=p) β t) := by
  exact (jointProcess_adapted (NullAugmentation.driver (VectorBrownian.driver N))
    β (N+1) (modelRadius_pos N) t).measurable.mono
      (sup_le_sup le_rfl (MeasurableSpace.comap_mono
        ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le t))) le_rfl

theorem branch_measurable (β : ℝ) (t T : ℝ≥0) (b : Fin K) :
    Measurable (branch (N:=N) (p:=p) β t T b) :=
  (jointEndpoint_measurable β t).comp (branchForward_measurePreserving T b).measurable

theorem model_eq_jointEndpoint (β : ℝ) (t : ℝ≥0) :
    modelProcess N p β t=ᵐ[AnnealedModelLaw.law N p] jointEndpoint β t :=
  annealedGlobal_eq_joint (NullAugmentation.driver (VectorBrownian.driver N))
    β (N+1) (modelRadius_pos N) (AnnealedModelLaw.parameter_disorder_memLp N p) t

theorem trunkHistory_branchForward (T : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) :
    trunkHistory T (branchForward T b z).2=trunkHistory T z.2 := by
  funext u
  change WithLp.toLp 2 (fun i => (branchForward T b z).2 i u)=
    WithLp.toLp 2 (fun i => z.2 i u)
  congr 1
  funext i
  exact splice_apply_of_le T u u.property _ _ i

/-- The original parameter and entire trunk Brownian past are retained,
not merely a one-time Brownian marginal. -/
theorem rich_joint_law (β : ℝ) (t T : ℝ≥0) (b : Fin K) :
    HasLaw (fun z : ForkSpace N p K =>
      (branch β t T b z,(z.1.1,trunkHistory T z.2)))
      ((AnnealedModelLaw.law N p).map (fun z =>
        (modelProcess N p β t z,(z.1,trunkHistory T z.2)))) (forkLaw N p K) := by
  let test : (AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N)→
      Vector N×(AnnealedCutoffProcess.Parameter N p×History N T) :=
    fun z => (jointEndpoint β t z,(z.1,trunkHistory T z.2))
  have hm : Measurable test := (jointEndpoint_measurable β t).prodMk
    (measurable_fst.prodMk ((trunkHistory_measurable N T).comp measurable_snd))
  have hl := (hasLaw_map hm.aemeasurable).comp (branchForward_measurePreserving T b).hasLaw
  have he : (fun z : ForkSpace N p K => test (branchForward T b z))=
      (fun z => (branch β t T b z,(z.1.1,trunkHistory T z.2))) := by
    funext z
    change (branch β t T b z,(z.1.1,trunkHistory T (branchForward T b z).2))=_
    rw [trunkHistory_branchForward]
  rw [Function.comp_def] at hl
  rw [he] at hl
  have hmap : (AnnealedModelLaw.law N p).map test=
      (AnnealedModelLaw.law N p).map (fun z =>
        (modelProcess N p β t z,(z.1,trunkHistory T z.2))) := by
    apply Measure.map_congr
    filter_upwards [model_eq_jointEndpoint (N:=N) (p:=p) β t] with z hz
    exact congrArg (fun x => (x,(z.1,trunkHistory T z.2))) hz.symm
  exact hmap ▸ hl

theorem fork_joint_law (β : ℝ) (t T : ℝ≥0) :
    ForkJointLaw β t T (branch (N:=N) (p:=p) (K:=K) β t T) := by
  intro b
  let project : Vector N×(AnnealedCutoffProcess.Parameter N p×History N T)→Vector N×History N T :=
    fun z => (z.1,z.2.2)
  have hmeas : Measurable project := measurable_fst.prodMk (measurable_snd.comp measurable_snd)
  have hl := (hasLaw_map hmeas.aemeasurable).comp (rich_joint_law (N:=N) (p:=p) β t T b)
  have ho : AEMeasurable (fun z : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N =>
      (modelProcess N p β t z,(z.1,trunkHistory T z.2))) (AnnealedModelLaw.law N p) :=
    (model_memLp N p β t).aestronglyMeasurable.aemeasurable.prodMk
      (measurable_fst.prodMk ((trunkHistory_measurable N T).comp measurable_snd)).aemeasurable
  rw [AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable ho] at hl
  exact hl

end SphericalAging.PhysicalForkConstruction
