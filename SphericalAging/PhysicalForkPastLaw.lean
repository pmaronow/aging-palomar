module

public import SphericalAging.PhysicalForkConstruction
public import SphericalAging.PhysicalForkWaitingTransfer
public import SphericalAging.WienerPastCausality

public section

/-! Exact physical common-past law for the constructed finite fork.
Past adaptedness is proved through an actual original-filtration
representative, and the full spliced Wiener law transfers the original
endpoint/waiting-state joint law. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory StochasticCalculus Set
open scoped NNReal ENNReal
namespace SphericalAging.PhysicalForkPastLaw
open FiniteModel HardSphereDynamics WienerForkTransfer WienerSplice WienerStoppedPath
  PhysicalForkConstruction PhysicalForkWaitingTransfer WienerPastCausality
  ActualSphereTransition AnnealedHamiltonianEnergyStein
variable {N p K : ℕ}

theorem stopped_branchForward (T : ℝ≥0) (b : Fin K) (z : ForkSpace N p K) :
    stopped T (branchForward T b z).2=stopped T (originalTrunk z).2 := by
  funext i
  apply ContinuousMap.ext
  intro t
  simp only [stopped_apply]
  exact splice_apply_of_le T (min t T) (min_le_right t T) _ _ i

/-- This is genuine physical causality for the actual joint SDE family.
Both paths retain their true original Wiener laws. -/
theorem jointEndpoint_prefix_eq (β : ℝ) (s T : ℝ≥0) (hs : s≤T) (b : Fin K) :
    (fun z : ForkSpace N p K => jointEndpoint β s (branchForward T b z))=ᵐ[forkLaw N p K]
      (fun z => jointEndpoint β s (originalTrunk z)) := by
  have hf := jointProcess_adapted (NullAugmentation.driver (VectorBrownian.driver N))
    (p:=p) β (N+1) (modelRadius_pos N) s
  obtain ⟨g,hg,he⟩ := exists_background_past_representative
    (ρ:=AnnealedModelLaw.parameterLaw N p) hs hf
  have he1 := (branchForward_measurePreserving (N:=N) (p:=p) T b).quasiMeasurePreserving.ae he
  have he2 := (originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae he
  filter_upwards [he1,he2] with z h1 h2
  change jointEndpoint β s (branchForward T b z)=g (branchForward T b z) at h1
  change jointEndpoint β s (originalTrunk z)=g (originalTrunk z) at h2
  rw [h1,h2]
  apply hg.factorsThrough
  change ((branchForward T b z).1,stopped T (branchForward T b z).2)=
    ((originalTrunk z).1,stopped T (originalTrunk z).2)
  rw [stopped_branchForward]
  rfl

/-- A branch physically agrees with the actual original waiting state
at every fixed observed time s≤T. -/
theorem branch_prefix_eq_waiting (β : ℝ) (s T : ℝ≥0) (hs : s≤T) (b : Fin K) :
    branch (N:=N) (p:=p) β s T b=ᵐ[forkLaw N p K] waiting β s := by
  have hp := jointEndpoint_prefix_eq (N:=N) (p:=p) β s T hs b
  have hm := (originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae
    (model_eq_jointEndpoint (N:=N) (p:=p) β s)
  filter_upwards [hp,hm] with z hz hmz
  exact hz.trans hmz.symm

/-- The exact stronger marginal required by PhysicalForkStanding.past_law
is derived from the actual constructed branch. -/
theorem physical_past_law (β : ℝ) (t T s : ℝ≥0) (hs : s≤T) :
    PhysicalPastLaw β t s (branch (N:=N) (p:=p) (K:=K) β t T) := by
  intro b
  let test : (AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N)→Vector N×Vector N :=
    fun z => (jointEndpoint β t z,jointEndpoint β s z)
  have hm : Measurable test := (jointEndpoint_measurable β t).prodMk (jointEndpoint_measurable β s)
  have hl := (hasLaw_map hm.aemeasurable).comp (branchForward_measurePreserving (N:=N) (p:=p) T b).hasLaw
  have hmap : (AnnealedModelLaw.law N p).map test=
      (AnnealedModelLaw.law N p).map (originalPair N p β t s) := by
    apply Measure.map_congr
    filter_upwards [model_eq_jointEndpoint (N:=N) (p:=p) β t,
      model_eq_jointEndpoint (N:=N) (p:=p) β s] with z ht hz
    exact Prod.ext ht.symm hz.symm
  rw [hmap] at hl
  apply hl.congr
  filter_upwards [branch_prefix_eq_waiting (N:=N) (p:=p) β s T hs b] with z hz
  change (branch β t T b z,waiting β s z)=
    (branch β t T b z,branch β s T b z)
  rw [hz]

end SphericalAging.PhysicalForkPastLaw
