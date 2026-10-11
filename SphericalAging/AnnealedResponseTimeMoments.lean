module

public import SphericalAging.TwoTimeResponseTimeParameter
public import SphericalAging.AnnealedResponseMatrixContraction

public section

/-! A true joint waiting-time/disorder/initial-state/Brownian version of
each actual fixed-terminal response column, with a uniform annealed L⁴
bound on every waiting-time slice. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedResponseTimeMoments
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseTimeParameter
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma annealedFourthConstant_mono (p : ℕ) (β : ℝ≥0) {t H : ℝ≥0} (ht : t≤H) :
    annealedFourthConstant p β t≤annealedFourthConstant p β H := by
  unfold annealedFourthConstant GaussianLandscapeMoments.momentCeiling
  have htr : (t : ℝ)≤H := ht
  gcongr

theorem exists_fixedTerminalColumn_joint_L4 (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) (v : State N) :
    ∃ G : WaitingTime H × ((Disorder N p × State N) × Ω) → State N,StronglyMeasurable G ∧
      (∀ s q,(fun ω => G (s,(q,ω))) =ᵐ[P]
        (fixedTerminalColumn (Nat.ne_of_gt hN) D₀ β R hR hNR H v s q : Ω → State N)) ∧
      (∀ s,MemLp (fun q => G (s,q)) 4 ((parameterLaw N p).prod P) ∧
        (∫ q,‖G (s,q)‖^4 ∂(parameterLaw N p).prod P)≤‖v‖^4*annealedFourthConstant p β H) := by
  obtain ⟨G₀,hG₀,hGV₀⟩ := JointLpRepresentative.exists_joint_representative
    (Function.uncurry (fixedTerminalColumn (p := p) (Nat.ne_of_gt hN) D₀ β R hR hNR H v))
    (fixedTerminalColumn_joint_stronglyMeasurable (Nat.ne_of_gt hN) D₀ β R hR hNR H v)
  let G : WaitingTime H × ((Disorder N p × State N) × Ω) → State N :=
    fun q => G₀ ((q.1,q.2.1),q.2.2)
  have hG : StronglyMeasurable G := hG₀.comp_measurable
    ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk (measurable_snd.comp measurable_snd))
  have hGV (s : WaitingTime H) (q : Disorder N p × State N) :
      (fun ω => G (s,(q,ω))) =ᵐ[P]
        (fixedTerminalColumn (Nat.ne_of_gt hN) D₀ β R hR hNR H v s q : Ω → State N) := hGV₀ (s,q)
  refine ⟨G,hG,hGV,?_⟩
  intro s
  obtain ⟨K,hK,hKV,hK4,hKB⟩ := exists_responseColumn_annealed_L4 hN hp D₀ β R hR hNR s (H+1) (H-s)
    ((tsub_le_self : H-(s : ℝ≥0)≤H).trans (le_add_right le_rfl)) (by positivity) v
  have hGs : StronglyMeasurable (fun q => G (s,q)) := hG.comp_measurable (measurable_const.prodMk measurable_id)
  have he : (fun q => G (s,q))=ᵐ[(parameterLaw N p).prod P] K := by
    apply (Measure.ae_prod_iff_ae_ae (hGs.measurableSet_eq_fun hK)).mpr
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    have hfield : fixedTerminalColumn (Nat.ne_of_gt hN) D₀ β R hR hNR H v s q=
        responseColumn (NullAugmentation.driver D₀) β R hR s (H+1) (H-s) v q := by
      rw [fixedTerminalColumn,dif_pos hq]
      exact (responseColumn_eq_physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s)
        ((tsub_le_self : H-(s : ℝ≥0)≤H).trans (le_add_right le_rfl)) (by positivity) v q hq).symm
    exact ((hGV s q).trans (.of_forall (fun ω => congrArg (fun z : Lp (State N) 2 P => z ω) hfield))).trans (hKV q).symm
  refine ⟨(memLp_congr_ae he).mpr hK4,?_⟩
  rw [integral_congr_ae (he.mono (fun q hq => congrArg (fun z : State N => ‖z‖^4) hq))]
  exact hKB.trans (by
    simpa only [annealedFourthConstant,mul_assoc] using
      mul_le_mul_of_nonneg_left (annealedFourthConstant_mono p β (tsub_le_self : H-(s : ℝ≥0)≤H)) (by positivity : 0≤‖v‖^4))

end SphericalAging.AnnealedResponseTimeMoments
