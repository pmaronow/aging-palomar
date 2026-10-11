module

public import SphericalAging.ActualBallResponseFieldMoments
public import SphericalAging.PhysicalForkEnergySections
public import SphericalAging.ActualFiniteHorizonTraceReplacement

public section

/-! The actual finite-fork center response correction has a uniform
annealed O(N^(-1/2)) integrated bound, with every matrix, seed, ball bound
and moment derived from the constructed physical branches. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace SphericalAging.ActualForkResponseError
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics PhysicalForkDrivers PhysicalForkMeanEnergyDuhamel PhysicalForkEnergySections
  TwoTimeResponseParameter TwoTimeResponseTimeParameter AnnealedTwoTimeResponseMoments
  AnnealedResponseMatrixContraction AnnealedResponseTimeMatrix ActualFiniteHorizonTraceReplacement
  EnergyCovarianceContraction ResponseMatrixEnergyContraction ActualBallResponseFieldMoments
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

private theorem integrated_abs_secondMoment {A Ω : Type*} [MeasurableSpace A] [MeasurableSpace Ω]
    {ν : Measure A} {P : Measure Ω} [IsFiniteMeasure ν] [IsProbabilityMeasure P]
    {f : A×Ω→ℝ} {B : ℝ} (hf : StronglyMeasurable f)
    (hm : ∀a,MemLp (fun ω => f (a,ω)) 2 P)
    (hB : ∀a,(∫ω,(f (a,ω))^2 ∂P)≤B) :
    Integrable f (ν.prod P) ∧ (∫q,|f q| ∂ν.prod P)≤ν.real univ*Real.sqrt B := by
  have hs (a : A) : Integrable (fun ω => |f (a,ω)|) P ∧ (∫ω,|f (a,ω)| ∂P)≤Real.sqrt B := by
    refine ⟨?_,(integral_abs_le_sqrt_secondMoment (hm a)).trans (Real.sqrt_le_sqrt (hB a))⟩
    simpa only [Real.norm_eq_abs] using ((hm a).integrable (by norm_num)).norm
  have hfa : StronglyMeasurable (fun q => |f q|) := by simpa only [Real.norm_eq_abs] using hf.norm
  have hF : Integrable (fun a => ∫ω,|f (a,ω)| ∂P) ν :=
    (integrable_const (Real.sqrt B)).mono' hfa.integral_prod_right'.aestronglyMeasurable
      (.of_forall fun a => by
        rw [Real.norm_of_nonneg (integral_nonneg fun _ => abs_nonneg _)]
        exact (hs a).2)
  have hi : Integrable (fun q => |f q|) (ν.prod P) := by
    apply (integrable_prod_iff hfa.aestronglyMeasurable).mpr
    refine ⟨.of_forall fun a => (hs a).1,?_⟩
    simpa only [Real.norm_eq_abs,abs_abs] using hF
  refine ⟨(integrable_norm_iff hf.aestronglyMeasurable).mp (by simpa only [Real.norm_eq_abs] using hi),?_⟩
  rw [integral_prod _ hi]
  exact (integral_mono_ae hF (integrable_const _) (.of_forall fun a => (hs a).2)).trans_eq (by
    rw [integral_const];rfl)

theorem exists_actual_fork_integrated_response_error (hN : 0<N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk : ℝ≥0) (b : Fin K) :
    ∃U : WaitingTime t×((Disorder N p×State N)×PathSeed N K)→State N→L[ℝ] State N,
      StronglyMeasurable U ∧
      (∀s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω)))=ᵐ[pathSeedLaw N K]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) (driver (N:=N) (K:=K) trunk b) β (N+1)
          (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N)
          s (t+1) (t-s) q hx)) ∧
      let ν := (waitingMeasure t).prod ((parameterLaw N p).prod (pathSeedLaw N K))
      let e := fun q : WaitingTime t×((Disorder N p×State N)×PathSeed N K) =>
        energyCorrection (p:=p) (actualMean β t trunk q.2.1.1 q.2.1.2 q.2.2)
          (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
            (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2) (U q)
      Integrable e ν ∧ (∫q,|e q| ∂ν)≤
        (t:ℝ)*Real.sqrt (((p:ℝ)^2*((p:ℝ)-1)^2/(N:ℝ))*(1+annealedFourthConstant p β t)) := by
  obtain ⟨U,hU,hUs,hUM⟩ := exists_actual_fixedTerminal_matrix hN hp (driver (N:=N) (K:=K) trunk b) β (N+1)
    (AnnealedHamiltonianEnergyStein.modelRadius_pos N) (AnnealedHamiltonianEnergyStein.modelRadius_sq N) t
  let M := fun q : (Disorder N p×State N)×PathSeed N K => actualMean β t trunk q.1.1 q.1.2 q.2
  have hM : StronglyMeasurable M := (actualMean_joint_measurable β t trunk).stronglyMeasurable
  have hMm := hM.aestronglyMeasurable (μ:=(parameterLaw N p).prod (pathSeedLaw N K))
  have hMb := actualMean_joint_ball (N:=N) (p:=p) hK β t trunk
  let e := fun q : WaitingTime t×((Disorder N p×State N)×PathSeed N K) =>
    energyCorrection (p:=p) (M q.2)
      (trajectory (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1)
        (AnnealedHamiltonianEnergyStein.modelRadius_pos N) q.1 q.2) (U q)
  have hY := waitingTrajectory_stronglyMeasurable (p:=p)
    (NullAugmentation.driver (driver (N:=N) (K:=K) trunk b)) β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N) t
  have he : StronglyMeasurable e := by
    have hX : StronglyMeasurable (fun q : WaitingTime t×((Disorder N p×State N)×PathSeed N K) => M q.2) := hM.comp_snd
    have hUX := (continuous_fst.clm_apply continuous_snd).comp_stronglyMeasurable (hU.prodMk hX)
    have ha := (hX.inner hY).mul_const (N:ℝ)⁻¹
    have hh := ((ha.pow (p-2)).mul (hY.inner hUX)).const_mul ((p:ℝ)*((p:ℝ)-1)/(N:ℝ)^2)
    convert hh using 1
    funext q
    simp only [e,energyCorrection,FiniteCorrelationIto.overlap,Pi.mul_apply,Pi.pow_apply,div_eq_mul_inv]
    ring
  have hbound (s : WaitingTime t) := actual_ball_field_energyCorrection_moments hN hp
    (driver (N:=N) (K:=K) trunk b) β (N+1) (AnnealedHamiltonianEnergyStein.modelRadius_pos N)
      (AnnealedHamiltonianEnergyStein.modelRadius_sq N) t U hU hUs s hMm hMb
  have hi := integrated_abs_secondMoment (ν:=waitingMeasure t) he
    (fun s => (hbound s).1) (fun s => (hbound s).2.1)
  refine ⟨U,hU,hUs,hi.1,?_⟩
  simpa only [waitingMeasure_real_univ] using hi.2

end SphericalAging.ActualForkResponseError
