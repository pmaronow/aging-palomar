module

public import SphericalAging.AnnealedResponseTimeMoments

public section

/-! One genuine jointly measurable fixed-terminal matrix response across
waiting time, disorder, sphere initial state, and Brownian noise. The
normalized trace L⁴ and rank-one energy error L² bounds are uniform on
the full finite waiting-time interval. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedResponseTimeMatrix
open HardSphereDynamics FiniteModel TwoTimeResponseParameter TwoTimeResponseTimeParameter
open ResponseMatrixEnergyContraction EnergyCovarianceContraction
open AnnealedTwoTimeResponseMoments AnnealedResponseMatrixContraction AnnealedResponseTimeMoments
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem exists_actual_fixedTerminal_matrix (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0) :
    ∃ U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ s q (hx : OnSphere q.2),(fun ω => U (s,(q,ω))) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx)) ∧
      (∀ s,MemLp (fun q => normalizedTrace (U (s,q))) 4 ((parameterLaw N p).prod P) ∧
        (∫ q,|normalizedTrace (U (s,q))|^4 ∂(parameterLaw N p).prod P)≤annealedFourthConstant p β H ∧
        MemLp (fun q => energyCorrection (p := p)
          (trajectory (NullAugmentation.driver D₀) β R hR H q)
          (trajectory (NullAugmentation.driver D₀) β R hR s q) (U (s,q))) 2 ((parameterLaw N p).prod P) ∧
        (∫ q,(energyCorrection (p := p)
          (trajectory (NullAugmentation.driver D₀) β R hR H q)
          (trajectory (NullAugmentation.driver D₀) β R hR s q) (U (s,q)))^2 ∂(parameterLaw N p).prod P)≤
          ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β H)) := by
  have hg (i : Fin N) := exists_fixedTerminalColumn_joint_L4 hN hp D₀ β R hR hNR H (basisVector i)
  choose G hG hGV hGM using hg
  let μ := (parameterLaw N p).prod P
  let U : WaitingTime H × ((Disorder N p × State N) × Ω) → (State N →L[ℝ] State N) :=
    fun q => ∑ i : Fin N,(VariationalCoefficients.coordinate i).smulRight (G i q)
  have hU : StronglyMeasurable U := by
    have hh := Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
      (ContinuousLinearMap.smulRightL ℝ (State N) (State N) (VariationalCoefficients.coordinate i)).continuous.comp_stronglyMeasurable (hG i))
    convert hh using 1
    funext q
    ext v
    simp only [U,Finset.sum_apply,sum_apply,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.smulRightL_apply_apply]
  refine ⟨U,hU,?_,?_⟩
  · intro s q hx
    have hh := ae_all_iff.mpr (fun i : Fin N => (hGV i s q).trans
      (.of_forall (fun ω => congrArg (fun z : Lp (State N) 2 P => z ω)
        (show fixedTerminalColumn (Nat.ne_of_gt hN) D₀ β R hR hNR H (basisVector i) s q=
          physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s (H+1) (H-s) q hx (basisVector i) from
            dif_pos hx))))
    filter_upwards [hh] with ω hω
    simp only [U,sampleMatrix]
    exact Finset.sum_congr rfl (fun i _ => congrArg ((VariationalCoefficients.coordinate i).smulRight) (hω i))
  · intro s
    let hm₂ (i : Fin N) : MemLp (fun q => G i (s,q)) 2 μ := (hGM i s).1.mono_exponent (by norm_num)
    let V (i : Fin N) : Lp (State N) 2 μ := (hm₂ i).toLp (fun q => G i (s,q))
    let M : State N →L[ℝ] Lp (State N) 2 μ := ∑ i : Fin N,(VariationalCoefficients.coordinate i).smulRight (V i)
    have hMbasis (i : Fin N) : M (basisVector i)=V i := by
      simp [M,ContinuousLinearMap.smulRight_apply,basisVector,PiLp.single_apply]
    have hUae : (fun q => U (s,q))=ᵐ[μ] sampleMatrix M := by
      have hh := ae_all_iff.mpr (fun i : Fin N => (hm₂ i).coeFn_toLp)
      filter_upwards [hh] with q hq
      simp only [U,sampleMatrix,hMbasis]
      exact Finset.sum_congr rfl (fun i _ => congrArg ((VariationalCoefficients.coordinate i).smulRight) (hq i).symm)
    have hM4 (i : Fin N) : MemLp (M (basisVector i) : _ → State N) 4 μ := by
      rw [hMbasis]
      exact (memLp_congr_ae (hm₂ i).coeFn_toLp).mpr (hGM i s).1
    have hMB (i : Fin N) : (∫ q,‖(M (basisVector i)) q‖^4 ∂μ)≤annealedFourthConstant p β H := by
      rw [hMbasis,integral_congr_ae ((hm₂ i).coeFn_toLp.mono (fun q hq => congrArg (fun z : State N => ‖z‖^4) hq))]
      simpa [basisVector] using (hGM i s).2
    have htraceAE : (fun q => normalizedTrace (U (s,q)))=ᵐ[μ] sampleTrace M :=
      hUae.mono (fun q hq => (congrArg normalizedTrace hq).trans (sampleTrace_eq M q).symm)
    have htrace := sampleTrace_fourthMoment hN M (annealedFourthConstant p β H) hM4 hMB
    have herror := energyCorrection_secondMoment hN hp M (annealedFourthConstant p β H) hM4 hMB
      (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR H).aestronglyMeasurable
      (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR s).aestronglyMeasurable
      (trajectory_onSphere hN D₀ β R hR hNR H) (trajectory_onSphere hN D₀ β R hR hNR s)
    have herrorAE : (fun q => energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR H q)
        (trajectory (NullAugmentation.driver D₀) β R hR s q) (U (s,q)))=ᵐ[μ]
      (fun q => energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR H q)
        (trajectory (NullAugmentation.driver D₀) β R hR s q) (sampleMatrix M q)) :=
      hUae.mono (fun q hq => congrArg (energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR H q)
        (trajectory (NullAugmentation.driver D₀) β R hR s q)) hq)
    refine ⟨(memLp_congr_ae htraceAE).mpr (sampleTrace_memLp_fourth M hM4),?_,
      (memLp_congr_ae herrorAE).mpr herror.1,?_⟩
    · rw [integral_congr_ae (htraceAE.mono (fun q hq => congrArg (fun z : ℝ => |z|^4) hq))]
      exact htrace.2
    · rw [integral_congr_ae (herrorAE.mono (fun q hq => congrArg (fun z : ℝ => z^2) hq))]
      exact herror.2

end SphericalAging.AnnealedResponseTimeMatrix
