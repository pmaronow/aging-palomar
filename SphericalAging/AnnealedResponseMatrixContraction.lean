module

public import SphericalAging.AnnealedTwoTimeResponseMoments

public section

/-! A genuine jointly measurable two-time sample response matrix under
the full disorder × sphere initial-state × Brownian law. Its columns
represent the actual projected response, and its normalized trace and
rank-one energy correction have dimension-uniform moment bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedResponseMatrixContraction
open HardSphereDynamics FiniteModel TwoTimeResponseParameter
open ResponseMatrixEnergyContraction AnnealedTwoTimeResponseMoments EnergyCovarianceContraction
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def annealedFourthConstant (p : ℕ) (β : ℝ≥0) (t : ℝ≥0) : ℝ :=
  Real.exp (54*(t : ℝ))*GaussianLandscapeMoments.momentCeiling p
    (4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ))

@[expose] def trajectory (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (t : ℝ≥0) (q : (Disorder N p × State N) × Ω) : State N :=
  ActualSphereTransition.jointProcess D β R hR q.1 t q.2

lemma trajectory_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) :
    StronglyMeasurable (trajectory (p := p) D β R hR t) := by
  exact (ActualSphereTransition.jointProcess_measurable D β R hR).comp_measurable
    (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))

lemma trajectory_onSphere (hN : 0<N) (D₀ : BrownianDriver N P F) (β : ℝ)
    (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t : ℝ≥0) :
    ∀ᵐ q ∂(parameterLaw N p).prod P,OnSphere (trajectory (NullAugmentation.driver D₀) β R hR t q) := by
  apply (Measure.ae_prod_iff_ae_ae ?_).mpr
  · filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    exact (ActualSphereTransition.jointProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hq).mono
      (fun _ h => h t)
  · exact ((trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR t).inner
      (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR t)).measurableSet_eq_fun
        stronglyMeasurable_const

/-- The matrix is built from actual response columns and represents the
physical projected matrix in every sphere initial-state slice. The
annealed normalized trace has a true L⁴ bound and the actual rank-one
energy error has an L² bound of order 1/N. No sample operator bound is
assumed. -/
theorem exists_actual_annealed_matrix (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T) :
    ∃ U : (Disorder N p × State N) × Ω → (State N →L[ℝ] State N),StronglyMeasurable U ∧
      (∀ q (hx : OnSphere q.2),(fun ω => U (q,ω)) =ᵐ[P]
        sampleMatrix (physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s T t q hx)) ∧
      MemLp (fun q => normalizedTrace (U q)) 4 ((parameterLaw N p).prod P) ∧
      (∫ q,|normalizedTrace (U q)|^4 ∂(parameterLaw N p).prod P)≤annealedFourthConstant p β t ∧
      MemLp (fun q => energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
        (trajectory (NullAugmentation.driver D₀) β R hR s q) (U q)) 2 ((parameterLaw N p).prod P) ∧
      (∫ q,(energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
        (trajectory (NullAugmentation.driver D₀) β R hR s q) (U q))^2 ∂(parameterLaw N p).prod P)≤
        ((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β t) ∧
      (∫ q,|energyCorrection (p := p)
        (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
        (trajectory (NullAugmentation.driver D₀) β R hR s q) (U q)| ∂(parameterLaw N p).prod P)≤
        Real.sqrt (((p : ℝ)^2*((p : ℝ)-1)^2/(N : ℝ))*(1+annealedFourthConstant p β t)) := by
  have hg (i : Fin N) := exists_responseColumn_annealed_L4 hN hp D₀ β R hR hNR s T t ht hT (basisVector i)
  choose G hG hGV hG4 hGB using hg
  let μ := (parameterLaw N p).prod P
  let hm₂ (i : Fin N) : MemLp (G i) 2 μ := (hG4 i).mono_exponent (by norm_num)
  let V (i : Fin N) : Lp (State N) 2 μ := (hm₂ i).toLp (G i)
  let M : State N →L[ℝ] Lp (State N) 2 μ :=
    ∑ i : Fin N,(VariationalCoefficients.coordinate i).smulRight (V i)
  let U : (Disorder N p × State N) × Ω → (State N →L[ℝ] State N) :=
    fun q => ∑ i : Fin N,(VariationalCoefficients.coordinate i).smulRight (G i q)
  have hMbasis (i : Fin N) : M (basisVector i)=V i := by
    simp [M,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,basisVector,PiLp.single_apply]
  have hU : StronglyMeasurable U := by
    have hh := Finset.stronglyMeasurable_sum Finset.univ (fun i _ =>
      (ContinuousLinearMap.smulRightL ℝ (State N) (State N) (VariationalCoefficients.coordinate i)).continuous.comp_stronglyMeasurable (hG i))
    convert hh using 1
    funext q
    ext v
    simp only [U,Finset.sum_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.smulRightL_apply_apply]
  have hUae : U=ᵐ[μ] sampleMatrix M := by
    have hh := ae_all_iff.mpr (fun i : Fin N => (hm₂ i).coeFn_toLp)
    filter_upwards [hh] with q hq
    simp only [U,sampleMatrix,hMbasis]
    exact Finset.sum_congr rfl (fun i _ => congrArg ((VariationalCoefficients.coordinate i).smulRight) (hq i).symm)
  have hM4 (i : Fin N) : MemLp (M (basisVector i) : _ → State N) 4 μ := by
    rw [hMbasis]
    exact (memLp_congr_ae (hm₂ i).coeFn_toLp).mpr (hG4 i)
  have hMB (i : Fin N) : (∫ q,‖(M (basisVector i)) q‖^4 ∂μ)≤annealedFourthConstant p β t := by
    rw [hMbasis,integral_congr_ae ((hm₂ i).coeFn_toLp.mono (fun q hq => congrArg (fun z : State N => ‖z‖^4) hq))]
    simpa [basisVector,annealedFourthConstant] using hGB i
  have htraceAE : (fun q => normalizedTrace (U q))=ᵐ[μ] sampleTrace M :=
    hUae.mono (fun q hq => (congrArg normalizedTrace hq).trans (sampleTrace_eq M q).symm)
  have htrace := sampleTrace_fourthMoment hN M (annealedFourthConstant p β t) hM4 hMB
  have herror := energyCorrection_secondMoment hN hp M (annealedFourthConstant p β t) hM4 hMB
    (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR (s+t)).aestronglyMeasurable
    (trajectory_stronglyMeasurable (NullAugmentation.driver D₀) β R hR s).aestronglyMeasurable
    (trajectory_onSphere hN D₀ β R hR hNR (s+t)) (trajectory_onSphere hN D₀ β R hR hNR s)
  have herrorAE : (fun q => energyCorrection (p := p)
      (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q) (U q))=ᵐ[μ]
    (fun q => energyCorrection (p := p)
      (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q) (sampleMatrix M q)) :=
    hUae.mono (fun q hq => congrArg (energyCorrection (p := p)
      (trajectory (NullAugmentation.driver D₀) β R hR (s+t) q)
      (trajectory (NullAugmentation.driver D₀) β R hR s q)) hq)
  refine ⟨U,hU,?_,(memLp_congr_ae htraceAE).mpr (sampleTrace_memLp_fourth M hM4),?_,
    (memLp_congr_ae herrorAE).mpr herror.1,?_,?_⟩
  · intro q hx
    have hh := ae_all_iff.mpr (fun i : Fin N => (hGV i q).trans
      (.of_forall (fun ω => congrArg (fun z : Lp (State N) 2 P => z ω)
        (responseColumn_eq_physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s T t ht hT (basisVector i) q hx))))
    filter_upwards [hh] with ω hω
    simp only [U,sampleMatrix]
    exact Finset.sum_congr rfl (fun i _ => congrArg ((VariationalCoefficients.coordinate i).smulRight) (hω i))
  · rw [integral_congr_ae (htraceAE.mono (fun q hq => congrArg (fun z : ℝ => |z|^4) hq))]
    exact htrace.2
  · rw [integral_congr_ae (herrorAE.mono (fun q hq => congrArg (fun z : ℝ => z^2) hq))]
    exact herror.2
  · rw [integral_congr_ae (herrorAE.mono (fun q hq => congrArg (fun z : ℝ => |z|) hq))]
    exact (integral_abs_le_sqrt_secondMoment herror.1).trans (Real.sqrt_le_sqrt herror.2)

end SphericalAging.AnnealedResponseMatrixContraction
