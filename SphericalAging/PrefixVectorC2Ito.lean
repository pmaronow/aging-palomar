module

public import SphericalAging.PrefixVectorCovariation
public import SphericalAging.MultivariateItoWeights
public import SphericalAging.LinearSDELocalization

public section

/-! Genuine C² multivariate Itô formula for a continuous adapted vector
with arbitrary predictable drift/noise rows and bounded observable derivative. All stochastic integrands are constructed predictable L² classes
and identified with the physical derivative/noise evaluations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.PrefixVectorC2Ito
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open VectorIto VectorItoFormula WeightedItoSums WeightedDriftSums AnnealedSDECore
open MultivariateTaylor MultivariateTaylorPartition MultivariateItoSums MultivariateItoWeights SDEWeightedLinear
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual C² Itô formula for arbitrary time-dependent predictable
coefficient rows. The observable has bounded first derivative; the process
itself need not be bounded. No bracket or Itô conclusion is a premise. -/
theorem prefix_C2_ito_formula (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T : ℝ≥0)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω))
    (hsigma : ∀ᵐ ω ∂P,∀ i j,Continuous (fun s => sigma i j s ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f)
    (K : Fin N → ℝ≥0) (hK : ∀ i x,‖fderiv ℝ f x (basisVector i)‖≤K i) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (∀ i j,(V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
        FourPapersCommon.continuousAdaptedTimeCut
          (fun s ω => fderiv ℝ f (X s ω) (basisVector i)*sigma i j s ω) T) ∧
      ∀ᵐ ω ∂P,f (X T ω)=f (Z0 ω)+
        (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          fderiv ℝ f (X s ω) (basisVector i)*cutRepresentative (A i) T (s,ω) ∂nonnegativeLebesgueMeasure)+
        (∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω)+
        (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          Hessian f (X s ω) (basisVector i) (basisVector k)*
            (∑ j : Fin N,sigma i j s ω*sigma k j s ω) ∂nonnegativeLebesgueMeasure) := by
  let H (i : Fin N) : ℝ≥0 → Ω → ℝ := fun s ω => fderiv ℝ f (X s ω) (basisVector i)
  have hWa (i : Fin N) : StronglyAdapted F (H i) := fun s =>
    (derivative_basis_continuous hf i).comp_stronglyMeasurable (hXa s)
  have hWc (i : Fin N) : ∀ᵐ ω ∂P,Continuous (fun s => H i s ω) :=
    hXc.mono (fun _ h => (derivative_basis_continuous hf i).comp h)
  let V (i j : Fin N) : PredictableProcessL2 F P :=
    weightedIntegrand (H i) (hWa i) (hWc i) (K i) (fun s ω => hK i (X s ω)) T (U i j)
  have hV (i j : Fin N) : (V i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      fun q => FourPapersCommon.continuousAdaptedTimeCut (H i) T q*(U i j : TimeProcessL2 P) q := by
    exact predictableProduct_coe
      (FourPapersCommon.aestronglyMeasurable_aeContinuousAdaptedTimeCut F (H i) (hWa i) (hWc i) T)
      (K i) (.of_forall (timeCut_bound (H i) (K i) (fun s ω => hK i (X s ω)) T)) (U i j)
  refine ⟨V,?_,?_⟩
  · intro i j
    filter_upwards [hV i j,hU i j] with q hv hu
    rw [hv,hu]
    simp only [FourPapersCommon.continuousAdaptedTimeCut,H]
    split_ifs <;> simp
  · have hlin (i : Fin N) := prefix_weightedLeftSum_tendsto D (A i) (U i) T T le_rfl
      (fun s ω => X s ω i) (H i) (fun ω => Z0 ω i) (fun s hs => hprefix s hs i)
      (hWa i) (hWc i) (K i) (fun s ω => hK i (X s ω))
    have hsum := tendstoInMeasure_finsetSum Finset.univ _ _ (fun i _ => hlin i)
    have hlinear : TendstoInMeasure P (fun n => linearApprox f X T (n+1)) atTop
        (fun ω => (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          fderiv ℝ f (X s ω) (basisVector i)*cutRepresentative (A i) T (s,ω) ∂nonnegativeLebesgueMeasure)+
          ∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω) := by
      apply hsum.congr
      · intro n
        exact .of_forall (fun ω => by
          dsimp only
          unfold linearApprox weightedLeftSum
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro l _
          rw [← state_sum_basis (X (uniformPartitionTime T (n+1) (l+1)) ω-X (uniformPartitionTime T (n+1) l) ω)]
          simp only [map_sum,map_smul,smul_eq_mul,PiLp.sub_apply,H]
          exact Finset.sum_congr rfl (fun i _ => by ring))
      · exact .of_forall (fun ω => Finset.sum_add_distrib)
    have hXm (s : ℝ≥0) : AEStronglyMeasurable (X s) P := ((hXa s).mono (F.le s)).aestronglyMeasurable
    have hquad := PrefixVectorCovariation.prefix_quadratic_tendsto D A U X Z0 sigma T T le_rfl
      hprefix hU hXm hXc hsigma hf
    have hrem := PrefixVectorCovariation.prefix_remainder_tendsto D A U X Z0 sigma T T le_rfl
      hprefix hU hXm hXc hf
    have htotal := (hlinear.add_real_noMeas hquad).add_real_noMeas hrem
    have hactual : TendstoInMeasure P
        (fun _ : ℕ => fun ω => f (X T ω)-f (X 0 ω)) atTop
        (fun ω => (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
          fderiv ℝ f (X s ω) (basisVector i)*cutRepresentative (A i) T (s,ω) ∂nonnegativeLebesgueMeasure)+
          (∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω)+
          (1/2 : ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) T,
            Hessian f (X s ω) (basisVector i) (basisVector k)*
              (∑ j : Fin N,sigma i j s ω*sigma k j s ω) ∂nonnegativeLebesgueMeasure)) := by
      apply htotal.congr
      · intro n
        exact .of_forall (fun ω => (partition_identity f X T (n+1) (Nat.zero_lt_succ n) ω).symm)
      · exact .of_forall (fun _ => add_zero _)
    have hc : TendstoInMeasure P (fun _ : ℕ => fun ω => f (X T ω)-f (X 0 ω)) atTop
        (fun ω => f (X T ω)-f (X 0 ω)) :=
      tendstoInMeasure_of_tendsto_ae (fun _ => (hf.continuous.comp_aestronglyMeasurable
        (((hXa T).mono (F.le T)).aestronglyMeasurable)).sub
          (hf.continuous.comp_aestronglyMeasurable (((hXa 0).mono (F.le 0)).aestronglyMeasurable)))
        (.of_forall (fun _ => tendsto_const_nhds))
    have hz : X 0=ᵐ[P] Z0 := by
      have hall := ae_all_iff.mpr (fun i : Fin N => hprefix 0 bot_le i)
      have hi : ∀ᵐ ω ∂P,∀ i : Fin N,vectorProcess D (U i) 0 ω=0 :=
        ae_all_iff.mpr (fun i => by
          have hlp := vectorProcessLp_ae_eq D (U i) 0
          rw [LinearSDELocalization.vectorProcessLp_zero_time] at hlp
          exact hlp.symm.trans (Lp.coeFn_zero ℝ 2 P))
      filter_upwards [hall,hi] with ω hω hiω
      apply PiLp.ext
      intro i
      have he := hω i
      simp only [driftVersion,primitive,Measure.restrict_empty,integral_zero_measure,Ioc_self,
        add_zero,hiω i] at he
      exact he
    filter_upwards [tendstoInMeasure_ae_unique hc hactual,hz] with ω he hzω
    rw [hzω] at he
    linarith

end SphericalAging.PrefixVectorC2Ito
