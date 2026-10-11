module

public import SphericalAging.MultivariateItoSums

public section

/-! Genuine mixed brackets for vector processes represented by arbitrary
predictable drift and diffusion classes, including time-dependent physical
variation coefficients. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.PrefixVectorCovariation
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open VectorIto VectorItoFormula VectorQuadraticVariation WeightedVectorQuadratic LocalWeightedQuadratic
open AnnealedSDECore SDEWeightedCovariation MultivariateItoSums MultivariateTaylorPartition MultivariateTaylor
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem prefix_coordinate_add_weightedQuadratic_tendsto (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t≤T)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    (i k : Fin N) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedQuadraticSum H (fun s ω => X s ω i+X s ω k) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,(sigma i j s ω+sigma k j s ω)^2) ∂nonnegativeLebesgueMeasure) := by
  apply prefix_weightedQuadratic_tendsto D (A i+A k) (fun j => U i j+U k j) T t ht
    (fun s ω => X s ω i+X s ω k) H (fun ω => Z0 ω i+Z0 ω k)
    (fun j s ω => sigma i j s ω+sigma k j s ω)
  · intro s hs
    filter_upwards [hprefix s hs i,hprefix s hs k,
      driftVersion_add_ae (A i) (A k) T,vectorProcess_add_ae D (U i) (U k) s]
      with ω hi hk hd hu
    rw [hd s,hu,hi,hk]
    ring
  · intro j
    filter_upwards [hU i j,hU k j,Lp.coeFn_add (U i j).val (U k j).val] with q hi hk ha
    have ha' : ((U i j+U k j : PredictableProcessL2 F P) : TimeProcessL2 P) q =
        (U i j : TimeProcessL2 P) q+(U k j : TimeProcessL2 P) q := by
      simpa only [Submodule.coe_add,Pi.add_apply] using ha
    rw [ha',hi,hk]
    simp only [FourPapersCommon.continuousAdaptedTimeCut]
    split_ifs <;> simp
  · exact hH
  · exact hHc

theorem prefix_coordinate_weightedCovariation_tendsto (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t≤T)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    (hsigma : ∀ᵐ ω ∂P,∀ i j,Continuous (fun s => sigma i j s ω))
    (i k : Fin N) (H : ℝ≥0 → Ω → ℝ)
    (hH : ∀ s,AEStronglyMeasurable (H s) P)
    (hHc : ∀ᵐ ω ∂P,Continuous (fun s => H s ω)) :
    TendstoInMeasure P (fun n => weightedCovariationSum H (fun s ω => X s ω i)
      (fun s ω => X s ω k) t (n+1)) atTop
      (fun ω => ∫ s in Ioc (0 : ℝ≥0) t,H s ω*
        (∑ j : Fin N,sigma i j s ω*sigma k j s ω) ∂nonnegativeLebesgueMeasure) := by
  have ha := prefix_coordinate_add_weightedQuadratic_tendsto D A U X Z0 sigma T t ht hprefix hU i k H hH hHc
  have hi := prefix_weightedQuadratic_tendsto D (A i) (U i) T t ht (fun s ω => X s ω i) H (fun ω => Z0 ω i) (sigma i) (fun s hs => hprefix s hs i) (hU i) hH hHc
  have hk := prefix_weightedQuadratic_tendsto D (A k) (U k) T t ht (fun s ω => X s ω k) H (fun ω => Z0 ω k) (sigma k) (fun s hs => hprefix s hs k) (hU k) hH hHc
  apply (((ha.sub_real_noMeas hi).sub_real_noMeas hk).const_mul_real_noMeas (1/2 : ℝ)).congr
  · intro n
    exact .of_forall (fun ω => by
      unfold weightedCovariationSum weightedQuadraticSum
      simp only [Finset.sum_sub_distrib,Finset.mul_sum]
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring)
  · filter_upwards [hsigma,hHc] with ω hsc hhc
    have hc (a : Fin N) (j : Fin N) : Continuous (fun s => sigma a j s ω) := hsc a j
    have hint (g : ℝ≥0 → ℝ) (hg : Continuous g) :
        IntegrableOn g (Ioc (0 : ℝ≥0) t) nonnegativeLebesgueMeasure :=
      (hg.continuousOn.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self
    have hia := hint _ (hhc.mul (continuous_finsetSum Finset.univ (fun j _ => ((hc i j).add (hc k j)).pow 2)))
    have hii := hint _ (hhc.mul (continuous_finsetSum Finset.univ (fun j _ => (hc i j).pow 2)))
    have hik := hint _ (hhc.mul (continuous_finsetSum Finset.univ (fun j _ => (hc k j).pow 2)))
    simp only [Pi.mul_apply,Pi.add_apply,Pi.pow_apply] at hia hii hik
    have hfirst := integral_sub hia hii
    have hsecond := integral_sub (hia.sub hii) hik
    simp only [Pi.mul_apply,Pi.sub_apply] at hfirst hsecond
    rw [← hfirst,← hsecond,← integral_const_mul]
    apply integral_congr_ae
    exact .of_forall (fun s => by
      simp only [Finset.mul_sum]
      rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring)


theorem prefix_normQuadratic_tendsto (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t≤T)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    : TendstoInMeasure P (fun n => normQuadraticApprox X t (n+1)) atTop
      (fun ω => ∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        (∑ j : Fin N,sigma i j s ω^2) ∂nonnegativeLebesgueMeasure) := by
  have hi := tendstoInMeasure_finsetSum Finset.univ
    (fun i n => weightedQuadraticSum (fun _ _ => 1) (fun s ω => X s ω i) t (n+1))
    (fun i ω => ∫ s in Ioc (0 : ℝ≥0) t,(∑ j : Fin N,sigma i j s ω^2) ∂nonnegativeLebesgueMeasure)
    (fun i _ => by simpa only [one_mul] using
      (prefix_weightedQuadratic_tendsto D (A i) (U i) T t ht (fun s ω => X s ω i)
        (fun _ _ => 1) (fun ω => Z0 ω i) (sigma i)
        (fun s hs => hprefix s hs i) (hU i)
        (fun _ => aestronglyMeasurable_const) (.of_forall (fun _ => continuous_const))))
  exact hi.congr_left (fun n => .of_forall (fun ω => (normQuadraticApprox_coordinates X t (n+1) ω).symm))

theorem prefix_remainder_tendsto (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t≤T)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    (hXm : ∀ s,AEStronglyMeasurable (X s) P)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    TendstoInMeasure P (fun n => remainderApprox f X t (n+1)) atTop (fun _ => 0) := by
  apply remainder_tendstoInMeasure hf X t _ hXm
    (hXc.mono (fun _ h => h.continuousOn))
  exact prefix_normQuadratic_tendsto D A U X Z0 sigma T t ht hprefix hU

theorem prefix_quadratic_tendsto (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t≤T)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    (hXm : ∀ s,AEStronglyMeasurable (X s) P)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω))
    (hsigma : ∀ᵐ ω ∂P,∀ i j,Continuous (fun s => sigma i j s ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) :
    TendstoInMeasure P (fun n => quadraticApprox f X t (n+1)) atTop
      (fun ω => (1/2 : ℝ)*∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        Hessian f (X s ω) (basisVector i) (basisVector k)*
          (∑ j : Fin N,sigma i j s ω*sigma k j s ω) ∂nonnegativeLebesgueMeasure) := by
  have h (i k : Fin N) := prefix_coordinate_weightedCovariation_tendsto D A U X Z0 sigma T t ht
    hprefix hU hsigma i k (fun s ω => Hessian f (X s ω) (basisVector i) (basisVector k))
    (fun s => (hessian_basis_continuous hf i k).comp_aestronglyMeasurable (hXm s))
    (hXc.mono (fun _ h => (hessian_basis_continuous hf i k).comp h))
  have hsum := tendstoInMeasure_finsetSum Finset.univ _ _ (fun i _ =>
    tendstoInMeasure_finsetSum Finset.univ _ _ (fun k _ => h i k))
  apply (hsum.const_mul_real_noMeas (1/2 : ℝ)).congr_left
  intro n
  exact .of_forall (fun ω => (quadraticApprox_coordinates f X t (n+1) ω).symm)

end SphericalAging.PrefixVectorCovariation
