module

public import SphericalAging.PrefixVectorC2Generator
public import SphericalAging.PrefixVectorC2ItoAt

public section

/-! A faithful scalar C² integral equation with the genuine jointly
integrable generator and constructed zero-mean vector Itô integrals. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.PrefixVectorC2Representation
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime VectorIto
open MultivariateTaylor PrefixVectorC2Generator
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem scalar_representation (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (U : Fin N → Fin N → PredictableProcessL2 F P)
    (X : ℝ≥0 → Ω → State N) (Z0 : Ω → State N)
    (sigma : Fin N → Fin N → ℝ≥0 → Ω → ℝ) (T t : ℝ≥0) (ht : t≤T)
    (hprefix : ∀ s,s≤T → ∀ i : Fin N,(fun ω => X s ω i)=ᵐ[P]
      fun ω => Z0 ω i+driftVersion (A i) T s ω+vectorProcess D (U i) s ω)
    (hU : ∀ i j,(U i j : ℝ≥0 × Ω → ℝ)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T)
    (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω))
    (hsigma : ∀ᵐ ω ∂P,∀ i j,Continuous (fun s => sigma i j s ω))
    {f : State N → ℝ} (hf : ContDiff ℝ 2 f) (K L : ℝ≥0)
    (hK : ∀ i x,‖fderiv ℝ f x (basisVector i)‖≤K)
    (hL : ∀ i k x,‖Hessian f x (basisVector i) (basisVector k)‖≤L) :
    ∃ V : Fin N → Fin N → PredictableProcessL2 F P,
      (fun ω => f (X t ω))=ᵐ[P] fun ω => f (Z0 ω)+
        (∫ s in Ioc (0 : ℝ≥0) t,generator f X T A U (s,ω) ∂nonnegativeLebesgueMeasure)+
        (∑ i : Fin N,(vectorIto D (V i) : Ω → ℝ) ω) := by
  obtain ⟨V,hV,hEq⟩ := PrefixVectorC2ItoAt.prefix_C2_ito_formula_at D A U X Z0 sigma T t ht
    hprefix hU hXa hXc hsigma hf (fun _ => K) hK
  refine ⟨V,?_⟩
  obtain ⟨hDi,hHi⟩ := components_integrable hf X hXa hXc T A U K L hK hL
  have hDip := ae_all_iff.mpr (fun i => (hDi i).prod_left_ae)
  have hHip := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun k => (hHi i k).prod_left_ae))
  have hUp := ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hU i j))
  have hUswap := (Measure.measurePreserving_swap (μ:=P) (ν:=nonnegativeLebesgueMeasure)).quasiMeasurePreserving.ae hUp
  filter_upwards [hEq,hDip,hHip,Measure.ae_ae_of_ae_prod hUswap] with ω he hdi hhi hu
  have hgen : (∫ s in Ioc (0 : ℝ≥0) t,generator f X T A U (s,ω) ∂nonnegativeLebesgueMeasure)=
      (∑ i : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        fderiv ℝ f (X s ω) (basisVector i)*cutRepresentative (A i) T (s,ω) ∂nonnegativeLebesgueMeasure)+
      (1/2:ℝ)*(∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        Hessian f (X s ω) (basisVector i) (basisVector k)*
          (∑ j : Fin N,sigma i j s ω*sigma k j s ω) ∂nonnegativeLebesgueMeasure) := by
    have hd := integrable_finsetSum Finset.univ (fun i _ => (hdi i).integrableOn (s:=Ioc (0 : ℝ≥0) t))
    have hh := integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun k _ => (hhi i k).integrableOn (s:=Ioc (0 : ℝ≥0) t)))
    simp only [generator]
    rw [integral_add hd (hh.const_mul (1/2:ℝ)),integral_const_mul,
      integral_finsetSum Finset.univ (fun i _ => (hdi i).integrableOn (s:=Ioc (0 : ℝ≥0) t)),
      integral_finsetSum Finset.univ (fun i _ =>
        integrable_finsetSum Finset.univ (fun k _ => (hhi i k).integrableOn (s:=Ioc (0 : ℝ≥0) t)))]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      simp only [derivativeCut,FourPapersCommon.continuousAdaptedTimeCut,
        ite_eq_left (show s∈Ioc (0 : ℝ≥0) T from ⟨hs.1,hs.2.trans ht⟩)]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finsetSum Finset.univ (fun k _ => (hhi i k).integrableOn (s:=Ioc (0 : ℝ≥0) t))]
      apply Finset.sum_congr rfl
      intro k _
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hu,ae_restrict_mem measurableSet_Ioc] with s hus hs
      have hsT : s∈Ioc (0 : ℝ≥0) T := ⟨hs.1,hs.2.trans ht⟩
      simp only [hessianCut,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hsT]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      have hi := hus i j
      have hk := hus k j
      simp only [Function.comp_def,Prod.swap,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left hsT] at hi hk
      rw [hi,hk]
  rw [hgen]
  linarith only [he]

end SphericalAging.PrefixVectorC2Representation
