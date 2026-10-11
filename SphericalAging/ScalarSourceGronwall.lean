module

public import SphericalAging.RandomInitialAffineRadialMoment

public section

/-! Actual scalar expectation Grönwall with an integrable, unbounded
time-dependent source. This retains the true source integral and is the
moment foundation for higher stochastic variations. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ScalarSourceGronwall
open HardSphereDynamics PredictableDriftTime RadialUniqueness VectorIto SharpRadialMoment
  LinearSDEFourthMoment
set_option maxHeartbeats 1800000
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem scalar_equation_source_firstMoment (D : BrownianDriver N P F)
    (Z : ℝ≥0→Ω→ℝ) (hZa : StronglyAdapted F Z)
    (hZc : ∀ᵐ ω ∂ P,Continuous (fun t => Z t ω)) (L M : ℝ≥0)
    (hbound : ∀ᵐ ω ∂ P,∀t,‖Z t ω‖≤L) (T : ℝ≥0)
    (z0 : Ω→ℝ) (hz0 : Integrable z0 P)
    (G : ℝ≥0×Ω→ℝ) (hG : Integrable G (nonnegativeLebesgueMeasure.prod P))
    (hGpos : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,0≤G q)
    (A : PredictableProcessL2 F P) (U : Fin N→PredictableProcessL2 F P)
    (hA : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T→
      (A : TimeProcessL2 P) q≤(M:ℝ)*Z q.1 q.2+G q)
    (heq : ∀t,t≤T→∀ᵐ ω ∂ P,Z t ω=z0 ω+driftVersion A t t ω+
      (vectorProcessLp D U t : Ω→ℝ) ω) (t : ℝ≥0) (ht : t≤T) :
    firstMoment (P:=P) Z t≤
      ((∫ ω,z0 ω ∂ P)+(∫q,G q ∂nonnegativeLebesgueMeasure.prod P))*Real.exp ((M:ℝ)*t) := by
  have hc := firstMoment_continuous Z hZa hZc L hbound
  have hb (s : ℝ≥0) (hs : s≤T) : firstMoment (P:=P) Z s≤
      ((∫ ω,z0 ω ∂ P)+(∫q,G q ∂nonnegativeLebesgueMeasure.prod P))+
        (M:ℝ)*∫r in Ioc (0:ℝ≥0) s,firstMoment (P:=P) Z r ∂nonnegativeLebesgueMeasure := by
    have hAi := (driftVersion_memLp A s s).integrable (by norm_num)
    have hUi := (Lp.memLp (vectorProcessLp D U s)).integrable (by norm_num)
    have he : firstMoment (P:=P) Z s=(∫ ω,z0 ω ∂ P)+∫ ω,driftVersion A s s ω ∂ P := by
      unfold firstMoment
      rw [integral_congr_ae (heq s hs)]
      have h1 := integral_add (hz0.add hAi) hUi
      have h2 := integral_add hz0 hAi
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2,vectorProcessLp_expectation_zero]
      simp
    rw [he,expectation_driftVersion]
    have hcut := timeCut_integrable Z hZa hZc L hbound s
    let Q : Set (ℝ≥0×Ω) := Ioc 0 s×ˢuniv
    have hQ : MeasurableSet Q := measurableSet_Ioc.prod MeasurableSet.univ
    have hiG : Integrable (Q.indicator G) (nonnegativeLebesgueMeasure.prod P) := hG.indicator hQ
    have hmono : (∫q,cutRepresentative A s q ∂nonnegativeLebesgueMeasure.prod P)≤
        (∫q,(M:ℝ)*FourPapersCommon.continuousAdaptedTimeCut Z s q+
          Q.indicator G q ∂nonnegativeLebesgueMeasure.prod P) := by
      apply integral_mono_ae (cutRepresentative_integrable A s) ((hcut.const_mul _).add hiG)
      filter_upwards [representative_ae A,hA] with q hr ha
      by_cases hq : q.1∈Ioc (0:ℝ≥0) s
      · have hqQ : q∈Q := ⟨hq,mem_univ _⟩
        simp only [Pi.add_apply,Pi.mul_apply,Q,cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
          indicator_of_mem hqQ,FourPapersCommon.continuousAdaptedTimeCut,hq,ite_true,hr]
        exact ha ⟨hq.1,hq.2.trans hs⟩
      · have hqQ : q∉Q := fun hh => hq hh.1
        simp only [Pi.add_apply,Pi.mul_apply,Q,cutRepresentative,FourPapersCommon.FilteredBrownian.predictableTimeFrame,
          indicator_of_notMem hqQ,FourPapersCommon.continuousAdaptedTimeCut,hq,ite_false,
          mul_zero,zero_add,le_refl]
    have hGi : (∫q,Q.indicator G q ∂nonnegativeLebesgueMeasure.prod P)≤
        ∫q,G q ∂nonnegativeLebesgueMeasure.prod P := by
      apply integral_mono_ae hiG hG
      filter_upwards [hGpos] with q hq
      by_cases hh : q∈Q
      · simp only [indicator_of_mem hh,le_refl]
      · simpa only [indicator_of_notMem hh] using hq
    have hZi : (∫q,(M:ℝ)*FourPapersCommon.continuousAdaptedTimeCut Z s q
        ∂nonnegativeLebesgueMeasure.prod P)=
        (M:ℝ)*∫r in Ioc (0:ℝ≥0) s,firstMoment (P:=P) Z r ∂nonnegativeLebesgueMeasure := by
      rw [integral_const_mul,integral_prod _ hcut,←integral_indicator measurableSet_Ioc]
      congr 1
      apply integral_congr_ae
      exact .of_forall (fun r => by
        by_cases hr : r∈Ioc (0:ℝ≥0) s
        · simp [FourPapersCommon.continuousAdaptedTimeCut,hr,firstMoment]
        · simp [FourPapersCommon.continuousAdaptedTimeCut,hr])
    rw [integral_add (hcut.const_mul _) hiG,hZi] at hmono
    linarith only [hmono,hGi]
  have hf : Continuous (fun r : ℝ => firstMoment (P:=P) Z r.toNNReal) := hc.comp continuous_real_toNNReal
  have hgr := integral_gronwall_bound (fun r => firstMoment (P:=P) Z r.toNNReal)
    ((∫ ω,z0 ω ∂ P)+(∫q,G q ∂nonnegativeLebesgueMeasure.prod P)) M T M.coe_nonneg hf (by
      intro r hr
      have hrs : r.toNNReal≤T := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2
      have hh := hb r.toNNReal hrs
      have he : (∫s in Ioc (0:ℝ≥0) r.toNNReal,firstMoment (P:=P) Z s ∂nonnegativeLebesgueMeasure)=
          ∫s in (0:ℝ)..(r.toNNReal:ℝ),firstMoment (P:=P) Z s.toNNReal :=
        primitive_eq_real_intervalIntegral (fun q : ℝ≥0×Unit => firstMoment (P:=P) Z q.1) _ ()
      rw [he,Real.coe_toNNReal _ hr.1] at hh
      exact hh)
  simpa only [Real.toNNReal_coe] using hgr t ⟨t.coe_nonneg,ht⟩

end SphericalAging.ScalarSourceGronwall
