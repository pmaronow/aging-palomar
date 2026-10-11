module

public import SphericalAging.RandomInitialAffineRadialMoment

public section

/-! First-moment comparison for genuine scalar integral equations with
integrable drift and observable, without a bounded-state requirement.
The stochastic integral has zero expectation by its constructed Itô law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.IntegrableScalarSDEComparison
open HardSphereDynamics PredictableDriftTime VectorIto SharpRadialMoment LinearSDEFourthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem firstMoment_le (D : BrownianDriver N P F) (T M c : ℝ≥0)
    (Z : ℝ≥0 → Ω → ℝ) (z0 : Ω → ℝ) (G : ℝ≥0 × Ω → ℝ)
    (hz0 : Integrable z0 P) (hZi : ∀ s,s≤T → Integrable (Z s) P)
    (hZtime : ∀ s,s≤T → Integrable (FourPapersCommon.continuousAdaptedTimeCut Z s)
      (nonnegativeLebesgueMeasure.prod P))
    (hGi : Integrable G (nonnegativeLebesgueMeasure.prod P))
    (hbound : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,q.1∈Ioc 0 T →
      G q≤(M:ℝ)*Z q.1 q.2+c)
    (heq : ∀ s,s≤T → ∃ U : Fin N → PredictableProcessL2 F P,
      Z s=ᵐ[P] fun ω => z0 ω+(∫ r in Ioc (0 : ℝ≥0) s,G (r,ω) ∂nonnegativeLebesgueMeasure)+
        (vectorProcessLp D U s : Ω → ℝ) ω)
    (t : ℝ≥0) (ht : t≤T) :
    (∫ ω,Z t ω ∂P)≤((∫ ω,z0 ω ∂P)+(c:ℝ)*T)*Real.exp ((M:ℝ)*t) := by
  let g : ℝ≥0 → ℝ := fun s => ∫ ω,G (s,ω) ∂P
  have hgi : Integrable g nonnegativeLebesgueMeasure := hGi.integral_prod_left
  have hGrestrict (s : ℝ≥0) : Integrable G
      ((nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) s)).prod P) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hGi.restrict
  have hswap (s : ℝ≥0) : (∫ ω,∫ r in Ioc (0 : ℝ≥0) s,G (r,ω) ∂nonnegativeLebesgueMeasure ∂P)=
      primitive (fun q : ℝ≥0 × Unit => g q.1) s () := by
    exact (integral_integral_swap (f:=fun r ω => G (r,ω)) (hGrestrict s)).symm
  have hmean (s : ℝ≥0) (hs : s≤T) : (∫ ω,Z s ω ∂P)=
      (∫ ω,z0 ω ∂P)+primitive (fun q : ℝ≥0 × Unit => g q.1) s () := by
    obtain ⟨U,hU⟩ := heq s hs
    have hAi := (hGrestrict s).integral_prod_right
    have hUi := (Lp.memLp (vectorProcessLp D U s)).integrable (by norm_num)
    rw [integral_congr_ae hU]
    have h1 := integral_add (hz0.add hAi) hUi
    have h2 := integral_add hz0 hAi
    simp only [Pi.add_apply] at h1 h2
    rw [h1,h2,vectorProcessLp_expectation_zero,hswap]
    simp
  let f : ℝ → ℝ := fun r => (∫ ω,z0 ω ∂P)+primitive (fun q : ℝ≥0 × Unit => g q.1) r.toNNReal ()
  have hfc : Continuous f := continuous_const.add
    ((primitive_continuous (fun q : ℝ≥0 × Unit => g q.1) () hgi).comp continuous_real_toNNReal)
  have hfe (s : ℝ≥0) (hs : s≤T) : f s=∫ ω,Z s ω ∂P := by
    simpa only [f,Real.toNNReal_coe] using (hmean s hs).symm
  have hb (s : ℝ≥0) (hs : s≤T) : (∫ ω,Z s ω ∂P)≤
      ((∫ ω,z0 ω ∂P)+(c:ℝ)*T)+
        (M:ℝ)*∫ r in Ioc (0 : ℝ≥0) s,(∫ ω,Z r ω ∂P) ∂nonnegativeLebesgueMeasure := by
    rw [hmean s hs]
    have hcut := hZtime s hs
    have hGcut : Integrable ((Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω)).indicator G)
        (nonnegativeLebesgueMeasure.prod P) := hGi.indicator (measurableSet_Ioc.prod MeasurableSet.univ)
    have hconst : Integrable ((Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω)).indicator (fun _ => (c:ℝ)))
        (nonnegativeLebesgueMeasure.prod P) :=
      memLp_one_iff_integrable.mp (memLp_indicator_const _ (measurableSet_Ioc.prod MeasurableSet.univ)
        (c:ℝ) (Or.inr (FourPapersCommon.finiteMeasure_time_rectangle s)))
    have hmono : (∫ q,(Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω)).indicator G q
        ∂nonnegativeLebesgueMeasure.prod P)≤
        ∫ q,(M:ℝ)*FourPapersCommon.continuousAdaptedTimeCut Z s q+
          (Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω)).indicator (fun _ => (c:ℝ)) q
          ∂nonnegativeLebesgueMeasure.prod P := by
      apply integral_mono_ae hGcut ((hcut.const_mul _).add hconst)
      filter_upwards [hbound] with q hq
      by_cases hqs : q.1∈Ioc (0 : ℝ≥0) s
      · simp only [indicator_of_mem (show q∈Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω) from ⟨hqs,mem_univ _⟩),
          FourPapersCommon.continuousAdaptedTimeCut,Pi.add_apply,hqs,ite_true]
        exact hq ⟨hqs.1,hqs.2.trans hs⟩
      · have hqn : q∉Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω) := fun h => hqs h.1
        simp only [indicator_of_notMem hqn,FourPapersCommon.continuousAdaptedTimeCut,hqs,
          Pi.add_apply,ite_false,mul_zero,zero_add,le_refl]
    have hGlhs : (∫ q,(Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω)).indicator G q
        ∂nonnegativeLebesgueMeasure.prod P)=primitive (fun q : ℝ≥0 × Unit => g q.1) s () := by
      rw [integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ),← Measure.restrict_prod_eq_prod_univ,
        integral_prod _ (hGrestrict s)]
      rfl
    have hZrhs : (∫ q,(M:ℝ)*FourPapersCommon.continuousAdaptedTimeCut Z s q
        ∂nonnegativeLebesgueMeasure.prod P)=
        (M:ℝ)*∫ r in Ioc (0 : ℝ≥0) s,(∫ ω,Z r ω ∂P) ∂nonnegativeLebesgueMeasure := by
      rw [integral_const_mul,integral_prod _ hcut,← integral_indicator measurableSet_Ioc]
      congr 1
      apply integral_congr_ae
      exact .of_forall (fun r => by by_cases hr : r∈Ioc (0 : ℝ≥0) s <;>
        simp [FourPapersCommon.continuousAdaptedTimeCut,hr])
    have hCrhs : (∫ q,(Ioc (0 : ℝ≥0) s ×ˢ (univ : Set Ω)).indicator (fun _ => (c:ℝ)) q
        ∂nonnegativeLebesgueMeasure.prod P)=(c:ℝ)*s := by
      rw [integral_indicator (measurableSet_Ioc.prod MeasurableSet.univ)]
      simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,mul_comm]
    rw [hGlhs,integral_add (hcut.const_mul _) hconst,hZrhs,hCrhs] at hmono
    have hcs : (c:ℝ)*s≤(c:ℝ)*T := mul_le_mul_of_nonneg_left hs c.coe_nonneg
    linarith only [hmono,hcs]
  have hgr := integral_gronwall_bound f ((∫ ω,z0 ω ∂P)+(c:ℝ)*T) M T M.coe_nonneg hfc (by
    intro r hr
    have hrs : r.toNNReal≤T := by
      simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2
    have hh := hb r.toNNReal hrs
    have he : (∫ s in Ioc (0 : ℝ≥0) r.toNNReal,(∫ ω,Z s ω ∂P) ∂nonnegativeLebesgueMeasure)=
        ∫ s in (0 : ℝ)..r,f s := by
      have hp := primitive_eq_real_intervalIntegral (fun q : ℝ≥0 × Unit => f q.1) r.toNNReal ()
      rw [Real.coe_toNNReal r hr.1] at hp
      calc
        _ = primitive (fun q : ℝ≥0 × Unit => f q.1) r.toNNReal () := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact (hfe s (hs.2.trans hrs)).symm
        _ = ∫ s in (0 : ℝ)..r,f (s.toNNReal : ℝ) := hp
        _ = _ := by
          congr 1
          funext s
          simp only [f,Real.toNNReal_coe]
    rw [he,← hfe r.toNNReal hrs] at hh
    simpa only [Real.coe_toNNReal r hr.1,Real.toNNReal_coe] using hh)
  rw [← hfe t ht]
  simpa only [Real.toNNReal_coe] using hgr t ⟨t.coe_nonneg,ht⟩

end SphericalAging.IntegrableScalarSDEComparison
