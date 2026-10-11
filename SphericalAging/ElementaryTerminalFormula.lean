module

public import SphericalAging.WholeVectorTerminalEnergy

public section

/-! Literal stopped-interval formulas for the genuine elementary drift
and full-filtration Itô terminal operators. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ElementaryTerminalFormula
open HardSphereDynamics PredictableDriftTime TerminalLinearity
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem primitive_interval (a b t : ℝ≥0) (c : ℝ) (hab : a≤b) :
    (∫ s in Ioc (0:ℝ≥0) t,(Ioc a b).indicator (fun _ => c) s ∂nonnegativeLebesgueMeasure)=
      ((min t b:ℝ)-(min t a:ℝ))*c := by
  rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc]
  rw [Set.Ioc_inter_Ioc]
  simp only [max_eq_left (show (0:ℝ≥0)≤a from bot_le)]
  by_cases hat : a≤t
  · have ha : a≤min t b := le_min hat hab
    rw [min_eq_right (show (a:ℝ)≤t from hat)]
    simp only [integral_const,Measure.restrict_apply_univ,smul_eq_mul,Measure.real_def,
      nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal]
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr (show (a:ℝ)≤min b t from le_min hab hat))]
    simp only [NNReal.coe_min,min_comm]
  · have hta : t≤a := (lt_of_not_ge hat).le
    have he : Ioc a (min b t)=∅ := Set.Ioc_eq_empty (not_lt_of_ge ((min_le_right b t).trans hta))
    rw [he,Measure.restrict_empty,integral_zero_measure,min_eq_left (show (t:ℝ)≤a from hta)]
    have htb : t≤b := hta.trans hab
    simp only [min_eq_left (show (t:ℝ)≤b from htb),sub_self,zero_mul]

theorem driftVersion_elementary (a b T : ℝ≥0) (hab : a≤b) (hbT : b≤T)
    (Z : lpMeas ℝ ℝ (F a) 2 P) :
    ∀ᵐ omega ∂P,∀t : ℝ≥0,driftVersion (elementaryPredictable F a b Z) T t omega=
      ((min t b:ℝ)-(min t a:ℝ))*(Z : Ω→ℝ) omega := by
  let U := elementaryPredictable F a b Z
  have hc : cutRepresentative U T=ᵐ[nonnegativeLebesgueMeasure.prod P]
      elementaryRepresentative F a b (Z : Ω→ℝ) := by
    filter_upwards [representative_ae U,elementaryPredictable_coeFn F a b Z] with q hr he
    unfold cutRepresentative FourPapersCommon.FilteredBrownian.predictableTimeFrame
    by_cases hq : q.1∈Ioc a b
    · have hT : q∈Ioc (0:ℝ≥0) T×ˢ(univ:Set Ω) :=
        ⟨⟨lt_of_le_of_lt (show (0:ℝ≥0)≤a from bot_le) hq.1,hq.2.trans hbT⟩,mem_univ _⟩
      rw [indicator_of_mem hT,hr]
      exact he
    · by_cases hT : q∈Ioc (0:ℝ≥0) T×ˢ(univ:Set Ω)
      · rw [indicator_of_mem hT,hr]
        exact he
      · simp only [indicator_of_notMem hT,elementaryRepresentative,hq,ite_false]
  have hswap := Measure.measurePreserving_swap.quasiMeasurePreserving.ae hc
  filter_upwards [Measure.ae_ae_of_ae_prod hswap] with omega homega
  intro t
  unfold driftVersion primitive
  have he : (∫ s in Ioc (0:ℝ≥0) t,cutRepresentative U T (s,omega) ∂nonnegativeLebesgueMeasure)=
      ∫ s in Ioc (0:ℝ≥0) t,(Ioc a b).indicator (fun _ => (Z : Ω→ℝ) omega) s ∂nonnegativeLebesgueMeasure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae homega] with s hs
    simpa only [elementaryRepresentative,Prod.swap_prod_mk,Set.indicator,mem_Ioc] using hs
  rw [he,primitive_interval a b t _ hab]

theorem driftTerminal_elementary_ae (a b T t : ℝ≥0) (hab : a≤b) (hbT : b≤T)
    (Z : lpMeas ℝ ℝ (F a) 2 P) :
    (driftTerminalOperator T t (elementaryPredictable F a b Z) : Ω→ℝ)=ᵐ[P]
      fun omega => ((min t b:ℝ)-(min t a:ℝ))*(Z : Ω→ℝ) omega :=
  (driftVersion_memLp (elementaryPredictable F a b Z) T t).coeFn_toLp.trans
    ((driftVersion_elementary a b T hab hbT Z).mono (fun _ h => h t))

theorem itoTerminal_elementary_ae (D : BrownianDriver N P F) (j : Fin N)
    (a b t : ℝ≥0) (hab : a≤b) (Z : lpMeas ℝ ℝ (F a) 2 P) :
    (itoTerminalOperator D j t (elementaryPredictable F a b Z) : Ω→ℝ)=ᵐ[P]
      fun omega => (Z : Ω→ℝ) omega*
        (D.coordinate j (min t b) omega-D.coordinate j (min t a) omega) := by
  exact (naturalItoProcess_ae_eq_representative (D.brownian j).toIsPreBrownianReal
    (D.coordinateStronglyMeasurable j) (D.filtered j) _ t).trans
    (naturalItoProcessRepresentative_elementaryPredictable_ae_eq (D.brownian j).toIsPreBrownianReal
      (D.coordinateStronglyMeasurable j) (D.filtered j) hab Z t)
end SphericalAging.ElementaryTerminalFormula
