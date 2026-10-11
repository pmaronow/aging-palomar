module

public import SphericalAging.WholeVectorTerminalGronwall
public import SphericalAging.ShiftedRandomSDE

public section

/-! Whole-vector increment energy for a genuine random-coefficient SDE.
The increment class is derived from the actual integral equation. The
estimate retains the complete drift norm and noise trace without a
coordinate dimension factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomSDEIncrementEnergy
open HardSphereDynamics LocalSDE AnnealedSDECore TerminalStateRepresentation
open WholeVectorCoefficientEnergy WholeVectorTerminalGronwall
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem terminalClass_ae_increment (D : BrownianDriver N P F)
    (b : Ω → State N → State N) (σ : Ω → Fin N → Fin N → State N → ℝ)
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T t : ℝ≥0) (ht : t≤T)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun r ω => b ω (X r ω) i) T)
    (he : ∀ i,∀ᵐ ω ∂P,X t ω i=Z0 ω i+
      (∫ r in (0 : ℝ)..(t : ℝ),b ω (X r.toNNReal ω) i)+
        (VectorIto.vectorProcessLp D (S i) t : Ω → ℝ) ω) :
    terminalClass D 0 A S T t=ᵐ[P] fun ω => X t ω-Z0 ω := by
  have hd := ae_all_iff.mpr (fun i => driftVersion_eq_actual (A i) _ T (hA i))
  have hn := ae_all_iff.mpr (fun i => vectorProcessLp_ae_itoVersions D (S i) t)
  filter_upwards [terminalClass_ae D 0 A S T t,hd,hn,ae_all_iff.mpr he] with ω hc hd hn he
  rw [hc]
  calc
    _=∑ i : Fin N,((X t ω-Z0 ω) i) • basisVector i := by
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [PiLp.zero_apply,zero_add,PiLp.sub_apply]
      rw [hd i t ht,← hn i]
      linarith [he i]
    _=_ := state_sum_basis _

theorem randomStrongSolution_increment_energy (D : BrownianDriver N P F)
    (b : Ω → State N → State N) (σ : Ω → Fin N → Fin N → State N → ℝ)
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D (fun ω i x => b ω x i) σ Z0 X T)
    (t : ℝ≥0) (ht : t≤T) :
    MemLp (fun ω => X t ω-Z0 ω) 2 P ∧
      (∫ ω,‖X t ω-Z0 ω‖^2 ∂P)≤
        2*(t : ℝ)*(∫ r in Ioc (0 : ℝ≥0) t,∫ ω,‖b ω (X r ω)‖^2 ∂P ∂nonnegativeLebesgueMeasure)+
          2*(∫ r in Ioc (0 : ℝ≥0) t,∫ ω,∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2
            ∂P ∂nonnegativeLebesgueMeasure) := by
  rcases hsol with ⟨_,_,_,A,S,hA,hS,he⟩
  have hc := terminalClass_ae_increment D b σ Z0 X T t ht A S hA (he t ht)
  refine ⟨(Lp.memLp (terminalClass D 0 A S T t)).ae_eq hc,?_⟩
  rw [← integral_congr_ae (hc.mono (fun _ h => congrArg (fun z : State N => ‖z‖^2) h)),
    PredictableFamilyLift.integral_norm_sq_Lp]
  exact terminalClass_zero_energy_le D A S (fun r ω => b ω (X r ω))
    (fun i j r ω => σ ω i j (X r ω)) T t ht hA hS

theorem randomStrongSolution_increment_bound (D : BrownianDriver N P F)
    (b : Ω → State N → State N) (σ : Ω → Fin N → Fin N → State N → ℝ)
    (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N) (T : ℝ≥0)
    (hsol : IsRandomStrongSolutionOn D (fun ω i x => b ω x i) σ Z0 X T)
    (B : Ω → ℝ) (hB : MemLp B 2 P) (C : ℝ≥0)
    (hb : ∀ r,r≤T → AEStronglyMeasurable (fun ω => b ω (X r ω)) P)
    (hbn : ∀ r,r≤T → ∀ᵐ ω ∂P,‖b ω (X r ω)‖≤B ω)
    (hσ : ∀ i j r,r≤T → AEStronglyMeasurable (fun ω => σ ω i j (X r ω)) P)
    (hσn : ∀ r,r≤T → ∀ᵐ ω ∂P,∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2≤(C : ℝ))
    (t : ℝ≥0) (ht : t≤T) :
    (∫ ω,‖X t ω-Z0 ω‖^2 ∂P)≤
      2*(t : ℝ)^2*(∫ ω,(B ω)^2 ∂P)+2*(t : ℝ)*C := by
  have henergy := (randomStrongSolution_increment_energy D b σ Z0 X T hsol t ht).2
  rcases hsol with ⟨_,_,_,A,S,hA,hS,_⟩
  have hbi (r : ℝ≥0) (hr : r≤T) : Integrable (fun ω => ‖b ω (X r ω)‖^2) P := by
    have hm : MemLp (fun ω => b ω (X r ω)) 2 P := hB.mono' (hb r hr) (hbn r hr)
    exact hm.integrable_norm_pow'
  have hble (r : ℝ≥0) (hr : r≤T) : (∫ ω,‖b ω (X r ω)‖^2 ∂P)≤∫ ω,(B ω)^2 ∂P := by
    apply integral_mono_ae (hbi r hr) hB.integrable_sq
    filter_upwards [hbn r hr] with ω h
    nlinarith [norm_nonneg (b ω (X r ω))]
  have hsi (r : ℝ≥0) (hr : r≤T) : Integrable
      (fun ω => ∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2) P := by
    have hm : AEStronglyMeasurable (fun ω => ∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2) P := by
      convert Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
        Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => (hσ i j r hr).pow 2)) using 1
      funext ω
      simp only [Finset.sum_apply,Pi.pow_apply]
    apply (integrable_const (C : ℝ)).mono' hm
    filter_upwards [hσn r hr] with ω h
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2)] using h
  have hsle (r : ℝ≥0) (hr : r≤T) :
      (∫ ω,∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2 ∂P)≤(C : ℝ) := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae (hsi r hr) (integrable_const (C : ℝ)) (hσn r hr)
  letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) t)) :=
    ⟨by simp [nonnegativeLebesgueMeasure_Ioc]⟩
  have hbt := finite_field_energy_integrableOn A (fun i r ω => b ω (X r ω) i) T t ht hA
  simp_rw [coordinate_square_sum,real_inner_self_eq_norm_sq] at hbt
  have hst := finite_field_energy_integrableOn
    (fun ij : Fin N×Fin N => S ij.1 ij.2) (fun ij r ω => σ ω ij.1 ij.2 (X r ω))
    T t ht (fun ij => hS ij.1 ij.2)
  simp only [Fintype.sum_prod_type] at hst
  have hbe : (∫ r in Ioc (0 : ℝ≥0) t,∫ ω,‖b ω (X r ω)‖^2 ∂P ∂nonnegativeLebesgueMeasure)≤
      (t : ℝ)*(∫ ω,(B ω)^2 ∂P) := by
    calc
      _≤∫ r in Ioc (0 : ℝ≥0) t,(∫ ω,(B ω)^2 ∂P) ∂nonnegativeLebesgueMeasure := by
        apply integral_mono_ae hbt (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hble r (hr.2.trans ht)
      _=_ := by simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal t.coe_nonneg]
  have hse : (∫ r in Ioc (0 : ℝ≥0) t,∫ ω,∑ i : Fin N,∑ j : Fin N,(σ ω i j (X r ω))^2
      ∂P ∂nonnegativeLebesgueMeasure)≤(t : ℝ)*C := by
    calc
      _≤∫ r in Ioc (0 : ℝ≥0) t,(C : ℝ) ∂nonnegativeLebesgueMeasure := by
        apply integral_mono_ae hst (integrable_const _)
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact hsle r (hr.2.trans ht)
      _=_ := by simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal t.coe_nonneg]
  refine henergy.trans ((add_le_add (mul_le_mul_of_nonneg_left hbe (by positivity))
    (mul_le_mul_of_nonneg_left hse (by norm_num))).trans_eq ?_)
  ring

end SphericalAging.RandomSDEIncrementEnergy
