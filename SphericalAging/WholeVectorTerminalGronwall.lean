module

public import SphericalAging.WholeVectorCoefficientEnergy
public import SphericalAging.TerminalFamilyContinuity
public import SphericalAging.LinearSDEFourthMoment

public section

/-! Dimension-free Gronwall for the actual zero-initial whole-vector
terminal class. The coefficient energy inequality and mean-square time
continuity are derived from the genuine drift and Itô operators. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.WholeVectorTerminalGronwall
open HardSphereDynamics TerminalStateRepresentation WholeVectorCoefficientEnergy
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem finite_field_energy_integrableOn {I : Type*} [Fintype I]
    (A : I → PredictableProcessL2 F P) (b : I → ℝ≥0 → Ω → ℝ)
    (T t : ℝ≥0) (ht : t≤T)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (b i) T) :
    IntegrableOn (fun s => ∫ ω,∑ i,(b i s ω)^2 ∂P) (Ioc (0 : ℝ≥0) t)
      nonnegativeLebesgueMeasure := by
  have hi (i : I) : Integrable (fun q => (FourPapersCommon.continuousAdaptedTimeCut (b i) t q)^2)
      (nonnegativeLebesgueMeasure.prod P) := (timeCut_memLp (A i) (b i) T t ht (hA i)).integrable_sq
  have hs := (integrable_finsetSum Finset.univ (fun i _ => hi i)).integral_prod_left
  apply (integrable_indicator_iff measurableSet_Ioc).mp
  apply hs.congr
  exact .of_forall (fun s => by
    by_cases ht : s∈Ioc (0 : ℝ≥0) t
    · simp only [Set.indicator_of_mem ht,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_left ht]
    · simp only [Set.indicator_of_notMem ht,FourPapersCommon.continuousAdaptedTimeCut,ite_eq_right ht,
        zero_pow (by norm_num : (2 : ℕ)≠0),Finset.sum_const_zero,integral_zero])

theorem terminalClass_zero_gronwall (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : ℝ≥0 → Ω → State N) (σ : Fin N → Fin N → ℝ≥0 → Ω → ℝ)
    (T K C : ℝ≥0)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => μ s ω i) T)
    (hS : ∀ i j,(S i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (σ i j) T)
    (hμm : ∀ s,s≤T → AEStronglyMeasurable (μ s) P)
    (hμ : ∀ s,s≤T → ∀ᵐ ω ∂P,
      ‖μ s ω‖≤(K : ℝ)*‖terminalClass D 0 A S T s ω‖)
    (hσm : ∀ i j s,s≤T → AEStronglyMeasurable (σ i j s) P)
    (hσ : ∀ s,s≤T → ∀ᵐ ω ∂P,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2≤(C : ℝ))
    (t : ℝ≥0) (ht : t≤T) :
    ‖terminalClass D 0 A S T t‖^2≤
      2*(C : ℝ)*T*Real.exp (2*(T : ℝ)*(K : ℝ)^2*t) := by
  let X : ℝ≥0 → Lp (State N) 2 P := fun s => terminalClass D 0 A S T s
  let u : ℝ≥0 → ℝ := fun s => ‖X s‖^2
  have hX : Continuous X := by
    have hh : Continuous (fun z : ℝ≥0×State N => terminalClass D 0 A S T z.1) :=
      TerminalFamilyContinuity.terminalClass_joint_continuous D T
      (fun _ : State N => 0) (fun _ => A) (fun _ => S)
      continuous_const (fun _ => continuous_const) (fun _ _ => continuous_const)
    have hm : Continuous (fun s : ℝ≥0 => (s,(0 : State N))) :=
      continuous_id.prodMk continuous_const
    have hcomp := hh.comp (f := fun s : ℝ≥0 => (s,(0 : State N))) hm
    change Continuous (fun s : ℝ≥0 => terminalClass D 0 A S T s) at hcomp
    exact hcomp
  have hu : Continuous u := hX.norm.pow 2
  have hμi (s : ℝ≥0) (hs : s≤T) : Integrable (fun ω => ‖μ s ω‖^2) P := by
    have hh : MemLp (μ s) 2 P := ((Lp.memLp (X s)).norm.const_mul (K : ℝ)).mono'
      (hμm s hs) (hμ s hs)
    exact hh.integrable_norm_pow'
  have hσi (s : ℝ≥0) (hs : s≤T) : Integrable (fun ω => ∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2) P := by
    have hsm : AEStronglyMeasurable (fun ω => ∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2) P := by
      convert (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
          Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => (hσm i j s hs).pow 2))) using 1
      funext ω
      simp only [Finset.sum_apply,Pi.pow_apply]
    apply (integrable_const (C : ℝ)).mono' hsm
    filter_upwards [hσ s hs] with ω hω
    simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2)] using hω
  have hμle (s : ℝ≥0) (hs : s≤T) : (∫ ω,‖μ s ω‖^2 ∂P)≤(K : ℝ)^2*u s := by
    calc
      _≤∫ ω,(K : ℝ)^2*‖X s ω‖^2 ∂P := by
        apply integral_mono_ae (hμi s hs) ((Lp.memLp (X s)).integrable_norm_pow'.const_mul _)
        filter_upwards [hμ s hs] with ω hω
        nlinarith [norm_nonneg (μ s ω),norm_nonneg (X s ω),K.coe_nonneg]
      _=_ := by rw [integral_const_mul,PredictableFamilyLift.integral_norm_sq_Lp]
  have hσle (s : ℝ≥0) (hs : s≤T) : (∫ ω,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2 ∂P)≤(C : ℝ) := by
    simpa only [integral_const,probReal_univ,one_smul] using
      integral_mono_ae (hσi s hs) (integrable_const (C : ℝ)) (hσ s hs)
  have hb (r : ℝ≥0) (hr : r≤T) : u r≤2*(C : ℝ)*T+
      (2*(T : ℝ)*(K : ℝ)^2)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure) := by
    letI : IsFiniteMeasure (nonnegativeLebesgueMeasure.restrict (Ioc (0 : ℝ≥0) r)) :=
      ⟨by simp [nonnegativeLebesgueMeasure_Ioc]⟩
    have hmi := finite_field_energy_integrableOn A (fun i s ω => μ s ω i) T r hr hA
    simp_rw [coordinate_square_sum,real_inner_self_eq_norm_sq] at hmi
    have hsi := finite_field_energy_integrableOn
      (fun ij : Fin N×Fin N => S ij.1 ij.2) (fun ij => σ ij.1 ij.2) T r hr (fun ij => hS ij.1 ij.2)
    simp only [Fintype.sum_prod_type] at hsi
    have hui : IntegrableOn u (Ioc (0 : ℝ≥0) r) nonnegativeLebesgueMeasure :=
      hu.integrableOn_Icc.mono_set Ioc_subset_Icc_self
    have hm : (∫ s in Ioc (0 : ℝ≥0) r,∫ ω,‖μ s ω‖^2 ∂P ∂nonnegativeLebesgueMeasure)≤
        (K : ℝ)^2*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure) := by
      rw [← integral_const_mul]
      apply integral_mono_ae hmi (hui.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      exact hμle s (hs.2.trans hr)
    have hn : (∫ s in Ioc (0 : ℝ≥0) r,∫ ω,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2 ∂P
        ∂nonnegativeLebesgueMeasure)≤(C : ℝ)*r := by
      calc
        _≤∫ s in Ioc (0 : ℝ≥0) r,(C : ℝ) ∂nonnegativeLebesgueMeasure := by
          apply integral_mono_ae hsi (integrable_const _)
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hσle s (hs.2.trans hr)
        _=_ := by simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal r.coe_nonneg];ring
    have hh := terminalClass_zero_energy_le D A S μ σ T r hr hA hS
    have hpos : 0≤∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hrt : (r : ℝ)≤T := hr
    change u r≤_ at hh
    calc
      _≤2*(r : ℝ)*((K : ℝ)^2*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure))+2*((C : ℝ)*r) :=
        hh.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
          (mul_le_mul_of_nonneg_left hn (by norm_num)))
      _≤2*(T : ℝ)*((K : ℝ)^2*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure))+2*((C : ℝ)*T) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrt (by norm_num))
            (mul_nonneg (sq_nonneg _) hpos)
        · gcongr
      _=_ := by ring
  have hg := LinearSDEFourthMoment.integral_gronwall_bound (fun r : ℝ => u r.toNNReal)
    (2*(C : ℝ)*T) (2*(T : ℝ)*(K : ℝ)^2) T (by positivity)
    (hu.comp continuous_real_toNNReal) (by
      intro r hr
      have hrs : r.toNNReal≤T := by
        simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hr.2
      have hh := hb r.toNNReal hrs
      have he : (∫ s in Ioc (0 : ℝ≥0) r.toNNReal,u s ∂nonnegativeLebesgueMeasure)=
          ∫ s in (0 : ℝ)..(r.toNNReal : ℝ),u s.toNNReal :=
        PredictableDriftTime.primitive_eq_real_intervalIntegral (fun q : ℝ≥0×Unit => u q.1) _ ()
      rw [he,Real.coe_toNNReal _ hr.1] at hh
      exact hh)
  simpa only [Real.toNNReal_coe] using hg t ⟨t.coe_nonneg,ht⟩

end SphericalAging.WholeVectorTerminalGronwall
