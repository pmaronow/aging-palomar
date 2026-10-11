module

public import SphericalAging.WholeVectorTerminalGronwall

public section

/-! Inhomogeneous dimension-free energy estimate for a genuine zero-initial
terminal class. Literal predictable coefficient fields give the energy inequality;
the coefficient expectations, time continuity, and integral Gronwall step are
kept separate from any application-specific approximation error. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.WholeVectorTerminalInhomogeneousGronwall
open HardSphereDynamics TerminalStateRepresentation WholeVectorCoefficientEnergy
open WholeVectorTerminalGronwall
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem terminalClass_zero_inhomogeneous_gronwall (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : ℝ≥0 → Ω → State N) (σ : Fin N → Fin N → ℝ≥0 → Ω → ℝ)
    (T Kd Ks Fd Fs : ℝ≥0)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => μ s ω i) T)
    (hS : ∀ i j,(S i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (σ i j) T)
    (hμ : ∀ s,s≤T → (∫ ω,‖μ s ω‖^2 ∂P)≤
      (Kd : ℝ)*‖terminalClass D 0 A S T s‖^2+Fd)
    (hσ : ∀ s,s≤T → (∫ ω,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2 ∂P)≤
      (Ks : ℝ)*‖terminalClass D 0 A S T s‖^2+Fs)
    (t : ℝ≥0) (ht : t≤T) :
    ‖terminalClass D 0 A S T t‖^2≤
      (2*(T : ℝ)^2*Fd+2*(T : ℝ)*Fs)*Real.exp ((2*(T : ℝ)*Kd+2*(Ks : ℝ))*t) := by
  let X : ℝ≥0 → Lp (State N) 2 P := fun s => terminalClass D 0 A S T s
  let u : ℝ≥0 → ℝ := fun s => ‖X s‖^2
  have hX : Continuous X := by
    have hh : Continuous (fun z : ℝ≥0×State N => terminalClass D 0 A S T z.1) :=
      TerminalFamilyContinuity.terminalClass_joint_continuous D T
      (fun _ : State N => 0) (fun _ => A) (fun _ => S)
      continuous_const (fun _ => continuous_const) (fun _ _ => continuous_const)
    have hm : Continuous (fun s : ℝ≥0 => (s,(0 : State N))) :=
      continuous_id.prodMk continuous_const
    exact hh.comp (f := fun s : ℝ≥0 => (s,(0 : State N))) hm
  have hu : Continuous u := hX.norm.pow 2
  have hb (r : ℝ≥0) (hr : r≤T) : u r≤2*(T : ℝ)^2*Fd+2*(T : ℝ)*Fs+
      (2*(T : ℝ)*Kd+2*(Ks : ℝ))*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure) := by
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
        (Kd : ℝ)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure)+(Fd : ℝ)*r := by
      calc
        _≤∫ s in Ioc (0 : ℝ≥0) r,(Kd : ℝ)*u s+Fd ∂nonnegativeLebesgueMeasure := by
          apply integral_mono_ae hmi ((hui.const_mul _).add (integrable_const _))
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hμ s (hs.2.trans hr)
        _=_ := by
          rw [integral_add (hui.const_mul _) (integrable_const _),integral_const_mul]
          simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal r.coe_nonneg]
          ring
    have hn : (∫ s in Ioc (0 : ℝ≥0) r,∫ ω,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2 ∂P
        ∂nonnegativeLebesgueMeasure)≤
        (Ks : ℝ)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure)+(Fs : ℝ)*r := by
      calc
        _≤∫ s in Ioc (0 : ℝ≥0) r,(Ks : ℝ)*u s+Fs ∂nonnegativeLebesgueMeasure := by
          apply integral_mono_ae hsi ((hui.const_mul _).add (integrable_const _))
          filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
          exact hσ s (hs.2.trans hr)
        _=_ := by
          rw [integral_add (hui.const_mul _) (integrable_const _),integral_const_mul]
          simp [Measure.real_def,nonnegativeLebesgueMeasure_Ioc,ENNReal.toReal_ofReal r.coe_nonneg]
          ring
    have hh := terminalClass_zero_energy_le D A S μ σ T r hr hA hS
    have hpos : 0≤∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure :=
      integral_nonneg (fun _ => sq_nonneg _)
    have hrt : (r : ℝ)≤T := hr
    change u r≤_ at hh
    calc
      _≤2*(r : ℝ)*((Kd : ℝ)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure)+(Fd : ℝ)*r)+
          2*((Ks : ℝ)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure)+(Fs : ℝ)*r) :=
        hh.trans (add_le_add (mul_le_mul_of_nonneg_left hm (by positivity))
          (mul_le_mul_of_nonneg_left hn (by norm_num)))
      _≤2*(T : ℝ)*((Kd : ℝ)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure)+(Fd : ℝ)*T)+
          2*((Ks : ℝ)*(∫ s in Ioc (0 : ℝ≥0) r,u s ∂nonnegativeLebesgueMeasure)+(Fs : ℝ)*T) := by
        gcongr
      _=_ := by ring
  have hg := LinearSDEFourthMoment.integral_gronwall_bound (fun r : ℝ => u r.toNNReal)
    (2*(T : ℝ)^2*Fd+2*(T : ℝ)*Fs) (2*(T : ℝ)*Kd+2*(Ks : ℝ)) T (by positivity)
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

theorem terminalClass_zero_inhomogeneous_gronwall_of_fields (D : BrownianDriver N P F)
    (A : Fin N → PredictableProcessL2 F P) (S : Fin N → Fin N → PredictableProcessL2 F P)
    (μ : ℝ≥0 → Ω → State N) (σ : Fin N → Fin N → ℝ≥0 → Ω → ℝ)
    (T Kd Ks Fd Fs : ℝ≥0)
    (hA : ∀ i,(A i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s ω => μ s ω i) T)
    (hS : ∀ i j,(S i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (σ i j) T)
    (hμm : ∀ s,s≤T → AEStronglyMeasurable (μ s) P)
    (hμ : ∀ s,s≤T → ∀ᵐ ω ∂P,‖μ s ω‖^2≤
      (Kd : ℝ)*‖terminalClass D 0 A S T s ω‖^2+Fd)
    (hσm : ∀ i j s,s≤T → AEStronglyMeasurable (σ i j s) P)
    (hσ : ∀ s,s≤T → ∀ᵐ ω ∂P,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2≤
      (Ks : ℝ)*‖terminalClass D 0 A S T s ω‖^2+Fs)
    (t : ℝ≥0) (ht : t≤T) :
    ‖terminalClass D 0 A S T t‖^2≤
      (2*(T : ℝ)^2*Fd+2*(T : ℝ)*Fs)*Real.exp ((2*(T : ℝ)*Kd+2*(Ks : ℝ))*t) := by
  have hmi (s : ℝ≥0) (hs : s≤T) : Integrable (fun ω => ‖μ s ω‖^2) P := by
    let X := terminalClass D 0 A S T s
    have hi := ((Lp.memLp X).integrable_norm_pow'.const_mul (Kd : ℝ)).add (integrable_const (Fd : ℝ))
    apply hi.mono' ((hμm s hs).norm.pow 2)
    filter_upwards [hμ s hs] with ω hω
    change ‖‖μ s ω‖^2‖≤(Kd : ℝ)*‖terminalClass D 0 A S T s ω‖^2+Fd
    simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hω
  have hsi (s : ℝ≥0) (hs : s≤T) : Integrable (fun ω => ∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2) P := by
    let X := terminalClass D 0 A S T s
    have hi := ((Lp.memLp X).integrable_norm_pow'.const_mul (Ks : ℝ)).add (integrable_const (Fs : ℝ))
    have hm : AEStronglyMeasurable (fun ω => ∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2) P := by
      convert (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
        Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => (hσm i j s hs).pow 2))) using 1
      funext ω
      simp only [Finset.sum_apply,Pi.pow_apply]
    apply hi.mono' hm
    filter_upwards [hσ s hs] with ω hω
    change ‖∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2‖≤
      (Ks : ℝ)*‖terminalClass D 0 A S T s ω‖^2+Fs
    simpa only [Real.norm_of_nonneg (show 0≤∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2 by positivity)] using hω
  apply terminalClass_zero_inhomogeneous_gronwall D A S μ σ T Kd Ks Fd Fs hA hS _ _ t ht
  · intro s hs
    have hh := integral_mono_ae (hmi s hs)
      (((Lp.memLp (terminalClass D 0 A S T s)).integrable_norm_pow'.const_mul (Kd : ℝ)).add
        (integrable_const (Fd : ℝ))) (hμ s hs)
    change (∫ ω,‖μ s ω‖^2 ∂P)≤∫ ω,(Kd : ℝ)*‖terminalClass D 0 A S T s ω‖^2+Fd ∂P at hh
    simpa only [integral_add (((Lp.memLp (terminalClass D 0 A S T s)).integrable_norm_pow').const_mul _)
      (integrable_const _),integral_const_mul,PredictableFamilyLift.integral_norm_sq_Lp,
      integral_const,probReal_univ,one_smul] using hh
  · intro s hs
    have hh := integral_mono_ae (hsi s hs)
      (((Lp.memLp (terminalClass D 0 A S T s)).integrable_norm_pow'.const_mul (Ks : ℝ)).add
        (integrable_const (Fs : ℝ))) (hσ s hs)
    change (∫ ω,∑ i : Fin N,∑ j : Fin N,(σ i j s ω)^2 ∂P)≤
      ∫ ω,(Ks : ℝ)*‖terminalClass D 0 A S T s ω‖^2+Fs ∂P at hh
    simpa only [integral_add (((Lp.memLp (terminalClass D 0 A S T s)).integrable_norm_pow').const_mul _)
      (integrable_const _),integral_const_mul,PredictableFamilyLift.integral_norm_sq_Lp,
      integral_const,probReal_univ,one_smul] using hh

end SphericalAging.WholeVectorTerminalInhomogeneousGronwall
