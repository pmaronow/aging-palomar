module

public import SphericalAging.SphereEulerPhysicalComparison
public import SphericalAging.SphereEulerLocalMoment

public section

/-! Genuine global whole-vector Euler error. Both approximation coefficient
bounds follow from the actual clipped coefficients and the independently
proved local block moment; the terminal energy and Gronwall steps are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.SphereEulerPhysicalError
open FiniteModel HardSphereDynamics SphereEulerPredictable SphereEulerInterpolationAlgebra
open SphereEulerPhysicalComparison SphereEulerLocalMoment
open WholeVectorTerminalInhomogeneousGronwall
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def driftRate (β : ℝ≥0) (J : Disorder N p) : ℝ≥0 :=
  ⟨1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J*2^(p-2)*(3*(p : ℝ)+5),
    by have := GaussianLandscape.landscapeNorm_nonnegative N p J;positivity⟩

theorem norm_displacement_sq_le (a b c : State N) :
    ‖a-c‖^2≤2*‖a-b‖^2+2*‖b-c‖^2 := by
  have hh : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a-b) (b-c)
  nlinarith [norm_nonneg (a-c),norm_nonneg (a-b),norm_nonneg (b-c),sq_nonneg (‖a-b‖-‖b-c‖)]

section Error
variable (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F) (β h : ℝ≥0)
  (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift (β : ℝ) J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
  (x : State N) (M : ℕ) (hNR : (N : ℝ)<(R : ℝ)^2) (hx : OnSphere x)

theorem driftField_aestronglyMeasurable (t : ℝ≥0) (ht : t≤grid h M) :
    AEStronglyMeasurable (SphereEulerPhysicalComparison.driftField D₀ β h J R hR hb hs x M t) P := by
  by_cases ht0 : t=0
  · subst t
    unfold SphereEulerPhysicalComparison.driftField
    simp only [ite_eq_left (show (0 : ℝ≥0)=0 from rfl)]
    change AEStronglyMeasurable (fun _ : Ω => (0 : State N)) P
    exact aestronglyMeasurable_const
  · obtain ⟨k,hk,hkt,htk⟩ := exists_interval h M (lt_of_le_of_ne bot_le (Ne.symm ht0)) ht
    have hHard := ((GlobalSDE.horizonProcess_stronglyAdapted (NullAugmentation.driver D₀) hb hs x (grid h M) t).mono
      ((NullAugmentation.augment F P).le t))
    have hNode := (node_stronglyMeasurable (NullAugmentation.driver D₀) β h J x k).mono
      ((NullAugmentation.augment F P).le _)
    have hh := (((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable hHard).sub
      ((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable
        (SphereEulerCoefficients.clip_lipschitz.continuous.comp_stronglyMeasurable hNode))).aestronglyMeasurable (μ:=P)
    convert hh using 1
    funext omega
    exact driftField_eq_node D₀ β h J R hR hb hs x M hk ⟨hkt,htk⟩ omega

theorem noiseField_aestronglyMeasurable (t : ℝ≥0) (ht : t≤grid h M) (i j : Fin N) :
    AEStronglyMeasurable (SphereEulerPhysicalComparison.noiseField D₀ β h J R hR hb hs x M i j t) P := by
  by_cases ht0 : t=0
  · subst t
    unfold SphereEulerPhysicalComparison.noiseField
    simp only [ite_eq_left (show (0 : ℝ≥0)=0 from rfl)]
    change AEStronglyMeasurable (fun _ : Ω => (0 : ℝ)) P
    exact aestronglyMeasurable_const
  · obtain ⟨k,hk,hkt,htk⟩ := exists_interval h M (lt_of_le_of_ne bot_le (Ne.symm ht0)) ht
    have hHard := ((GlobalSDE.horizonProcess_stronglyAdapted (NullAugmentation.driver D₀) hb hs x (grid h M) t).mono
      ((NullAugmentation.augment F P).le t))
    have hNode := (node_stronglyMeasurable (NullAugmentation.driver D₀) β h J x k).mono
      ((NullAugmentation.augment F P).le _)
    have hh := ((continuous_noiseCoordinate i j).comp_stronglyMeasurable hHard).sub
      ((continuous_noiseCoordinate i j).comp_stronglyMeasurable
        (SphereEulerCoefficients.clip_lipschitz.continuous.comp_stronglyMeasurable hNode))
    convert hh.aestronglyMeasurable using 1
    funext omega
    exact noiseField_eq_node D₀ β h J R hR hb hs x M hk ⟨hkt,htk⟩ omega i j

include hp hNR hx in
theorem driftField_sq_le (t : ℝ≥0) (ht : t≤grid h M) :
    ∀ᵐ omega ∂P,‖SphereEulerPhysicalComparison.driftField D₀ β h J R hR hb hs x M t omega‖^2≤
      2*(driftRate β J : ℝ)^2*‖differenceClass hN D₀ β h J R hR hb hs x M t omega‖^2+
        2*(driftRate β J : ℝ)^2*‖interpolant (NullAugmentation.driver D₀) β h J x M t omega-
          leftState (NullAugmentation.driver D₀) β h J x M t omega‖^2 := by
  by_cases ht0 : t=0
  · subst t
    exact .of_forall (fun omega => by simp only [SphereEulerPhysicalComparison.driftField,ite_true,norm_zero,zero_pow (by norm_num : (2 : ℕ)≠0)];positivity)
  · obtain ⟨k,hk,hkt,htk⟩ := exists_interval h M (lt_of_le_of_ne bot_le (Ne.symm ht0)) ht
    filter_upwards [hardProcess_onSphere hN D₀ β h J R hR hb hs x M hNR hx,
      differenceClass_ae hN D₀ β h J R hR hb hs x M t] with omega hsp hdiff
    rw [driftField_eq_node D₀ β h J R hR hb hs x M hk ⟨hkt,htk⟩,
      leftState_eq_node (NullAugmentation.driver D₀) β h J x M hk ⟨hkt,htk⟩,hdiff]
    have hd := SphereEulerCoefficients.drift_lipschitz_bound hN hp β.coe_nonneg J
      (hardProcess D₀ β h J R hR hb hs x M t omega) (node (NullAugmentation.driver D₀) β h J x k omega)
    rw [SphereEulerCoefficients.drift,SphereEulerCoefficients.clip_eq_onSphere _ (hsp t ht)] at hd
    have hds := pow_le_pow_left₀ (norm_nonneg _) hd 2
    rw [mul_pow] at hds
    refine hds.trans ?_
    have hh := mul_le_mul_of_nonneg_left
      (norm_displacement_sq_le (hardProcess D₀ β h J R hR hb hs x M t omega)
        (interpolant (NullAugmentation.driver D₀) β h J x M t omega)
        (node (NullAugmentation.driver D₀) β h J x k omega)) (sq_nonneg (driftRate β J : ℝ))
    change (driftRate β J : ℝ)^2*_≤_
    convert hh using 1 <;> ring

include hNR hx in
theorem noiseField_trace_le (t : ℝ≥0) (ht : t≤grid h M) :
    ∀ᵐ omega ∂P,(∑ i : Fin N,∑ j : Fin N,(SphereEulerPhysicalComparison.noiseField D₀ β h J R hR hb hs x M i j t omega)^2)≤
      (16/(N : ℝ))*‖differenceClass hN D₀ β h J R hR hb hs x M t omega‖^2+
        (16/(N : ℝ))*‖interpolant (NullAugmentation.driver D₀) β h J x M t omega-
          leftState (NullAugmentation.driver D₀) β h J x M t omega‖^2 := by
  by_cases ht0 : t=0
  · subst t
    exact .of_forall (fun omega => by simp only [SphereEulerPhysicalComparison.noiseField,ite_true,zero_pow (by norm_num : (2 : ℕ)≠0),Finset.sum_const_zero];positivity)
  · obtain ⟨k,hk,hkt,htk⟩ := exists_interval h M (lt_of_le_of_ne bot_le (Ne.symm ht0)) ht
    filter_upwards [hardProcess_onSphere hN D₀ β h J R hR hb hs x M hNR hx,
      differenceClass_ae hN D₀ β h J R hR hb hs x M t] with omega hsp hdiff
    simp_rw [noiseField_eq_node D₀ β h J R hR hb hs x M hk ⟨hkt,htk⟩]
    rw [leftState_eq_node (NullAugmentation.driver D₀) β h J x M hk ⟨hkt,htk⟩,hdiff]
    have hh := SphereEulerCoefficients.noise_clipped_difference_bound hN
      (hardProcess D₀ β h J R hR hb hs x M t omega) (node (NullAugmentation.driver D₀) β h J x k omega)
    simp only [SphereEulerCoefficients.noise,SphereEulerCoefficients.clip_eq_onSphere _ (hsp t ht)] at hh
    refine hh.trans ?_
    have hd := mul_le_mul_of_nonneg_left
      (norm_displacement_sq_le (hardProcess D₀ β h J R hR hb hs x M t omega)
        (interpolant (NullAugmentation.driver D₀) β h J x M t omega)
        (node (NullAugmentation.driver D₀) β h J x k omega)) (by positivity : (0 : ℝ)≤8/(N : ℝ))
    convert hd using 1 <;> ring

theorem integral_dominated_by_class_and_defect {f : Ω→ℝ}
    (Z : Lp (State N) 2 P) {E : Ω→State N} (a C : ℝ≥0)
    (hm : AEStronglyMeasurable f P) (hpos : ∀ omega,0≤f omega)
    (hE : MemLp E 2 P) (hEC : (∫ omega,‖E omega‖^2 ∂P)≤C)
    (hbound : ∀ᵐ omega ∂P,f omega≤(a : ℝ)*‖Z omega‖^2+(a : ℝ)*‖E omega‖^2) :
    (∫ omega,f omega ∂P)≤(a : ℝ)*‖Z‖^2+a*C := by
  have hZi := (Lp.memLp Z).integrable_norm_pow'
  have hEi := hE.integrable_norm_pow'
  have hi := (hZi.const_mul (a : ℝ)).add (hEi.const_mul (a : ℝ))
  have hf : Integrable f P := by
    apply hi.mono' hm
    filter_upwards [hbound] with omega ho
    change ‖f omega‖≤(a : ℝ)*‖Z omega‖^2+(a : ℝ)*‖E omega‖^2
    simpa only [Real.norm_of_nonneg (hpos omega)] using ho
  have hh := integral_mono_ae hf hi hbound
  change (∫ omega,f omega ∂P)≤∫ omega,(a : ℝ)*‖Z omega‖^2+(a : ℝ)*‖E omega‖^2 ∂P at hh
  calc
    _≤(a : ℝ)*‖Z‖^2+(a : ℝ)*(∫ omega,‖E omega‖^2 ∂P) := by
      simpa only [integral_add (hZi.const_mul _) (hEi.const_mul _),integral_const_mul,
        PredictableFamilyLift.integral_norm_sq_Lp] using hh
    _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hEC a.coe_nonneg)

include hp hNR hx in
theorem driftField_expected_sq_le (t : ℝ≥0) (ht : t≤grid h M) :
    (∫ omega,‖SphereEulerPhysicalComparison.driftField D₀ β h J R hR hb hs x M t omega‖^2 ∂P)≤
      (2*(driftRate β J : ℝ)^2)*‖differenceClass hN D₀ β h J R hR hb hs x M t‖^2+
        (2*(driftRate β J : ℝ)^2)*localCeiling β h J M := by
  have hh := integral_dominated_by_class_and_defect
    (differenceClass hN D₀ β h J R hR hb hs x M t)
    (2*(driftRate β J)^2) (localCeiling β h J M)
    ((driftField_aestronglyMeasurable D₀ β h J R hR hb hs x M t ht).norm.pow 2)
    (fun _ => sq_nonneg _)
    (local_defect_memLp (NullAugmentation.driver D₀) β h J x M hN t ht)
    (local_defect_secondMoment (NullAugmentation.driver D₀) β h J x M hN t ht)
    (by
      simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,Pi.pow_apply] using
        driftField_sq_le hN hp D₀ β h J R hR hb hs x M hNR hx t ht)
  simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat,Pi.pow_apply] using hh

include hNR hx in
theorem noiseField_expected_trace_le (t : ℝ≥0) (ht : t≤grid h M) :
    (∫ omega,∑ i : Fin N,∑ j : Fin N,(SphereEulerPhysicalComparison.noiseField D₀ β h J R hR hb hs x M i j t omega)^2 ∂P)≤
      (16/(N : ℝ))*‖differenceClass hN D₀ β h J R hR hb hs x M t‖^2+
        (16/(N : ℝ))*localCeiling β h J M := by
  have hm : AEStronglyMeasurable
      (fun omega => ∑ i : Fin N,∑ j : Fin N,(SphereEulerPhysicalComparison.noiseField D₀ β h J R hR hb hs x M i j t omega)^2) P := by
    convert (Finset.aestronglyMeasurable_sum Finset.univ (fun i _ =>
      Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
        (noiseField_aestronglyMeasurable D₀ β h J R hR hb hs x M t ht i j).pow 2))) using 1
    funext omega
    simp only [Finset.sum_apply,Pi.pow_apply]
  have hh := integral_dominated_by_class_and_defect
    (differenceClass hN D₀ β h J R hR hb hs x M t)
    (16/(N : ℝ≥0)) (localCeiling β h J M) hm (fun _ => by positivity)
    (local_defect_memLp (NullAugmentation.driver D₀) β h J x M hN t ht)
    (local_defect_secondMoment (NullAugmentation.driver D₀) β h J x M hN t ht)
    (by
      simpa only [NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat] using
        noiseField_trace_le hN D₀ β h J R hR hb hs x M hNR hx t ht)
  simpa only [NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat] using hh

include hp hNR hx in
theorem differenceClass_norm_sq_le (t : ℝ≥0) (ht : t≤grid h M) :
    ‖differenceClass hN D₀ β h J R hR hb hs x M t‖^2≤
      (grid h M : ℝ)*(localCeiling β h J M : ℝ)*
        (4*(grid h M : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*
        Real.exp ((4*(grid h M : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*t) := by
  have hh := terminalClass_zero_inhomogeneous_gronwall (NullAugmentation.driver D₀)
    (driftRows hN D₀ β h J R hR hb hs x M) (noiseRows hN D₀ β h J R hR hb hs x M)
    (SphereEulerPhysicalComparison.driftField D₀ β h J R hR hb hs x M) (SphereEulerPhysicalComparison.noiseField D₀ β h J R hR hb hs x M)
    (grid h M) (2*(driftRate β J)^2) (16/(N : ℝ≥0))
    (2*(driftRate β J)^2*localCeiling β h J M) ((16/(N : ℝ≥0))*localCeiling β h J M)
    (driftRows_ae hN D₀ β h J R hR hb hs x M hNR hx)
    (noiseRows_ae hN D₀ β h J R hR hb hs x M hNR hx)
    (by
      intro s hsT
      rw [←differenceClass_eq_terminal hN D₀ β h J R hR hb hs x M s]
      simpa only [NNReal.coe_mul,NNReal.coe_pow,NNReal.coe_ofNat] using
        driftField_expected_sq_le hN hp D₀ β h J R hR hb hs x M hNR hx s hsT)
    (by
      intro s hsT
      rw [←differenceClass_eq_terminal hN D₀ β h J R hR hb hs x M s]
      simpa only [NNReal.coe_mul,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat] using
        noiseField_expected_trace_le hN D₀ β h J R hR hb hs x M hNR hx s hsT) t ht
  rw [←differenceClass_eq_terminal hN D₀ β h J R hR hb hs x M t] at hh
  push_cast at hh
  have hr : 2*(grid h M : ℝ)*(2*(driftRate β J : ℝ)^2)+2*(16/(N : ℝ))=
      4*(grid h M : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ) := by ring
  rw [hr] at hh
  convert hh using 1 <;> ring

include hN hp hNR hx in
theorem physical_euler_secondMoment (t : ℝ≥0) (ht : t≤grid h M) :
    (∫ omega,‖hardProcess D₀ β h J R hR hb hs x M t omega-
      interpolant (NullAugmentation.driver D₀) β h J x M t omega‖^2 ∂P)≤
      (grid h M : ℝ)*(localCeiling β h J M : ℝ)*
        (4*(grid h M : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*
        Real.exp ((4*(grid h M : ℝ)*(driftRate β J : ℝ)^2+32/(N : ℝ))*t) := by
  have he : (∫ omega,‖hardProcess D₀ β h J R hR hb hs x M t omega-
      interpolant (NullAugmentation.driver D₀) β h J x M t omega‖^2 ∂P)=
      ‖differenceClass hN D₀ β h J R hR hb hs x M t‖^2 := by
    rw [←PredictableFamilyLift.integral_norm_sq_Lp]
    apply integral_congr_ae
    filter_upwards [differenceClass_ae hN D₀ β h J R hR hb hs x M t] with omega ho
    rw [ho]
  rw [he]
  exact differenceClass_norm_sq_le hN hp D₀ β h J R hR hb hs x M hNR hx t ht

end Error
end SphericalAging.SphereEulerPhysicalError
