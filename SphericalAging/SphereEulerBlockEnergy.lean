module

public import SphericalAging.SphereEulerTerminalRepresentation
public import SphericalAging.SphereEulerLocalAlgebra
public import SphericalAging.WholeVectorCoefficientEnergy

public section

/-! Genuine whole-vector second-moment control of one Euler interpolation
block, retaining the noise trace and the dimension scaling. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereEulerBlockEnergy
open HardSphereDynamics SphereEulerCoefficients SphereEulerPredictable SphereEulerInterpolationAlgebra
open ElementaryTerminalFormula TerminalLinearity TerminalStateRepresentation PredictableDriftTime PredictableItoTime
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

private theorem elementary_known_timeCut (a b T : ℝ≥0) (hbT : b≤T)
    (Z : lpMeas ℝ ℝ (F a) 2 P) (f : Ω→ℝ) (hz : (Z : Ω→ℝ)=ᵐ[P] f) :
    (elementaryPredictable F a b Z : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun t omega => if t∈Ioc a b then f omega else 0) T := by
  have hzz : (fun q : ℝ≥0×Ω => (Z : Ω→ℝ) q.2)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      (fun q => f q.2) := Measure.quasiMeasurePreserving_snd.ae_eq_comp hz
  filter_upwards [elementaryPredictable_coeFn F a b Z,hzz] with q he hz
  rw [he]
  by_cases hq : q.1∈Ioc a b
  · have hT : q.1∈Ioc (0:ℝ≥0) T :=
      ⟨lt_of_le_of_lt (show (0:ℝ≥0)≤a from bot_le) hq.1,hq.2.trans hbT⟩
    simp only [FourPapersCommon.continuousAdaptedTimeCut,hT,ite_true,hq,hz]
  · by_cases hT : q.1∈Ioc (0:ℝ≥0) T <;>
      simp only [FourPapersCommon.continuousAdaptedTimeCut,hT,ite_true,ite_false,hq]

variable (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
  (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (T : ℝ≥0)

@[expose] def driftRow (i : Fin N) : PredictableProcessL2 F P :=
  elementaryPredictable F (grid h k) (grid h (k+1)) (driftKnown hN D β h J x k i)
@[expose] def noiseRow (i j : Fin N) : PredictableProcessL2 F P :=
  elementaryPredictable F (grid h k) (grid h (k+1)) (noiseKnown hN D β h J x k i j)
@[expose] def blockClass (t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass D 0 (driftRow hN D β h J x k) (noiseRow hN D β h J x k) T t

theorem blockClass_ae (hbT : grid h (k+1)≤T) (t : ℝ≥0) :
    blockClass hN D β h J x k T t=ᵐ[P] block D β h J x k t := by
  have hd (i : Fin N) : driftVersion (driftRow hN D β h J x k i) T t=ᵐ[P]
      fun omega => (((min t (grid h (k+1)):ℝ≥0):ℝ)-((min t (grid h k):ℝ≥0):ℝ))*driftField D β h J x k i omega := by
    have hh := driftVersion_elementary (grid h k) (grid h (k+1)) T (grid_mono h (Nat.le_succ k)) hbT
      (driftKnown hN D β h J x k i)
    have hz := boundedKnown_ae (P:=P) (grid h k) (driftField D β h J x k i)
      (driftField_stronglyMeasurable D β h J x k i) (driftCap β J) (driftField_bound hN D β h J x k i)
    filter_upwards [hh,hz] with omega hh hz
    change (driftKnown hN D β h J x k i : Ω→ℝ) omega=_ at hz
    change driftVersion (elementaryPredictable F (grid h k) (grid h (k+1)) (driftKnown hN D β h J x k i)) T t omega=_
    rw [hh t,hz]
    simp only [NNReal.coe_min]
  have hn (i j : Fin N) : itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j)
      (D.filtered j) (noiseRow hN D β h J x k i j) t=ᵐ[P]
      fun omega => noiseField D β h J x k i j omega*
        (D.coordinate j (min t (grid h (k+1))) omega-D.coordinate j (min t (grid h k)) omega) := by
    have hh := itoTerminal_elementary_ae D j (grid h k) (grid h (k+1)) t
      (grid_mono h (Nat.le_succ k)) (noiseKnown hN D β h J x k i j)
    have hz := boundedKnown_ae (P:=P) (grid h k) (noiseField D β h J x k i j)
      (noiseField_stronglyMeasurable D β h J x k i j) noiseCap (noiseField_bound hN D β h J x k i j)
    have hi := itoVersion_ae_eq (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
      (noiseRow hN D β h J x k i j) t
    filter_upwards [hh,hz,hi] with omega hh hz hi
    change (noiseKnown hN D β h J x k i j : Ω→ℝ) omega=_ at hz
    rw [←hi]
    change (itoTerminalOperator D j t (elementaryPredictable F (grid h k) (grid h (k+1))
      (noiseKnown hN D β h J x k i j)) : Ω→ℝ) omega=_
    rw [hh,hz]
  filter_upwards [terminalClass_ae D 0 (driftRow hN D β h J x k) (noiseRow hN D β h J x k) T t,
    ae_all_iff.mpr hd,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hn i))] with omega he hd hn
  change (terminalClass D 0 (driftRow hN D β h J x k) (noiseRow hN D β h J x k) T t : Ω→State N) omega=_
  rw [he]
  apply PiLp.ext
  intro i
  simp only [WithLp.ofLp_sum,Finset.sum_apply,PiLp.smul_apply,smul_eq_mul,basisVector,PiLp.single_apply,
    mul_ite,mul_one,mul_zero,Finset.sum_ite_eq,Finset.mem_univ,ite_true,PiLp.zero_apply,zero_add,hd,hn]
  exact (SphereEulerTerminalRepresentation.block_coordinate D β h J x k t omega i).symm

private theorem indicator_energy_integral (a b t : ℝ≥0) (hab : a≤b) (f : Ω→State N) :
    (∫ s in Ioc (0:ℝ≥0) t,∫ omega,‖if s∈Ioc a b then f omega else 0‖^2 ∂P ∂nonnegativeLebesgueMeasure)=
      ((min t b:ℝ)-(min t a:ℝ))*(∫ omega,‖f omega‖^2 ∂P) := by
  rw [←primitive_interval a b t _ hab]
  apply integral_congr_ae
  exact .of_forall (fun s => by by_cases hs : s∈Ioc a b <;> simp [hs])

/-- One genuine Euler block has O(N h) energy, with no coordinate-count loss. -/
theorem blockClass_norm_sq_le (hbT : grid h (k+1)≤T) {t : ℝ≥0} (htT : t≤T)
    (ht : t∈Ioc (grid h k) (grid h (k+1))) :
    ‖blockClass hN D β h J x k T t‖^2≤
      (2*(T:ℝ)*(driftCap β J:ℝ)^2+4*(N:ℝ))*(h:ℝ) := by
  let f : Ω→State N := fun omega => SphereEulerCoefficients.drift β J (node D β h J x k omega)
  let mu : ℝ≥0→Ω→State N := fun s omega => if s∈Ioc (grid h k) (grid h (k+1)) then f omega else 0
  let sigma : Fin N→Fin N→ℝ≥0→Ω→ℝ := fun i j s omega =>
    if s∈Ioc (grid h k) (grid h (k+1)) then noiseField D β h J x k i j omega else 0
  have hA (i : Fin N) : (driftRow hN D β h J x k i : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (fun s omega => mu s omega i) T := by
    have hh := elementary_known_timeCut (grid h k) (grid h (k+1)) T hbT
      (driftKnown hN D β h J x k i) (driftField D β h J x k i)
      (boundedKnown_ae (P:=P) _ _ _ _ _)
    filter_upwards [hh] with q hh
    unfold driftRow
    rw [hh]
    by_cases hs : q.1∈Ioc (grid h k) (grid h (k+1)) <;>
      by_cases hq : q.1∈Ioc (0:ℝ≥0) T <;>
        simp only [FourPapersCommon.continuousAdaptedTimeCut,mu,f,hs,hq,ite_true,ite_false,PiLp.zero_apply,driftField]
  have hS (i j : Fin N) : (noiseRow hN D β h J x k i j : TimeProcessL2 P)=ᵐ[nonnegativeLebesgueMeasure.prod P]
      FourPapersCommon.continuousAdaptedTimeCut (sigma i j) T :=
    elementary_known_timeCut (grid h k) (grid h (k+1)) T hbT (noiseKnown hN D β h J x k i j)
      (noiseField D β h J x k i j) (boundedKnown_ae (P:=P) _ _ _ _ _)
  have hf : MemLp f 2 P := MemLp.of_bound
    ((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable
      (clip_lipschitz.continuous.comp_stronglyMeasurable
        ((node_stronglyMeasurable D β h J x k).mono (F.le _)))).aestronglyMeasurable
    (driftCap β J) (.of_forall (fun omega => drift_norm_bound hN β.coe_nonneg J _))
  have hfE : (∫ omega,‖f omega‖^2 ∂P)≤(driftCap β J:ℝ)^2 := by
    have hh := integral_mono_ae hf.integrable_norm_pow' (integrable_const ((driftCap β J:ℝ)^2))
      (.of_forall (fun omega => pow_le_pow_left₀ (norm_nonneg (f omega))
        (drift_norm_bound hN β.coe_nonneg J (node D β h J x k omega)) 2))
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hnoiseM : AEStronglyMeasurable (fun omega => ∑i : Fin N,∑j : Fin N,(noiseField D β h J x k i j omega)^2) P := by
    have hh := Finset.aestronglyMeasurable_sum (μ:=P) Finset.univ (fun i _ =>
      Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
        ((noiseField_stronglyMeasurable D β h J x k i j).mono (F.le _)).aestronglyMeasurable.pow 2))
    convert hh using 1
    funext omega
    simp only [Finset.sum_apply,Pi.pow_apply]
  have hnoiseI : Integrable (fun omega => ∑i : Fin N,∑j : Fin N,(noiseField D β h J x k i j omega)^2) P := by
    apply (integrable_const (2*(N:ℝ))).mono' hnoiseM
    exact .of_forall (fun (omega : Ω) => by
      rw [Real.norm_eq_abs,abs_of_nonneg (by positivity :
        0≤∑i : Fin N,∑j : Fin N,(noiseField D β h J x k i j omega)^2)]
      exact noise_clipped_frobenius_bound hN (node D β h J x k omega))
  have hnoiseE : (∫ omega,∑i : Fin N,∑j : Fin N,(noiseField D β h J x k i j omega)^2 ∂P)≤2*(N:ℝ) := by
    have hh := integral_mono_ae hnoiseI (integrable_const (2*(N:ℝ)))
      (.of_forall (fun omega => noise_clipped_frobenius_bound hN (node D β h J x k omega)))
    simpa only [integral_const,probReal_univ,one_smul] using hh
  have hmuE := indicator_energy_integral (P:=P) (grid h k) (grid h (k+1)) t (grid_mono h (Nat.le_succ k)) f
  have hsE : (∫ s in Ioc (0:ℝ≥0) t,∫ omega,∑i : Fin N,∑j : Fin N,(sigma i j s omega)^2 ∂P ∂nonnegativeLebesgueMeasure)=
      ((min t (grid h (k+1)):ℝ)-(min t (grid h k):ℝ))*(∫ omega,∑i : Fin N,∑j : Fin N,(noiseField D β h J x k i j omega)^2 ∂P) := by
    rw [←primitive_interval (grid h k) (grid h (k+1)) t _ (grid_mono h (Nat.le_succ k))]
    apply integral_congr_ae
    exact .of_forall (fun s => by by_cases hs : s∈Ioc (grid h k) (grid h (k+1)) <;> simp only [sigma,Set.indicator,hs,ite_true,ite_false,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero,integral_zero])
  have hm : min (t:ℝ) (grid h (k+1):ℝ)=t := min_eq_left ht.2
  have ha : min (t:ℝ) (grid h k:ℝ)=grid h k := min_eq_right ht.1.le
  rw [hm,ha] at hmuE hsE
  change (∫ s in Ioc (0:ℝ≥0) t,∫ omega,‖mu s omega‖^2 ∂P ∂nonnegativeLebesgueMeasure)=_ at hmuE
  have hh := WholeVectorCoefficientEnergy.terminalClass_zero_energy_le D
    (driftRow hN D β h J x k) (noiseRow hN D β h J x k) mu sigma T t htT hA hS
  change ‖blockClass hN D β h J x k T t‖^2≤_ at hh
  rw [hmuE,hsE] at hh
  have hgap := SphereEulerLocalAlgebra.local_time_gap_le (h:=h) ht
  calc
    _ ≤2*(t:ℝ)*(((t:ℝ)-(grid h k:ℝ))*(driftCap β J:ℝ)^2)+
        2*(((t:ℝ)-(grid h k:ℝ))*(2*(N:ℝ))) :=
      hh.trans (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hfE hgap.1) (by positivity))
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnoiseE hgap.1) (by norm_num)))
    _ ≤2*(T:ℝ)*((h:ℝ)*(driftCap β J:ℝ)^2)+2*((h:ℝ)*(2*(N:ℝ))) := by
      have hg0 := hgap.1
      have hg1 := hgap.2
      gcongr
    _ = _ := by ring
end SphericalAging.SphereEulerBlockEnergy
