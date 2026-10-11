module

public import SphericalAging.AdditiveSphereParameterLipschitz

public section

/-! Actual additive-flow outputs jointly measurable in initial state,
Euclidean disorder and Brownian seed, with a samplewise global Lipschitz
bound. This permits honest random sphere initial states and fork seeds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.AdditiveSphereJointParameter
open HardSphereDynamics LocalSDE LandscapeMetricProjection PredictableDriftTime
open AdditiveSphereApproximationCoefficients AdditiveSphereApproximationSDE
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def jointRate (p : ℕ) (β A T : ℝ≥0) : ℝ≥0 :=
  ⟨1+((stateRate p β A:ℝ)+(parameterRate p β:ℝ))*Real.exp ((stateRate p β A:ℝ)*(T:ℝ)),by positivity⟩

theorem noiseRows_initial_independent (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J : CoefficientSpace N p) (x y : State N) (T : ℝ≥0) (i j : Fin N) :
    noiseRows hN hp D β A J x T i j=noiseRows hN hp D β A J y T i j := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [predictableCoefficient_coeFn (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A J x T) T,
    predictableCoefficient_coeFn (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A J y T) T] with q hx hy
  simp only [AdditiveSphereNoise.coefficient] at hx hy
  change (predictableCoefficient (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A J x T) T:TimeProcessL2 P) q=
    (predictableCoefficient (AdditiveSphereNoise.coefficient_lipschitz i j)
      (horizonClass hN hp D β A J y T) T:TimeProcessL2 P) q
  exact hx.trans hy.symm

theorem process_difference_coordinate (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x y : State N) (T t : ℝ≥0) (omega : Ω) (i : Fin N) :
    (process hN hp D β A J x T t omega-process hN hp D β A K y T t omega-(x-y)) i=
      driftVersion (driftRows hN hp D β A J x T i) T t omega-
        driftVersion (driftRows hN hp D β A K y T i) T t omega := by
  simp only [PiLp.sub_apply,process,GlobalSDE.horizonProcess,LocalSDE.version_apply,LocalSDE.coordinateVersion]
  change ((x i+driftVersion (driftRows hN hp D β A J x T i) T t omega+
      ∑ j, PredictableItoTime.itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseRows hN hp D β A J x T i j) t omega)-
    (y i+driftVersion (driftRows hN hp D β A K y T i) T t omega+
      ∑ j, PredictableItoTime.itoVersion (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j)
        (noiseRows hN hp D β A K y T i j) t omega))-(x i-y i)=_
  simp_rw [AdditiveSphereParameterCancellation.noiseRows_independent hN hp D β A J K x T i,
    noiseRows_initial_independent hN hp D β A K x y T i]
  ring

theorem process_difference_eq_integral (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x y : State N) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t≤T→
      process hN hp D β A J x T t omega-process hN hp D β A K y T t omega-(x-y)=
        ∫ s in (0:ℝ)..(t:ℝ),
          drift β A J (process hN hp D β A J x T s.toNNReal omega)-
            drift β A K (process hN hp D β A K y T s.toNNReal omega) := by
  have hdJ := ae_all_iff.mpr (fun i : Fin N => driftVersion_eq_actual_drift_ae
    (process_timeCut hN hp D β A J x T) (drift_coordinate_lipschitz hN hp β A J i))
  have hdK := ae_all_iff.mpr (fun i : Fin N => driftVersion_eq_actual_drift_ae
    (process_timeCut hN hp D β A K y T) (drift_coordinate_lipschitz hN hp β A K i))
  filter_upwards [process_continuous hN hp D β A J x T,process_continuous hN hp D β A K y T,hdJ,hdK]
    with omega hJ hK hdJ hdK
  have hcJ : Continuous (fun s : ℝ => drift β A J (process hN hp D β A J x T s.toNNReal omega)) :=
    (drift_state_lipschitz hN hp β A J).continuous.comp (hJ.comp continuous_real_toNNReal)
  have hcK : Continuous (fun s : ℝ => drift β A K (process hN hp D β A K y T s.toNNReal omega)) :=
    (drift_state_lipschitz hN hp β A K).continuous.comp (hK.comp continuous_real_toNNReal)
  intro t ht
  apply PiLp.ext
  intro i
  have hh : (∫ s in (0:ℝ)..(t:ℝ),
      (drift β A J (process hN hp D β A J x T s.toNNReal omega)-
        drift β A K (process hN hp D β A K y T s.toNNReal omega)) i)=
      (∫ s in (0:ℝ)..(t:ℝ),
        drift β A J (process hN hp D β A J x T s.toNNReal omega)-
          drift β A K (process hN hp D β A K y T s.toNNReal omega)) i := by
    simpa only [Pi.sub_apply,VariationalCoefficients.coordinate_apply] using
      (VariationalCoefficients.coordinate i).intervalIntegral_comp_comm (μ:=volume)
        ((hcJ.sub hcK).intervalIntegrable (0:ℝ) (t:ℝ))
  rw [←hh]
  change _=∫ s in (0:ℝ)..(t:ℝ),driftCoordinate β A J i
    (process hN hp D β A J x T s.toNNReal omega)-driftCoordinate β A K i
    (process hN hp D β A K y T s.toNNReal omega)
  have hiJ : IntervalIntegrable (fun s : ℝ => driftCoordinate β A J i
      (process hN hp D β A J x T s.toNNReal omega)) volume (0:ℝ) (t:ℝ) :=
    ((VariationalCoefficients.coordinate i).continuous.comp hcJ).intervalIntegrable (0:ℝ) (t:ℝ)
  have hiK : IntervalIntegrable (fun s : ℝ => driftCoordinate β A K i
      (process hN hp D β A K y T s.toNNReal omega)) volume (0:ℝ) (t:ℝ) :=
    ((VariationalCoefficients.coordinate i).continuous.comp hcK).intervalIntegrable (0:ℝ) (t:ℝ)
  rw [intervalIntegral.integral_sub hiJ hiK,
    process_difference_coordinate hN hp D β A J K x y T t omega i]
  exact congrArg₂ (fun a b : ℝ => a-b) (hdJ i t ht) (hdK i t ht)

theorem process_joint_parameter_bound (hN : 0<N) (hp : 2≤p) (D : BrownianDriver N P F)
    (β A : ℝ≥0) (J K : CoefficientSpace N p) (x y : State N) (T : ℝ≥0) :
    ∀ᵐ omega ∂P,∀ t,t≤T→
      ‖process hN hp D β A J x T t omega-process hN hp D β A K y T t omega‖≤
        (jointRate p β A T:ℝ)*dist (J,x) (K,y) := by
  filter_upwards [process_continuous hN hp D β A J x T,process_continuous hN hp D β A K y T,
    process_difference_eq_integral hN hp D β A J K x y T] with omega hJ hK he
  let g : ℝ→State N := fun s => drift β A J (process hN hp D β A J x T s.toNNReal omega)-
    drift β A K (process hN hp D β A K y T s.toNNReal omega)
  have hg : Continuous g :=
    ((drift_state_lipschitz hN hp β A J).continuous.comp (hJ.comp continuous_real_toNNReal)).sub
      ((drift_state_lipschitz hN hp β A K).continuous.comp (hK.comp continuous_real_toNNReal))
  have hRate : (1:ℝ)≤stateRate p β A := by
    change 1≤1+(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5)
    have hh : 0≤(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5) := by positivity
    linarith
  have hbound : ∀s∈Ico (0:ℝ) (T:ℝ),‖g s‖≤(stateRate p β A:ℝ)*‖∫r in (0:ℝ)..s,g r‖+
      ((stateRate p β A:ℝ)*‖x-y‖+(parameterRate p β:ℝ)*‖J-K‖) := by
    intro s hs
    have hst : s.toNNReal≤T := by simpa only [Real.toNNReal_coe] using Real.toNNReal_le_toNNReal hs.2.le
    have hes := he s.toNNReal hst
    rw [Real.coe_toNNReal s hs.1] at hes
    have hd : process hN hp D β A J x T s.toNNReal omega-process hN hp D β A K y T s.toNNReal omega=
        (x-y)+(∫r in (0:ℝ)..s,g r) := by rw [←hes];abel
    have hh := AdditiveSphereParameterPrimitive.drift_pair_bound hN hp β A J K
      (process hN hp D β A J x T s.toNNReal omega) (process hN hp D β A K y T s.toNNReal omega)
    change ‖g s‖≤_ at hh
    rw [hd] at hh
    have hn := norm_add_le (x-y) (∫r in (0:ℝ)..s,g r)
    have hm := mul_le_mul_of_nonneg_left hn (stateRate p β A).coe_nonneg
    nlinarith
  intro t ht
  have hh := PrimitiveNormGronwall.primitive_norm_le hg hRate (by positivity)
    hbound (show (t:ℝ)∈Icc (0:ℝ) (T:ℝ) from ⟨t.coe_nonneg,ht⟩)
  have hd : process hN hp D β A J x T t omega-process hN hp D β A K y T t omega=
      (x-y)+(∫r in (0:ℝ)..(t:ℝ),g r) := by rw [←he t ht];abel
  have hcoef : ‖J-K‖≤dist (J,x) (K,y) := by rw [Prod.dist_eq,dist_eq_norm];exact le_max_left _ _
  have hinit : ‖x-y‖≤dist (J,x) (K,y) := by rw [Prod.dist_eq,dist_eq_norm,dist_eq_norm];exact le_max_right _ _
  rw [hd]
  calc
    _≤‖x-y‖+‖∫r in (0:ℝ)..(t:ℝ),g r‖ := norm_add_le _ _
    _≤‖x-y‖+((stateRate p β A:ℝ)*‖x-y‖+(parameterRate p β:ℝ)*‖J-K‖)*Real.exp _ := add_le_add le_rfl hh
    _≤dist (J,x) (K,y)+((stateRate p β A:ℝ)*dist (J,x) (K,y)+
        (parameterRate p β:ℝ)*dist (J,x) (K,y))*Real.exp _ := by gcongr
    _=_ := by change _=(1+((stateRate p β A:ℝ)+(parameterRate p β:ℝ))*Real.exp _)*dist (J,x) (K,y);ring

theorem exists_jointly_measurable_lipschitz_terminal (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β A : ℝ≥0) (T t : ℝ≥0) (ht : t≤T) :
    ∃ G : Ω×(CoefficientSpace N p×State N)→State N,
      Measurable G ∧ (∀ omega,LipschitzWith (jointRate p β A T) (fun q => G (omega,q))) ∧
      ∀ J x,(fun omega => G (omega,(J,x)))=ᵐ[P] process hN hp D β A J x T t := by
  obtain ⟨G,hG,hLip,hEq⟩ := DenseLipschitzModification.exists_jointly_measurable_lipschitz_version
    (jointRate p β A T) (fun q : CoefficientSpace N p×State N => process hN hp D β A q.1 q.2 T t) P
    (fun q => ((process_stronglyAdapted hN hp D β A q.1 q.2 T t).mono (F.le t)).measurable)
    (fun q r => (process_joint_parameter_bound hN hp D β A q.1 r.1 q.2 r.2 T).mono
      (fun omega h => by simpa only [dist_eq_norm] using h t ht))
  exact ⟨G,hG,hLip,fun J x => hEq (J,x)⟩

end SphericalAging.AdditiveSphereJointParameter
