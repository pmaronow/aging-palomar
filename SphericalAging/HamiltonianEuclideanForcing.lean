module

public import SphericalAging.HamiltonianDerivativeCovariance
public import SphericalAging.PhysicalOrderedResponseMoments
public import SphericalAging.PhysicalDisorderVariationalEquation

public section

/-! Dimension-independent forcing control in the true Euclidean ordered
tensor norm. The gradient bound is derived from the actual coefficient
covariance kernel and finite Cauchy--Schwarz, rather than summing separate
coordinate forcing bounds. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.HamiltonianEuclideanForcing
open FiniteModel GaussianIntegrationByParts HamiltonianDerivativeCovariance HardSphereDynamics
set_option maxHeartbeats 1300000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma coefficient_direction_sq_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (x v : State N) (hx : OnSphere x) :
    (∑ I : TensorIndex N p,(fderiv ℝ (hamiltonianCoefficient I) x v)^2)≤(p : ℝ)^2*‖v‖^2 := by
  have hn : (N : ℝ)≠0 := (Nat.cast_pos.mpr hN).ne'
  have hxnorm := (onSphere_iff_norm_sq x).mp hx
  have hcs : (inner ℝ v x)^2≤‖v‖^2*(N : ℝ) := by
    have h := (sq_le_sq₀ (abs_nonneg (inner ℝ v x)) (mul_nonneg (norm_nonneg v) (norm_nonneg x))).mpr
      (abs_real_inner_le_norm v x)
    simpa only [sq_abs,mul_pow,hxnorm] using h
  have hg := coefficient_gradient_cross_gram_overlap hN hp x x v v
  simp only [← pow_two,real_inner_self_eq_norm_sq,hxnorm,div_self hn,one_pow,mul_one] at hg
  rw [real_inner_comm v x] at hg
  rw [hg]
  calc
    _ ≤ (p : ℝ)*‖v‖^2+((p : ℝ)*((p : ℝ)-1)/(N : ℝ))*(‖v‖^2*(N : ℝ)) := by
      have hp1 : (1 : ℝ)≤p := by exact_mod_cast (show 1≤p by omega)
      have hc := mul_le_mul_of_nonneg_left hcs
        (div_nonneg (mul_nonneg (Nat.cast_nonneg p) (sub_nonneg.mpr hp1)) (Nat.cast_nonneg N))
      nlinarith [hc]
    _ = _ := by field_simp;ring

/-- Every genuine ordered tensor direction has physical Hamiltonian
gradient norm at most p times its Euclidean coefficient norm. -/
theorem hamiltonianGradient_euclidean_bound {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (δ : Disorder N p) (x : State N) (hx : OnSphere x) :
    ‖hamiltonianGradient δ x‖≤(p : ℝ)*‖WithLp.toLp 2 δ‖ := by
  let G := hamiltonianGradient δ x
  have he : ‖G‖^2=∑ I : TensorIndex N p,δ I*fderiv ℝ (hamiltonianCoefficient I) x G := by
    have hh := Hamiltonian_derivative_tensorLinear δ 1 x (fun _ => G)
    simp only [coefficientDerivative,iteratedFDeriv_one_apply,tensorLinear] at hh
    rw [← inner_gradient_left] at hh
    change inner ℝ G G=_ at hh
    rw [real_inner_self_eq_norm_sq] at hh
    simpa only [mul_comm] using hh
  have hδ : (∑ I : TensorIndex N p,(δ I)^2)=‖WithLp.toLp 2 δ‖^2 := by
    simp only [EuclideanSpace.real_norm_sq_eq,PiLp.toLp_apply]
  have hcs : (∑ I : TensorIndex N p,δ I*fderiv ℝ (hamiltonianCoefficient I) x G)^2≤
      (∑ I : TensorIndex N p,(δ I)^2)*(∑ I : TensorIndex N p,(fderiv ℝ (hamiltonianCoefficient I) x G)^2) := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ δ (fun I => fderiv ℝ (hamiltonianCoefficient I) x G)
  rw [← he,hδ] at hcs
  have hg := coefficient_direction_sq_bound hN hp x G hx
  have hh := hcs.trans (mul_le_mul_of_nonneg_left hg (sq_nonneg ‖WithLp.toLp 2 δ‖))
  by_cases hz : ‖G‖=0
  · rw [hz]
    positivity
  · have hpos : 0<‖G‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
    have hmul : (‖G‖^2-(p : ℝ)^2*‖WithLp.toLp 2 δ‖^2)*‖G‖^2≤0 := by nlinarith [hh]
    have hsq : ‖G‖^2≤(p : ℝ)^2*‖WithLp.toLp 2 δ‖^2 := by
      by_contra hh
      have hc := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) (sq_pos_of_pos hpos)
      linarith
    exact (sq_le_sq₀ (norm_nonneg G) (mul_nonneg (Nat.cast_nonneg p) (norm_nonneg _))).mp (by simpa only [mul_pow] using hsq)

theorem native_euclidean_forcing_norm {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J δ : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun i => (HamiltonianDisorderResponseSolution.forcing (NullAugmentation.driver D₀) β R hR J δ x T i).value q)‖≤
        (β : ℝ)*(p : ℝ)*‖WithLp.toLp 2 δ‖ := by
  let D := NullAugmentation.driver D₀
  let X := HamiltonianDisorderResponseSolution.baseProcess D β R hR J x T
  have hXs := (Measure.quasiMeasurePreserving_snd (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
    (PhysicalVariationalMoments.baseProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T)
  filter_upwards [hXs] with q hq
  by_cases ht : q.1∈Ioc (0 : ℝ≥0) T
  · have hz : OnSphere (X q.1 q.2) := hq q.1 ht.2
    have hzr : ‖X q.1 q.2‖≤R := by
      have hh := (onSphere_iff_norm_sq _).mp hz
      nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
    have he : WithLp.toLp 2 (fun i => (HamiltonianDisorderResponseSolution.forcing D β R hR J δ x T i).value q)=
        hamiltonianDrift β δ (X q.1 q.2)-hamiltonianDrift β (0 : Disorder N p) (X q.1 q.2) := by
      ext i
      rw [PiLp.toLp_apply,HamiltonianDisorderResponseSolution.forcing_value,ite_eq_left ht,
        CutoffSDE.cutoffDrift_eq β δ R hR _ hzr,CutoffSDE.cutoffDrift_eq β (0 : Disorder N p) R hR _ hzr]
      rfl
    rw [he,PhysicalDisorderVariationalEquation.drift_zero_difference,
      PhysicalDisorderVariationalEquation.physicalForcing,norm_smul,Real.norm_of_nonneg β.coe_nonneg]
    exact (mul_le_mul_of_nonneg_left ((projection_norm_le_onSphere (Nat.ne_of_gt hN) _ _ hz).trans
      (hamiltonianGradient_euclidean_bound hN hp δ _ hz)) β.coe_nonneg).trans_eq (by ring)
  · have he : WithLp.toLp 2 (fun i => (HamiltonianDisorderResponseSolution.forcing D β R hR J δ x T i).value q)=(0 : State N) := by
      ext i
      rw [PiLp.toLp_apply,HamiltonianDisorderResponseSolution.forcing_value,ite_eq_right ht]
      rfl
    rw [he,norm_zero]
    positivity

/-- Actual terminal disorder response in every Euclidean tensor
direction, with the true vector drift/noise rate and no coordinate-count
loss in the forcing. -/
theorem terminal_response_norm_sq {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J δ : Disorder N p) (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ‖^2≤
      ((β : ℝ)*(p : ℝ)*‖WithLp.toLp 2 δ‖)^2*Real.exp
        (((2*PhysicalVariationalMoments.physicalDriftBound p β J+1+
          PhysicalVariationalMoments.physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  have hc := PhysicalVariationalMoments.nativeRows_physical_bounds hN hp D₀ β R hR hNR J x hx T
  have hf := native_euclidean_forcing_norm hN hp D₀ β R hR hNR J δ x hx T
  have hm := VectorSDESecondLocalization.vector_solution_secondMoment_augmented F
    (HamiltonianDisorderResponseSolution.process_strongSolution (NullAugmentation.driver D₀) β R hR J δ x T)
    (PhysicalVariationalMoments.physicalDriftBound p β J) (PhysicalVariationalMoments.physicalNoiseTraceBound N)
    (β*p*‖WithLp.toLp 2 δ‖₊) hc.1 hc.2 hf t ht
  have he : ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ‖^2=
      ∫ ω,‖HamiltonianDisorderResponseSolution.process (NullAugmentation.driver D₀) β R hR J δ x T t ω‖^2 ∂P := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [HamiltonianDisorderResponseSolution.terminalResponse_ae (NullAugmentation.driver D₀) β R hR J δ x T t]
      with ω hω
    rw [hω,real_inner_self_eq_norm_sq]
  rw [he]
  simpa only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one,NNReal.coe_ofNat,
    coe_nnnorm,norm_zero,zero_pow (by norm_num : 2≠0),add_zero] using hm.2

theorem terminal_response_norm_sq_dimension_uniform {N p : ℕ} (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J δ : Disorder N p) (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t≤T) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ‖^2≤
      ((β : ℝ)*(p : ℝ)*‖WithLp.toLp 2 δ‖)^2*Real.exp (11*(t : ℝ)+
        (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ))*GaussianLandscape.landscapeNorm N p J) := by
  refine (terminal_response_norm_sq hN hp D₀ β R hR hNR J δ x hx T t ht).trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ)≤N := by exact_mod_cast hN
  have hdiv : 8/(N : ℝ)≤8 := (div_le_iff₀ hn).mpr (by linarith)
  change (2*(1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)+1+8/(N : ℝ))*(t : ℝ)≤_
  nlinarith [mul_le_mul_of_nonneg_right hdiv t.coe_nonneg]

end SphericalAging.HamiltonianEuclideanForcing
