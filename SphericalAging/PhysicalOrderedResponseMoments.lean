module

public import SphericalAging.PhysicalVariationalMoments
public import SphericalAging.GaussianLandscapeMoments
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

public section

/-! True ordered-disorder responses have dimension-independent second
moment rates. The genuine parameter derivative, response SDE, sphere
support and coefficient bounds are all constructed in imported modules. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalOrderedResponseMoments
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open HamiltonianPicardDependence PhysicalVariationalBounds PhysicalVariationalMoments
  HamiltonianDisorderResponseSolution FiniteModel
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The true forcing of one ordered Gaussian tensor coordinate is bounded
by βp in vector norm on the actual canonical sphere path. -/
theorem native_ordered_forcing_norm (hN : 0 < N) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (hNR : (N : ℝ) < (R : ℝ)^2)
    (J : Disorder N p) (I : TensorIndex N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun i => (forcing (NullAugmentation.driver D₀) β R hR J
        (Pi.single I 1) x T i).value q)‖ ≤ β*(p : ℝ) := by
  let D := NullAugmentation.driver D₀
  let X := baseProcess D β R hR J x T
  have hXs := (Measure.quasiMeasurePreserving_snd
    (μ := nonnegativeLebesgueMeasure) (ν := P)).ae
      (baseProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx T)
  filter_upwards [hXs] with q hq
  by_cases ht : q.1 ∈ Ioc (0 : ℝ≥0) T
  · have hz : OnSphere (X q.1 q.2) := hq q.1 ht.2
    have hzr : ‖X q.1 q.2‖ ≤ R := by
      have hh := (onSphere_iff_norm_sq _).mp hz
      nlinarith [norm_nonneg (X q.1 q.2),R.coe_nonneg]
    have hd := HamiltonianParameter.cutoffDrift_vector_sub β
      (Pi.single I 1 : Disorder N p) 0 R hR (X q.1 q.2)
    simp only [Pi.zero_apply,sub_zero] at hd
    have hsingle : (∑ K : TensorIndex N p,(Pi.single I 1 : Disorder N p) K •
        HamiltonianParameter.couplingDrift β R hR K (X q.1 q.2))=
        HamiltonianParameter.couplingDrift β R hR I (X q.1 q.2) := by
      simp [Pi.single_apply]
    rw [hsingle] at hd
    have he : WithLp.toLp 2 (fun i => (forcing D β R hR J (Pi.single I 1) x T i).value q)=
        HamiltonianParameter.couplingDrift β R hR I (X q.1 q.2) := by
      ext i
      rw [PiLp.toLp_apply,forcing_value,ite_eq_left ht]
      exact congrArg (fun z : State N => z i) hd
    rw [he]
    exact couplingDrift_sphere_norm_le hN β.coe_nonneg R hR I _ hz hzr
  · have he : WithLp.toLp 2 (fun i => (forcing D β R hR J (Pi.single I 1) x T i).value q)=(0 : State N) := by
      ext i
      rw [PiLp.toLp_apply,forcing_value,ite_eq_right ht]
      rfl
    rw [he,norm_zero]
    positivity

/-- The genuine one-coupling response process satisfies a sharp physical
second moment, proved from its actual affine Jacobian SDE. -/
theorem ordered_process_secondMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    MemLp (process (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t) 2 P ∧
      (∫ ω,‖process (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t ω‖^2 ∂P) ≤
        ((β : ℝ)*(p : ℝ))^2*Real.exp
          (((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  have hc := nativeRows_physical_bounds hN hp D₀ β R hR hNR J x hx T
  have hf := native_ordered_forcing_norm hN D₀ β R hR hNR J I x hx T
  have hm := VectorSDESecondLocalization.vector_solution_secondMoment_augmented F
    (process_strongSolution (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T)
    (physicalDriftBound p β J) (physicalNoiseTraceBound N) (β*p) hc.1 hc.2 hf t ht
  simpa only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one,NNReal.coe_ofNat,norm_zero,zero_pow (by norm_num : 2≠0),add_zero] using hm

/-- The actual terminal Fréchet derivative inherits the physical rate;
no formal derivative or moment estimate is an input. -/
theorem ordered_terminal_norm_sq_le (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β R hR J x T t (Pi.single I 1)‖^2 ≤
      ((β : ℝ)*(p : ℝ))^2*Real.exp
        (((2*physicalDriftBound p β J+1+physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  let V := HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
    β R hR J x T t (Pi.single I 1)
  have he : ‖V‖^2=∫ ω,‖process (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t ω‖^2 ∂P := by
    rw [← real_inner_self_eq_norm_sq,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [terminalResponse_ae (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t]
      with ω hω
    rw [hω,real_inner_self_eq_norm_sq]
  rw [he]
  exact (ordered_process_secondMoment hN hp D₀ β R hR hNR J I x hx T t ht).2

/-- The actual response rate has a uniform-in-N exponential ceiling,
linear in the genuine Gaussian landscape seminorm. -/
theorem ordered_terminal_norm_sq_dimension_uniform (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β R hR J x T t (Pi.single I 1)‖^2 ≤
      ((β : ℝ)*(p : ℝ))^2*Real.exp (11*(t : ℝ)+
        (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ))*GaussianLandscape.landscapeNorm N p J) := by
  refine (ordered_terminal_norm_sq_le hN hp D₀ β R hR hNR J I x hx T t ht).trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (sq_nonneg _)
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdiv : 8/(N : ℝ) ≤ 8 := (div_le_iff₀ hn).mpr (by linarith)
  change (2*(1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)+1+
    8/(N : ℝ))*(t : ℝ) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hdiv t.coe_nonneg]

/-- Norms of the genuine L² Fréchet derivative are measurable in the
actual disorder. No samplewise parameter derivative is used. -/
theorem ordered_terminal_norm_sq_measurable (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (I : TensorIndex N p)
    (x : State N) (T t : ℝ≥0) :
    Measurable (fun J : Disorder N p =>
      ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
        β R hR J x T t (Pi.single I 1)‖^2) := by
  let X : Disorder N p → Lp (State N) 2 P := fun J =>
    HamiltonianDisorderTerminalDerivative.stateClass (NullAugmentation.driver D₀) β R hR J x T t
  letI : MeasurableSpace (Lp (State N) 2 P) := borel _
  letI : BorelSpace (Lp (State N) 2 P) := ⟨rfl⟩
  have he : (fun J : Disorder N p => fderiv ℝ X J (Pi.single I 1))=
      (fun J : Disorder N p => HamiltonianDisorderTerminalDerivative.stateResponse
        (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)) := by
    funext J
    exact congrArg (fun f : Disorder N p →L[ℝ] Lp (State N) 2 P => f (Pi.single I 1))
      (HamiltonianDisorderTerminalDerivative.stateClass_hasFDerivAt_disorder D₀ β R hR J x T t).fderiv
  have hm := (measurable_fderiv_apply_const ℝ X (Pi.single I 1)).norm.pow_const 2
  have he' (J : Disorder N p) := congrFun he J
  simpa only [he'] using hm

/-- A true uniform annealed second moment for the response to any one
ordered coupling, under the actual iid Gaussian tensor law. The ceiling
is independent of N, the initial sphere point, the cutoff, and the index. -/
theorem ordered_terminal_uniform_annealed_secondMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    Integrable (fun J : Disorder N p =>
      ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
        β R hR J x T t (Pi.single I 1)‖^2) (disorderLaw N p) ∧
      (∫ J : Disorder N p,
        ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
          β R hR J x T t (Pi.single I 1)‖^2 ∂disorderLaw N p) ≤
        ((β : ℝ)*(p : ℝ))^2*Real.exp (11*(t : ℝ))*
          GaussianLandscapeMoments.momentCeiling p
            (2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)) := by
  let b : ℝ := 2*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)
  let c : ℝ := ((β : ℝ)*(p : ℝ))^2*Real.exp (11*(t : ℝ))
  let f : Disorder N p → ℝ := fun J =>
    ‖HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β R hR J x T t (Pi.single I 1)‖^2
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (Nat.succ_le_iff.mpr hN)
    (by omega : 0 < p) b
  have hg : Integrable (fun J => c*Real.exp (b*GaussianLandscape.landscapeNorm N p J))
      (disorderLaw N p) := hexp.1.const_mul c
  have hb (J : Disorder N p) : f J ≤ c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) := by
    have hh := ordered_terminal_norm_sq_dimension_uniform hN hp D₀ β R hR hNR J I x hx T t ht
    simpa only [f,c,b,Real.exp_add,mul_assoc] using hh
  have hi : Integrable f (disorderLaw N p) := hg.mono
    (ordered_terminal_norm_sq_measurable D₀ β R hR I x T t).aestronglyMeasurable
    (.of_forall (fun J => by
      rw [Real.norm_of_nonneg (sq_nonneg _),Real.norm_of_nonneg (mul_nonneg hc (Real.exp_nonneg _))]
      exact hb J))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ J : Disorder N p,c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p :=
      integral_mono hi hg hb
    _ = c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) :=
      integral_const_mul _ _
    _ ≤ c*GaussianLandscapeMoments.momentCeiling p b := mul_le_mul_of_nonneg_left hexp.2 hc

end SphericalAging.PhysicalOrderedResponseMoments
