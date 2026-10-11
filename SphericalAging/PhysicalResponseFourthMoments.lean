module

public import SphericalAging.PhysicalInitialResponseMoments
public import SphericalAging.VectorSDEFourthLocalization
public import SphericalAging.JointLpRepresentative

public section

/-! True physical response fourth moments from the actual differentiated
Hamiltonian SDE, with rates linear in the Gaussian landscape seminorm. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalResponseFourthMoments
open HardSphereDynamics LocalSDE VariationalCoefficients PredictableLinearCoefficient
open HamiltonianPicardDependence PhysicalVariationalBounds PhysicalVariationalMoments
  HamiltonianDisorderResponseSolution FiniteModel PhysicalOrderedResponseMoments PhysicalInitialResponseMoments
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem ordered_process_fourthMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    MemLp (process (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t) 4 P ∧
      (∫ ω,‖process (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t ω‖^4 ∂P) ≤
        ((β : ℝ)*(p : ℝ))^4*Real.exp
          (((4*physicalDriftBound p β J+2+6*physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  have hc := nativeRows_physical_bounds hN hp D₀ β R hR hNR J x hx T
  have hf := native_ordered_forcing_norm hN D₀ β R hR hNR J I x hx T
  have hm := VectorSDEFourthLocalization.vector_solution_fourthMoment_augmented F
    (process_strongSolution (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T)
    (physicalDriftBound p β J) (physicalNoiseTraceBound N) (β*p) hc.1 hc.2 hf t ht
  simpa only [NNReal.coe_mul,NNReal.coe_natCast,NNReal.coe_add,NNReal.coe_one,NNReal.coe_ofNat,norm_zero,zero_pow (by norm_num : 2≠0),add_zero,← pow_mul,show 2*2=4 from rfl] using hm

/-- The actual terminal Fréchet derivative to an ordered coupling has
an actual fourth-moment class under the Brownian probability law. -/
theorem ordered_terminal_fourthMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    let V := HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β R hR J x T t (Pi.single I 1)
    MemLp (V : Ω → State N) 4 P ∧ (∫ ω,‖V ω‖^4 ∂P) ≤
      ((β : ℝ)*(p : ℝ))^4*Real.exp
        (((4*physicalDriftBound p β J+2+6*physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  dsimp only
  have hm := ordered_process_fourthMoment hN hp D₀ β R hR hNR J I x hx T t ht
  have he := terminalResponse_ae (NullAugmentation.driver D₀) β R hR J (Pi.single I 1) x T t
  refine ⟨(memLp_congr_ae he).mpr hm.1,?_⟩
  rw [integral_congr_ae (he.mono (fun ω hh => congrArg (fun z : State N => ‖z‖^4) hh))]
  exact hm.2

/-- Uniform-in-dimension fourth-moment rate for the true ordered coupling
response. It depends linearly on the actual Gaussian landscape norm. -/
theorem ordered_terminal_fourthMoment_dimension_uniform (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    (∫ ω,‖(HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β R hR J x T t (Pi.single I 1) : Ω → State N) ω‖^4 ∂P) ≤
      ((β : ℝ)*(p : ℝ))^4*Real.exp (54*(t : ℝ)+
        (4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ))*GaussianLandscape.landscapeNorm N p J) := by
  refine (ordered_terminal_fourthMoment hN hp D₀ β R hR hNR J I x hx T t ht).2.trans ?_
  apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
  have hn : (0 : ℝ) < N := Nat.cast_pos.mpr hN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hdiv : 8/(N : ℝ) ≤ 8 := (div_le_iff₀ hn).mpr (by linarith)
  change (4*(1+(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*GaussianLandscape.landscapeNorm N p J)+2+
    6*(8/(N : ℝ)))*(t : ℝ) ≤ _
  nlinarith [mul_le_mul_of_nonneg_right hdiv t.coe_nonneg]

/-- Every direction of the true initial-state terminal Fréchet derivative
has a genuine fourth moment with the physical vector/trace rate. -/
theorem initial_terminal_fourthMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (J : Disorder N p)
    (x v : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    let V := HamiltonianTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β J R hR x T t v
    MemLp (V : Ω → State N) 4 P ∧ (∫ ω,‖V ω‖^4 ∂P) ≤
      ‖v‖^4*Real.exp
        (((4*physicalDriftBound p β J+2+6*physicalNoiseTraceBound N : ℝ≥0) : ℝ)*(t : ℝ)) := by
  dsimp only
  let D := NullAugmentation.driver D₀
  let hb := (CutoffSDE.cutoffDrift_lipschitz β J R hR).choose_spec
  let hs := (CutoffSDE.cutoffNoise_lipschitz N R hR).choose_spec
  obtain ⟨Y,hYsol,hYeq⟩ := HamiltonianTerminalDerivative.exists_terminalResponse_solution D β J R hR x v T
  have hc := cutoffRows_physical_bounds hN hp D₀ β R hR hNR J x hx T hb hs
  have hf : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,
      ‖WithLp.toLp 2 (fun _i : Fin N =>
        (AffineSDESecondLocalization.zeroForcing (F := NullAugmentation.augment F P)
          (P := P)).value q)‖ ≤ (0 : ℝ≥0) := .of_forall (fun q => by
    have he : WithLp.toLp 2 (fun _i : Fin N =>
        (AffineSDESecondLocalization.zeroForcing (F := NullAugmentation.augment F P)
          (P := P)).value q)=(0 : State N) := rfl
    rw [he,norm_zero];rfl)
  have hm := VectorSDEFourthLocalization.vector_solution_fourthMoment_augmented F
    (AffineSDESecondLocalization.linear_solution_as_affine hYsol)
    (physicalDriftBound p β J) (physicalNoiseTraceBound N) 0 hc.1 hc.2 hf t ht
  have he := hYeq t
  refine ⟨(memLp_congr_ae he).mpr hm.1,?_⟩
  rw [integral_congr_ae (he.mono (fun ω hh => congrArg (fun z : State N => ‖z‖^4) hh))]
  simpa only [NNReal.coe_zero,zero_pow (by norm_num : 2≠0),zero_add,← pow_mul,show 2*2=4 from rfl,
    NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat] using hm.2


/-- The actual ordered terminal response is strongly measurable as an L²
class in the disorder. The proof uses the true derivative of a continuous
one-dimensional parameter family, so no samplewise derivative is assumed. -/
theorem ordered_terminal_stronglyMeasurable (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (I : TensorIndex N p)
    (x : State N) (T t : ℝ≥0) :
    StronglyMeasurable (fun J : Disorder N p =>
      HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
        β R hR J x T t (Pi.single I 1)) := by
  let X : Disorder N p → Lp (State N) 2 P := fun J =>
    HamiltonianDisorderTerminalDerivative.stateClass (NullAugmentation.driver D₀) β R hR J x T t
  let δ : Disorder N p := Pi.single I 1
  have hc : Continuous X := continuous_iff_continuousAt.mpr (fun J =>
    (HamiltonianDisorderTerminalDerivative.stateClass_hasFDerivAt_disorder D₀ β R hR J x T t).continuousAt)
  let g : Disorder N p → ℝ → Lp (State N) 2 P := fun J c => X (J+c • δ)
  have hg : Continuous (Function.uncurry g) := hc.comp (continuous_fst.add (continuous_snd.smul continuous_const))
  have hm := (stronglyMeasurable_deriv_with_param hg).comp_measurable
    (measurable_id.prodMk (measurable_const : Measurable (fun _ : Disorder N p => (0 : ℝ))))
  have he (J : Disorder N p) : deriv (g J) 0=
      HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t δ := by
    have hd : HasDerivAt (fun c : ℝ => J+c • δ) δ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const δ).const_add J
    have hdf : HasFDerivAt X
        (HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t)
        (J+(0 : ℝ) • δ) := by
      simpa only [X,zero_smul,add_zero] using
        HamiltonianDisorderTerminalDerivative.stateClass_hasFDerivAt_disorder D₀ β R hR J x T t
    have hh := hdf.comp_hasDerivAt 0 hd
    simpa only [zero_smul,add_zero,g,X,Function.comp_def] using hh.deriv
  simpa only [Function.comp_def,id_eq,he,δ] using hm

/-- The genuine Brownian fourth moment of an ordered terminal derivative
is measurable in the Gaussian disorder. Joint representation is proved
from its actual strongly measurable L² family. -/
theorem ordered_terminal_fourthMoment_stronglyMeasurable (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0 < (R : ℝ)) (I : TensorIndex N p)
    (x : State N) (T t : ℝ≥0) :
    StronglyMeasurable (fun J : Disorder N p => ∫ ω,
      ‖(HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
        β R hR J x T t (Pi.single I 1) : Ω → State N) ω‖^4 ∂P) := by
  let V : Disorder N p → Lp (State N) 2 P := fun J =>
    HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)
  obtain ⟨G,hG,hGV⟩ := JointLpRepresentative.exists_joint_representative V
    (ordered_terminal_stronglyMeasurable D₀ β R hR I x T t)
  have hm := (hG.norm.pow 4).integral_prod_right' (ν := P)
  have he : (fun J : Disorder N p => ∫ ω,‖G (J,ω)‖^4 ∂P)=
      (fun J : Disorder N p => ∫ ω,‖(V J : Ω → State N) ω‖^4 ∂P) := by
    funext J
    exact integral_congr_ae ((hGV J).mono (fun ω hh => congrArg (fun z : State N => ‖z‖^4) hh))
  change StronglyMeasurable (fun J : Disorder N p => ∫ ω,‖G (J,ω)‖^4 ∂P) at hm
  rw [he] at hm
  exact hm

/-- A true fourth moment averaged over both Brownian noise and the actual
iid Gaussian coupling law, with a ceiling independent of N. -/
theorem ordered_terminal_uniform_annealed_fourthMoment (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    let f : Disorder N p → ℝ := fun J => ∫ ω,
      ‖(HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
        β R hR J x T t (Pi.single I 1) : Ω → State N) ω‖^4 ∂P
    Integrable f (disorderLaw N p) ∧ (∫ J,f J ∂disorderLaw N p) ≤
      ((β : ℝ)*(p : ℝ))^4*Real.exp (54*(t : ℝ))*
        GaussianLandscapeMoments.momentCeiling p
          (4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)) := by
  dsimp only
  let b : ℝ := 4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)
  let c : ℝ := ((β : ℝ)*(p : ℝ))^4*Real.exp (54*(t : ℝ))
  let f : Disorder N p → ℝ := fun J => ∫ ω,
    ‖(HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
      β R hR J x T t (Pi.single I 1) : Ω → State N) ω‖^4 ∂P
  have hc : 0 ≤ c := by dsimp [c];positivity
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (Nat.succ_le_iff.mpr hN)
    (by omega : 0 < p) b
  have hg : Integrable (fun J => c*Real.exp (b*GaussianLandscape.landscapeNorm N p J))
      (disorderLaw N p) := hexp.1.const_mul c
  have hb (J : Disorder N p) : f J ≤ c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) := by
    have hh := ordered_terminal_fourthMoment_dimension_uniform hN hp D₀ β R hR hNR J I x hx T t ht
    simpa only [f,c,b,Real.exp_add,mul_assoc] using hh
  have hpos (J : Disorder N p) : 0 ≤ f J := integral_nonneg (fun _ => by positivity)
  have hi : Integrable f (disorderLaw N p) := hg.mono
    (ordered_terminal_fourthMoment_stronglyMeasurable D₀ β R hR I x T t).aestronglyMeasurable
    (.of_forall (fun J => by
      rw [Real.norm_of_nonneg (hpos J),Real.norm_of_nonneg (mul_nonneg hc (Real.exp_nonneg _))]
      exact hb J))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ J : Disorder N p,c*Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p :=
      integral_mono hi hg hb
    _ = c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) :=
      integral_const_mul _ _
    _ ≤ c*GaussianLandscapeMoments.momentCeiling p b := mul_le_mul_of_nonneg_left hexp.2 hc


/-- The actual terminal ordered response has a jointly measurable
representative in L⁴ of the full iid-disorder × Brownian law. The
uniform annealed fourth-moment bound applies to this genuine version. -/
theorem exists_ordered_terminal_annealed_L4 (hN : 0 < N) (hp : 2 ≤ p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0 < (R : ℝ))
    (hNR : (N : ℝ) < (R : ℝ)^2) (I : TensorIndex N p)
    (x : State N) (hx : OnSphere x) (T t : ℝ≥0) (ht : t ≤ T) :
    ∃ G : Disorder N p × Ω → State N,StronglyMeasurable G ∧
      (∀ J,(fun ω => G (J,ω)) =ᵐ[P]
        (HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀)
          β R hR J x T t (Pi.single I 1) : Ω → State N)) ∧
      MemLp G 4 ((disorderLaw N p).prod P) ∧
      (∫ q,‖G q‖^4 ∂(disorderLaw N p).prod P) ≤
        ((β : ℝ)*(p : ℝ))^4*Real.exp (54*(t : ℝ))*
          GaussianLandscapeMoments.momentCeiling p
            (4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)) := by
  let V : Disorder N p → Lp (State N) 2 P := fun J =>
    HamiltonianDisorderTerminalDerivative.stateResponse (NullAugmentation.driver D₀) β R hR J x T t (Pi.single I 1)
  obtain ⟨G,hG,hGV⟩ := JointLpRepresentative.exists_joint_representative V
    (ordered_terminal_stronglyMeasurable D₀ β R hR I x T t)
  have ha := ordered_terminal_uniform_annealed_fourthMoment hN hp D₀ β R hR hNR I x hx T t ht
  have hs (J : Disorder N p) : MemLp (fun ω => G (J,ω)) 4 P :=
    (memLp_congr_ae (hGV J)).mpr (ordered_terminal_fourthMoment hN hp D₀ β R hR hNR J I x hx T t ht).1
  have he (J : Disorder N p) : (∫ ω,‖G (J,ω)‖^4 ∂P)=∫ ω,‖(V J : Ω → State N) ω‖^4 ∂P :=
    integral_congr_ae ((hGV J).mono (fun ω hh => congrArg (fun z : State N => ‖z‖^4) hh))
  have hi : Integrable (fun q => ‖G q‖^4) ((disorderLaw N p).prod P) := by
    apply (integrable_prod_iff (hG.norm.pow 4).aestronglyMeasurable).mpr
    refine ⟨.of_forall (fun J => (hs J).integrable_norm_pow'),?_⟩
    convert ha.1 using 1
    funext J
    calc
      (∫ ω,‖‖G (J,ω)‖^4‖ ∂P) = ∫ ω,‖G (J,ω)‖^4 ∂P := by
        apply integral_congr_ae
        exact .of_forall (fun ω => Real.norm_of_nonneg (by positivity))
      _ = _ := he J
  refine ⟨G,hG,hGV,?_,?_⟩
  · apply (integrable_norm_rpow_iff hG.aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞) ≠ 0) (by norm_num : (4 : ℝ≥0∞) ≠ ∞)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hi
  · rw [integral_prod _ hi]
    have heall : (fun J : Disorder N p => ∫ ω,‖G (J,ω)‖^4 ∂P)=fun J => ∫ ω,‖(V J : Ω → State N) ω‖^4 ∂P := funext he
    rw [heall]
    exact ha.2

end SphericalAging.PhysicalResponseFourthMoments
