module

public import SphericalAging.TwoTimeResponseParameter
public import SphericalAging.ResponseMatrixEnergyContraction
public import SphericalAging.SphereInitialLaw
public import SphericalAging.JointLpRepresentative

public section

/-! Actual two-time response columns under the iid Gaussian disorder,
rotation invariant sphere initial state, and Brownian product law. Joint
measurability comes from differentiating the genuine restarted flow, and
the annealed bound comes from the physical variational equation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.AnnealedTwoTimeResponseMoments
open HardSphereDynamics FiniteModel HamiltonianPicardDependence SphereInitialLaw
open TwoTimeResponseParameter ResponseMatrixEnergyContraction
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def parameterLaw (N p : ℕ) : Measure (Disorder N p × State N) :=
  (disorderLaw N p).prod (sphereLaw N)

instance parameterLaw_probability : IsProbabilityMeasure (parameterLaw N p) := by
  unfold parameterLaw
  infer_instance

lemma parameterLaw_onSphere (hN : 0<N) : ∀ᵐ q ∂parameterLaw N p,OnSphere q.2 := by
  have h := (Measure.quasiMeasurePreserving_snd (μ := disorderLaw N p) (ν := sphereLaw N)).ae
    (sphereLaw_support (Nat.succ_le_iff.mpr hN))
  exact h.mono (fun q hq => (onSphere_iff_norm_sq q.2).mpr hq)

/-- The actual physical matrix column has a quenched fourth moment with
only linear Gaussian landscape dependence in the exponent. -/
theorem responseColumn_fourthMoment (hN : 0<N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T) (v : State N)
    (q : Disorder N p × State N) (hx : OnSphere q.2) :
    MemLp (responseColumn (NullAugmentation.driver D₀) β R hR s T t v q : Ω → State N) 4 P ∧
      (∫ ω,‖(responseColumn (NullAugmentation.driver D₀) β R hR s T t v q) ω‖^4 ∂P)≤
        ‖v‖^4*uniformFourthConstant p β q.1 t := by
  rw [responseColumn_eq_physicalMatrix (Nat.ne_of_gt hN) D₀ β R hR hNR s T t ht hT v q hx]
  let hsol := globalProcess_physicalSolution (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx (s+T)
  let hall := ActualSphereTransition.globalProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR q.1 q.2 hx
  have hh := TwoTimeResponseMoments.terminal_direction_fourthMoment hN hp (NullAugmentation.driver D₀)
    β R hR hNR q.1 (HamiltonianJointProcess.globalProcess (NullAugmentation.driver D₀) β R hR q)
    hsol.choose hsol.choose_spec.choose
    (drift_family_lipschitz β R hR (‖q.1‖₊+1) ⟨q.1,by simp⟩) (noise_family_lipschitz N R hR)
    s T (hall.mono (fun _ h => h s)) (hall.mono (fun _ h u _ => h u))
    (fun _ hA hzero => NullAugmentation.augment_null_known_zero F hA hzero) t ht v
  refine ⟨hh.1,hh.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (physicalFourthConstant_le hN β q.1 t) (by positivity)

/-- A jointly measurable representative of the actual column lies in L⁴
of the full disorder × sphere initial state × Brownian law, with a bound
independent of dimension. Every physical parameter slice is identified. -/
theorem exists_responseColumn_annealed_L4 (hN : 0<N) (hp : 2≤p)
    (D₀ : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s T t : ℝ≥0) (ht : t≤T) (hT : 0<T) (v : State N) :
    ∃ G : (Disorder N p × State N) × Ω → State N,StronglyMeasurable G ∧
      (∀ q,(fun ω => G (q,ω)) =ᵐ[P]
        (responseColumn (NullAugmentation.driver D₀) β R hR s T t v q : Ω → State N)) ∧
      MemLp G 4 ((parameterLaw N p).prod P) ∧
      (∫ q,‖G q‖^4 ∂(parameterLaw N p).prod P)≤
        ‖v‖^4*Real.exp (54*(t : ℝ))*GaussianLandscapeMoments.momentCeiling p
          (4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)) := by
  let V := responseColumn (p := p) (NullAugmentation.driver D₀) β R hR s T t v
  obtain ⟨G,hG,hGV⟩ := JointLpRepresentative.exists_joint_representative V
    (responseColumn_stronglyMeasurable (NullAugmentation.driver D₀) β R hR s T t v)
  let b : ℝ := 4*(β : ℝ)*(p : ℝ)*((p : ℝ)+1)*(t : ℝ)
  let c : ℝ := ‖v‖^4*Real.exp (54*(t : ℝ))
  let f : Disorder N p × State N → ℝ := fun q => ∫ ω,‖G (q,ω)‖^4 ∂P
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment
    (Nat.succ_le_iff.mpr hN) (by omega : 0<p) b
  have hdom : Integrable (fun q : Disorder N p × State N => c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1))
      (parameterLaw N p) := (hexp.1.const_mul c).comp_fst (sphereLaw N)
  have hfsm : StronglyMeasurable f := (hG.norm.pow 4).integral_prod_right'
  have hbound : ∀ᵐ q ∂parameterLaw N p,f q≤c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1) := by
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    have hh := responseColumn_fourthMoment hN hp D₀ β R hR hNR s T t ht hT v q hq
    have he : f q=∫ ω,‖(V q : Ω → State N) ω‖^4 ∂P :=
      integral_congr_ae ((hGV q).mono (fun ω hw => congrArg (fun z : State N => ‖z‖^4) hw))
    rw [he]
    simpa only [uniformFourthConstant,Real.exp_add,b,c,mul_assoc] using hh.2
  have hfi : Integrable f (parameterLaw N p) := hdom.mono' hfsm.aestronglyMeasurable
    (hbound.mono (fun q hq => by
      rw [Real.norm_of_nonneg (show 0≤f q from integral_nonneg (fun _ => by positivity))]
      exact hq))
  have hslice : ∀ᵐ q ∂parameterLaw N p,Integrable (fun ω => ‖G (q,ω)‖^4) P := by
    filter_upwards [parameterLaw_onSphere (p := p) hN] with q hq
    exact ((memLp_congr_ae (hGV q)).mpr
      (responseColumn_fourthMoment hN hp D₀ β R hR hNR s T t ht hT v q hq).1).integrable_norm_pow'
  have hi : Integrable (fun q => ‖G q‖^4) ((parameterLaw N p).prod P) := by
    apply (integrable_prod_iff (hG.norm.pow 4).aestronglyMeasurable).mpr
    refine ⟨hslice,?_⟩
    convert hfi using 1
    funext q
    dsimp only [f]
    exact integral_congr_ae (.of_forall (fun ω => Real.norm_of_nonneg (pow_nonneg (norm_nonneg (G (q,ω))) 4)))
  refine ⟨G,hG,hGV,?_,?_⟩
  · apply (integrable_norm_rpow_iff hG.aestronglyMeasurable
      (by norm_num : (4 : ℝ≥0∞)≠0) (by norm_num : (4 : ℝ≥0∞)≠∞)).mp
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using hi
  · rw [integral_prod _ hi]
    calc
      _ ≤ ∫ q : Disorder N p × State N,c*Real.exp (b*GaussianLandscape.landscapeNorm N p q.1) ∂parameterLaw N p :=
        integral_mono_ae hfi hdom hbound
      _ = c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p) := by
        rw [parameterLaw,integral_prod _ hdom]
        simp only [integral_const,probReal_univ,one_smul,integral_const_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hexp.2 (by positivity)

end SphericalAging.AnnealedTwoTimeResponseMoments
