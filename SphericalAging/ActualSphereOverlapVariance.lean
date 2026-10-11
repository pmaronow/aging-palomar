module

public import SphericalAging.SphereGaussianVariance
public import SphericalAging.ActualSphereOverlapDerivative

public section

/-! Actual initial-sphere fluctuations of the Brownian-averaged two-time
overlap, with a dimension-uniform annealed O(1/N) bound. Sphere and Gaussian
variance estimates and all tangent response moments are derived. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped InnerProductSpace BigOperators NNReal ENNReal
namespace SphericalAging.ActualSphereOverlapVariance
open FiniteModel HardSphereDynamics ActualSphereOverlapDerivative ActualDisorderOverlapVariance
open SphereInitialLaw SphereGaussianVariance
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

 theorem actual_sphere_overlap_variance (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    variance (initialMean D₀ β R hR J T s t) (sphereLaw N)≤
      (8*Real.pi^2/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))*GaussianLandscape.landscapeNorm N p J)+
        sphereVarianceConstant/(N : ℝ) := by
  have hn : 0<N := by omega
  have hh := sphere_variance_le_tangent hn
    (fun x => (initialMean_hasFDerivAt D₀ β R hR J T s t hT x).differentiableAt)
    (M := 1) (L := initialTangentBound N p β T J) (by norm_num) (Real.sqrt_nonneg _)
    (fun x hx => overlapMean_abs_le_one hn D₀ β R hR hNR x hx T s t hs ht J)
    (fun x v hx => initialMean_projected_derivative_norm hN hp D₀ β R hR hNR J x v hx T s t hs ht hT)
  have hA : 0≤(4/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)) := by positivity
  dsimp [initialTangentBound] at hh
  rw [Real.sq_sqrt hA] at hh
  refine hh.trans_eq ?_
  simp only [one_pow,mul_one]
  congr 1
  · have he : (2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ)=
        (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))*GaussianLandscape.landscapeNorm N p J := by ring
    rw [he]
    ring

 lemma stateClass_joint_continuous (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (T t : ℝ≥0) : Continuous (fun q : Disorder N p × State N =>
      HamiltonianDisorderTerminalDerivative.stateClass D β R hR q.1 q.2 T t) := by
  unfold HamiltonianDisorderTerminalDerivative.stateClass TerminalStateRepresentation.terminalClass
  apply Continuous.add
  · exact TerminalLinearity.initialTerminalOperator.continuous.comp continuous_snd
  · apply continuous_finset_sum
    intro i _
    apply TerminalLinearity.stateTerminalInclusion i |>.continuous.comp
    apply Continuous.add
    · exact (TerminalLinearity.driftTerminalOperator T t).continuous.comp
        (HamiltonianCoefficientDependence.driftClass_continuous D β R hR T i)
    · apply continuous_finset_sum
      intro j _
      exact (TerminalLinearity.itoTerminalOperator D j t).continuous.comp
        (HamiltonianCoefficientDependence.noiseClass_continuous D β R hR T i j)

 lemma initialMean_joint_continuous (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (T s t : ℝ≥0) : Continuous (fun q : Disorder N p × State N =>
      initialMean D₀ β R hR q.1 T s t q.2) := by
  exact ((stateClass_joint_continuous (NullAugmentation.driver D₀) β R hR T s).inner
    (stateClass_joint_continuous (NullAugmentation.driver D₀) β R hR T t)).div_const (N : ℝ)

 lemma initialMean_sphere_memLp (hN : 0<N) (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) :
    MemLp (initialMean D₀ β R hR J T s t) 2 (sphereLaw N) := by
  have hm : StronglyMeasurable (initialMean D₀ β R hR J T s t) :=
    ((initialMean_joint_continuous D₀ β R hR T s t).comp (continuous_const.prodMk continuous_id)).stronglyMeasurable
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  filter_upwards [sphereLaw_support (Nat.succ_le_iff.mpr hN)] with x hx
  simpa only [Real.norm_eq_abs,initialMean] using overlapMean_abs_le_one hN D₀ β R hR hNR x
    ((onSphere_iff_norm_sq _).mpr hx) T s t hs ht J

 lemma sphereVariance_stronglyMeasurable (hN : 0<N) (D₀ : BrownianDriver N P F) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) :
    StronglyMeasurable (fun J : Disorder N p => variance (initialMean D₀ β R hR J T s t) (sphereLaw N)) := by
  have hm := (initialMean_joint_continuous (p := p) D₀ β R hR T s t).stronglyMeasurable
  have he : (fun J : Disorder N p => variance (initialMean D₀ β R hR J T s t) (sphereLaw N))=
      fun J => (∫ x,(initialMean D₀ β R hR J T s t x)^2 ∂sphereLaw N)-
        (∫ x,initialMean D₀ β R hR J T s t x ∂sphereLaw N)^2 := by
    funext J
    exact variance_eq_sub (initialMean_sphere_memLp hN D₀ β R hR hNR J T s t hs ht)
  rw [he]
  exact (hm.pow 2).integral_prod_right.sub (hm.integral_prod_right.pow 2)

 theorem annealed_sphere_overlap_variance (hN : 3≤N) (hp : 2≤p) (D₀ : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (T s t : ℝ≥0) (hs : s≤T) (ht : t≤T) (hT : 0<T) :
    Integrable (fun J : Disorder N p => variance (initialMean D₀ β R hR J T s t) (sphereLaw N)) (disorderLaw N p) ∧
      (∫ J : Disorder N p,variance (initialMean D₀ β R hR J T s t) (sphereLaw N) ∂disorderLaw N p)≤
        (8*Real.pi^2*GaussianLandscapeMoments.momentCeiling p (2*(β : ℝ)*(p : ℝ)^2*(T : ℝ))+
          sphereVarianceConstant)/(N : ℝ) := by
  have hn : 0<N := by omega
  let b := 2*(β : ℝ)*(p : ℝ)^2*(T : ℝ)
  let c := 8*Real.pi^2/(N : ℝ)
  let d := sphereVarianceConstant/(N : ℝ)
  have hc : 0≤c := by dsimp [c];positivity
  have hexp := GaussianLandscapeMoments.uniform_exponential_moment (Nat.succ_le_iff.mpr hn) (by omega : 0<p) b
  have hib : Integrable (fun J : Disorder N p => c*Real.exp (b*GaussianLandscape.landscapeNorm N p J)+d) (disorderLaw N p) :=
    (hexp.1.const_mul c).add (integrable_const d)
  have hi : Integrable (fun J : Disorder N p => variance (initialMean D₀ β R hR J T s t) (sphereLaw N)) (disorderLaw N p) := by
    apply hib.mono' (sphereVariance_stronglyMeasurable hn D₀ β R hR hNR T s t hs ht).aestronglyMeasurable
    exact .of_forall (fun J => by rw [Real.norm_of_nonneg (variance_nonneg _ _)];exact actual_sphere_overlap_variance hN hp D₀ β R hR hNR J T s t hs ht hT)
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ J : Disorder N p,c*Real.exp (b*GaussianLandscape.landscapeNorm N p J)+d ∂disorderLaw N p :=
      integral_mono hi hib (fun J => actual_sphere_overlap_variance hN hp D₀ β R hR hNR J T s t hs ht hT)
    _ = c*(∫ J : Disorder N p,Real.exp (b*GaussianLandscape.landscapeNorm N p J) ∂disorderLaw N p)+d := by
      rw [integral_add (hexp.1.const_mul c) (integrable_const d),integral_const_mul,integral_const]
      simp
    _ ≤ c*GaussianLandscapeMoments.momentCeiling p b+d := add_le_add (mul_le_mul_of_nonneg_left hexp.2 hc) le_rfl
    _ = _ := by dsimp [c,b,d];ring

end SphericalAging.ActualSphereOverlapVariance
