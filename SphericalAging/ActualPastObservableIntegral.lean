module

public import SphericalAging.ActualCoordinateNoiseOrthogonality
public import SphericalAging.ActualQuenchedCorrelationIntegral

public section

/-! The genuine physical SDE paired with an arbitrary unbounded L² past
vector observable. Conditional martingale orthogonality removes the actual
projected noise, before specializing the observable to Brownian motion. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualPastObservableIntegral
open HardSphereDynamics FiniteModel FiniteCorrelationIto FiniteCorrelationEquation
  ActualCoordinateNoiseOrthogonality ActualQuenchedCorrelationIntegral
  ActualSphereTransition ActualSphereMarkovRestart PhysicalStateIncrementMoments
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {X : ℝ≥0→Ω→State N}

@[expose] def pastVectorNoise (D : BrownianDriver N P F) (hN : 0<N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun u => X u ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ u, OnSphere (X u ω)) (Y : Ω→State N) (s t : ℝ≥0) (ω : Ω) : ℝ :=
  (∑ i : Fin N,Y ω i*((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω→ℝ) ω-
    (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω→ℝ) ω))/(Real.sqrt 2*N)

 theorem pastVectorNoise_integrable_mean_zero (D : BrownianDriver N P F) (hN : 0<N)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun u => X u ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ u, OnSphere (X u ω)) (Y : Ω→State N)
    {s t : ℝ≥0} (hst : s≤t) (hY : StronglyMeasurable[F s] Y) (hY2 : MemLp Y 2 P) :
    Integrable (pastVectorNoise D hN hXa hXc hSphere Y s t) P ∧
      (∫ ω,pastVectorNoise D hN hXa hXc hSphere Y s t ω ∂P)=0 := by
  have hYi (i : Fin N) : MemLp (fun ω => Y ω i) 2 P := by
    simpa only [PiLp.proj_apply] using
      (hY2.continuousLinearMap_comp (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i))
  have hh (i : Fin N) := actual_coordinate_noise_past_L2_mean_zero D hN hXa hXc hSphere hst i
    (fun ω => Y ω i) ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp_stronglyMeasurable hY)
    (hYi i)
  have hi := integrable_finsetSum Finset.univ (fun i _ => (hh i).1)
  refine ⟨hi.div_const _,?_⟩
  unfold pastVectorNoise
  rw [integral_div,integral_finsetSum _ (fun i _ => (hh i).1)]
  simp only [(hh _).2,Finset.sum_const_zero,zero_div]

 theorem past_vector_equation (D : BrownianDriver N P F) (hN : 0<N)
    (β : ℝ) (J : Disorder N p) (Z0 : Ω→State N) (T : ℝ≥0)
    (hsol : RandomInitialSDE.IsStrongSolutionOn (fun i z => hamiltonianDrift β J z i)
      (fun i j z => noiseColumn z j i) continuous_noiseCoordinate D Z0 X T)
    (hXa : StronglyAdapted F X) (hXc : ∀ᵐ ω ∂P, Continuous (fun u => X u ω))
    (hSphere : ∀ᵐ ω ∂P, ∀ u, OnSphere (X u ω)) (Y : Ω→State N)
    {s t : ℝ≥0} (hst : s≤t) (ht : t≤T) :
    ∀ᵐ ω ∂P,inner ℝ (X t ω) (Y ω)/(Real.sqrt 2*N)=
      inner ℝ (X s ω) (Y ω)/(Real.sqrt 2*N)+
      (∫ u in (s : ℝ)..(t : ℝ),inner ℝ (hamiltonianDrift β J (X u.toNNReal ω)) (Y ω)/(Real.sqrt 2*N))+
      pastVectorNoise D hN hXa hXc hSphere Y s t ω := by
  have het := ae_all_iff.mpr (fun i => physical_coordinate_equation D hN β J Z0 T hsol hXa hXc hSphere ht i)
  have hes := ae_all_iff.mpr (fun i => physical_coordinate_equation D hN β J Z0 T hsol hXa hXc hSphere (hst.trans ht) i)
  filter_upwards [het,hes,hXc] with ω het hes hc
  have hfc (i : Fin N) : Continuous (fun u : ℝ => hamiltonianDrift β J (X u.toNNReal ω) i) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp
      (contDiff_hamiltonianDrift β J).continuous).comp (hc.comp continuous_real_toNNReal)
  have he (i : Fin N) : X t ω i=X s ω i+
      (∫ u in (s : ℝ)..(t : ℝ),hamiltonianDrift β J (X u.toNNReal ω) i)+
      ((coordinateNoiseValue D hN hXa hXc hSphere t i : Ω→ℝ) ω-
        (coordinateNoiseValue D hN hXa hXc hSphere s i : Ω→ℝ) ω) := by
    have hi := intervalIntegral.integral_interval_sub_left
      ((hfc i).intervalIntegrable (μ := volume) (0 : ℝ) (t : ℝ))
      ((hfc i).intervalIntegrable (μ := volume) (0 : ℝ) (s : ℝ))
    linarith [het i,hes i]
  have hip (z : State N) : inner ℝ z (Y ω)=∑ i : Fin N,Y ω i*z i := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct,dotProduct,star_trivial]
  have hd : (∫ u in (s : ℝ)..(t : ℝ),inner ℝ (hamiltonianDrift β J (X u.toNNReal ω)) (Y ω)/(Real.sqrt 2*N))=
      (∑ i : Fin N,Y ω i*(∫ u in (s : ℝ)..(t : ℝ),hamiltonianDrift β J (X u.toNNReal ω) i))/(Real.sqrt 2*N) := by
    simp_rw [hip]
    rw [intervalIntegral.integral_div,intervalIntegral.integral_finsetSum
      (fun i _ => ((hfc i).intervalIntegrable (μ := volume) (s : ℝ) (t : ℝ)).const_mul _)]
    simp only [intervalIntegral.integral_const_mul]
  rw [hd,hip,hip]
  simp_rw [he,mul_add]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp only [pastVectorNoise,add_div]

end SphericalAging.ActualPastObservableIntegral
