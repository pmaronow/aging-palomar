module

public import SphericalAging.ActualPastObservableIntegral

public section

/-! True fixed-disorder expectation equation for the physical state paired
with any square-integrable past vector. All time/expectation exchanges are
proved from sphere support and the actual drift estimate. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualQuenchedPastVectorMean
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualPastObservableIntegral
  ActualQuenchedCorrelationIntegral ActualSphereTransition ActualSphereMarkovRestart
  PhysicalStateIncrementMoments
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def pastDrift (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (x : State N) (Y : Ω→State N) (q : ℝ×Ω) : ℝ :=
  inner ℝ (hamiltonianDrift β J (jointProcess D β R hR (J,x) q.1.toNNReal q.2))
    (Y q.2)/(Real.sqrt 2*N)

lemma pastDrift_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (x : State N) (Y : Ω→State N)
    (hY : StronglyMeasurable Y) : StronglyMeasurable (pastDrift D β R hR J x Y) := by
  have hX : StronglyMeasurable (fun q : ℝ×Ω => jointProcess D β R hR (J,x) q.1.toNNReal q.2) :=
    (jointProcess_measurable D β R hR).comp_measurable (measurable_const.prodMk
      (((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk measurable_snd))
  convert (((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable hX).inner
    (𝕜 := ℝ) hY.comp_snd).mul_const (Real.sqrt 2*N)⁻¹ using 1
  funext q
  simp only [pastDrift,div_eq_mul_inv]

 theorem actual_quenched_past_vector_mean (hN : 0<N) (D₀ : BrownianDriver N P F)
    (β : ℝ≥0) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (s t : ℝ≥0) (hst : s≤t)
    (Y : Ω→State N) (hY : StronglyMeasurable[(NullAugmentation.augment F P) s] Y)
    (hY2 : MemLp Y 2 P) :
    (∫ ω,inner ℝ (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t ω) (Y ω)/(Real.sqrt 2*N) ∂P)=
      (∫ ω,inner ℝ (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) s ω) (Y ω)/(Real.sqrt 2*N) ∂P)+
      ∫ u in (s : ℝ)..(t : ℝ),∫ ω,pastDrift (NullAugmentation.driver D₀) β R hR J x Y (u,ω) ∂P := by
  let D := NullAugmentation.driver D₀
  let X := jointProcess D β R hR (J,x)
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  have hsol := jointProcess_fixed_strongSolution (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx t
  have hSphere := jointProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx
  have hy : StronglyMeasurable Y := hY.mono ((NullAugmentation.augment F P).le s)
  have hyn : Integrable (fun ω => ‖Y ω‖) P := (hY2.integrable (by norm_num)).norm
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  have hd : 0<Real.sqrt 2*(N : ℝ) := by positivity
  have hB : Integrable (pastDrift D β R hR J x Y) (ν.prod P) := by
    apply ((hyn.const_mul ((1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N/(Real.sqrt 2*N))).comp_snd ν).mono'
      (pastDrift_stronglyMeasurable D β R hR J x Y hy).aestronglyMeasurable
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae hSphere] with q hq
    rw [pastDrift,Real.norm_eq_abs,abs_div,abs_of_pos hd]
    calc
      _≤(‖hamiltonianDrift β J (X q.1.toNNReal q.2)‖*‖Y q.2‖)/(Real.sqrt 2*N) :=
        div_le_div_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) _ _) hd.le
      _≤((1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N*‖Y q.2‖)/(Real.sqrt 2*N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (drift_norm_onSphere hN β J _ (hq _)) (norm_nonneg _)) hd.le
      _=_ := by ring
  have hf : Integrable (fun ω => ∫ u in (s : ℝ)..(t : ℝ),pastDrift D β R hR J x Y (u,ω)) P := by
    simpa only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst)] using hB.integral_prod_right
  have hg (u : ℝ≥0) : Integrable (fun ω => inner ℝ (X u ω) (Y ω)/(Real.sqrt 2*N)) P := by
    apply (hyn.const_mul (Real.sqrt N/(Real.sqrt 2*N))).mono'
      (by convert (((hsol.1 u).mono ((NullAugmentation.augment F P).le u)).inner (𝕜 := ℝ) hy).mul_const (Real.sqrt 2*N)⁻¹ |>.aestronglyMeasurable using 1 <;> simp only [X,D,div_eq_mul_inv])
    filter_upwards [hSphere] with ω hω
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hd]
    calc
      _≤(‖X u ω‖*‖Y ω‖)/(Real.sqrt 2*N) := div_le_div_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) _ _) hd.le
      _=_ := by rw [sphere_norm (hω u)];ring
  have hm := pastVectorNoise_integrable_mean_zero D hN hsol.1 hsol.2.1 hSphere Y hst hY hY2
  have he := past_vector_equation D hN β J (fun _ => x) t hsol hsol.1 hsol.2.1 hSphere Y hst le_rfl
  have he' : (fun ω => inner ℝ (X t ω) (Y ω)/(Real.sqrt 2*N))=ᵐ[P]
      (fun ω => (inner ℝ (X s ω) (Y ω)/(Real.sqrt 2*N)+
        ∫ u in (s : ℝ)..(t : ℝ),pastDrift D β R hR J x Y (u,ω))+
        pastVectorNoise D hN hsol.1 hsol.2.1 hSphere Y s t ω) := by
    filter_upwards [he] with ω hω
    simpa only [pastDrift,X,D] using hω
  rw [integral_congr_ae he']
  have hh : Integrable (fun ω => inner ℝ (X s ω) (Y ω)/(Real.sqrt 2*N)+
      ∫ u in (s : ℝ)..(t : ℝ),pastDrift D β R hR J x Y (u,ω)) P := (hg s).add hf
  rw [integral_add hh hm.1,integral_add (hg s) hf,hm.2,add_zero]
  congr 1
  simp only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst)]
  exact (integral_integral_swap (f := fun u ω => pastDrift D β R hR J x Y (u,ω)) hB).symm

end SphericalAging.ActualQuenchedPastVectorMean
