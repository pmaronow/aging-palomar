module

public import SphericalAging.FiniteDisclosureCostObservable

public section

/-! Genuine annealed residual field cost of an actual ambient Gaussian
algorithm at a constructed finite history. All integrability and conditional
Gaussian averaging is established internally. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureAmbientCost
open Set Filter MeasureTheory ProbabilityTheory FiniteModel GaussianLandscape AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureSeedHistory FiniteDisclosureAmbient FiniteDisclosureIntegral FiniteDisclosureIntegrableAverage
open FiniteDisclosureResidualCost FiniteDisclosureCostObservable FiniteDisclosureExactHistory
open ResidualGaussianMeanCost ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open HamiltonianBallBounds SphereGibbsEntropy
open scoped Topology InnerProductSpace NNReal

@[expose]  def cost {N p n : ℕ} {S : Type} [MeasurableSpace S] (P : Plan N p n 0 S)
    (A : S→TensorSpace N p→Vector N) (u : Past N p n 0 S→Vector N) (z : S×TensorSpace N p) : ℝ :=
  Hamiltonian N p z.2.ofLp ((actualSpace P z)ᗮ.starProjection (A z.1 z.2))/(N:ℝ)+
    betaD p*|⟪u (actualHistory P z),A z.1 z.2⟫_ℝ/Real.sqrt (N:ℝ)|^p

 theorem actual_value_eq {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (A : S→TensorSpace N p→Vector N) (u : Past N p n 0 S→Vector N) :
    FiniteDisclosureResidualCost.value N p n 0 S P (initialFrame N S) (fun _ => 0) A u∘
      (execute N p n 0 S P∘initialState)=cost P A u :=
  funext (actual_value P A u)

 theorem cost_integrable {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (hN : 0<N) (hp : 3≤p) (P : Plan N p n 0 S) (μ : Measure S) [IsProbabilityMeasure μ]
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hball : ∀ᵐs ∂μ,∀J,‖A s J‖≤Real.sqrt N)
    (u : Past N p n 0 S→Vector N) (hu : Measurable u)
    (hun : ∀z : S×TensorSpace N p,u (actualHistory P z)=0 ∨ ‖u (actualHistory P z)‖=1) :
    Integrable (cost P A u) (μ.prod (stdGaussian (TensorSpace N p))) := by
  have hf := value_measurable N p n 0 S P (initialFrame N S) measurable_snd
    (fun _ => 0) measurable_const A hA u hu
  have hLaw := (actual_finite_tree_law N p n 0 S P μ).comp (initialState_law μ)
  have hm : Measurable (cost P A u) := by
    rw [←actual_value_eq P A u]
    exact hf.comp hLaw.measurable
  have hQi := (disorder_coordinates_preserving N p).integrable_comp_of_integrable
    (landscapeNorm_integrable hN (by omega : 1≤p))
  have hQprod := hQi.comp_snd μ
  apply (hQprod.add (integrable_const (betaD p))).mono' hm.aestronglyMeasurable
  filter_upwards [(measurePreserving_fst (μ:=μ) (ν:=stdGaussian (TensorSpace N p))).quasiMeasurePreserving.ae hball] with z hz
  have hAb : ‖A z.1 z.2‖≤Real.sqrt N := hz _
  have hPb : ‖(actualSpace P z)ᗮ.starProjection (A z.1 z.2)‖≤Real.sqrt N :=
    ((actualSpace P z)ᗮ.norm_starProjection_apply_le _).trans hAb
  have he := Hamiltonian_ball_bound hN (show 1≤p by omega) z.2.ofLp hPb
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hE : |Hamiltonian N p z.2.ofLp ((actualSpace P z)ᗮ.starProjection (A z.1 z.2))/(N:ℝ)|≤landscapeNorm N p z.2.ofLp := by
    simpa only [abs_div,abs_of_pos hNr] using he
  have hUn : ‖u (actualHistory P z)‖≤1 := by
    rcases hun z with hzero | hunit
    · simp only [hzero,norm_zero];norm_num
    · exact hunit.le
  have hα : |⟪u (actualHistory P z),A z.1 z.2⟫_ℝ/Real.sqrt (N:ℝ)|≤1 := by
    rw [abs_div,abs_of_pos (Real.sqrt_pos.mpr hNr)]
    apply (div_le_one (Real.sqrt_pos.mpr hNr)).mpr
    exact (abs_real_inner_le_norm _ _).trans (by
      simpa only [one_mul] using mul_le_mul hUn hAb (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
  have hβ := (betaD_positive hp).le
  have hpow : 0≤betaD p*|⟪u (actualHistory P z),A z.1 z.2⟫_ℝ/Real.sqrt (N:ℝ)|^p :=
    mul_nonneg hβ (pow_nonneg (abs_nonneg _) _)
  change |cost P A u z|≤landscapeNorm N p z.2.ofLp+betaD p
  unfold cost
  exact (abs_add_le _ _).trans (add_le_add hE (by
    rw [abs_of_nonneg hpow]
    exact mul_le_of_le_one_right hβ (pow_le_one₀ (abs_nonneg _) hα)))

 theorem actual_mean_bound {N p n k : ℕ} {S : Type} [MeasurableSpace S] {L : ℝ≥0}
    (hN : 0<N) (hk : k<N) (hp : 3≤p) {ε : ℝ} (hε : 0≤ε)
    (hb : ∀m,N-k≤m→1≤m→∀B : BallFieldAlgorithm m p L,meanCost B≤thresholdEnergy p+ε)
    (P : Plan N p n 0 S) (μ : Measure S) [IsProbabilityMeasure μ]
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hgood : ∀ᵐs ∂μ,LipschitzWith L (A s) ∧ ∀J,‖A s J‖≤Real.sqrt N)
    (u : Past N p n 0 S→Vector N) (hu : Measurable u)
    (hRank : ∀z : S×TensorSpace N p,Module.finrank ℝ (actualSpace P z)≤k)
    (horth : ∀z : S×TensorSpace N p,u (actualHistory P z)∈(actualSpace P z)ᗮ)
    (hun : ∀z : S×TensorSpace N p,u (actualHistory P z)=0 ∨ ‖u (actualHistory P z)‖=1) :
    (∫z,cost P A u z ∂μ.prod (stdGaussian (TensorSpace N p)))≤
      thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
  let f := FiniteDisclosureResidualCost.value N p n 0 S P (initialFrame N S) (fun _ => 0) A u
  let g := average N p n 0 S f
  have hfm : StronglyMeasurable f :=
    (value_measurable N p n 0 S P (initialFrame N S) measurable_snd
      (fun _ => 0) measurable_const A hA u hu).stronglyMeasurable
  have hLaw := (actual_finite_tree_law N p n 0 S P μ).comp (initialState_law μ)
  have hfi : Integrable f (leafLaw N p n 0 S P μ) :=
    (hLaw.integrable_comp hfm.aestronglyMeasurable).mp (by
      rw [actual_value_eq P A u]
      exact cost_integrable hN hp P μ A hA (hgood.mono (fun s hs => hs.2)) u hu hun)
  have hPast := (actual_finite_past_law N p n 0 S P μ).comp (initialState_law μ)
  haveI : IsProbabilityMeasure (pastLaw N p n 0 S P μ) :=
    hPast.hasLaw.isProbabilityMeasure_iff.mp inferInstance
  have hgm : StronglyMeasurable g := average_stronglyMeasurable N p n 0 S hfm
  have hgi : Integrable g (pastLaw N p n 0 S P μ) := average_integrable N p n 0 S P μ hfm hfi
  have hgActual : ∀ᵐz ∂μ.prod (stdGaussian (TensorSpace N p)),
      g (actualHistory P z)≤thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
    filter_upwards [(measurePreserving_fst (μ:=μ) (ν:=stdGaussian (TensorSpace N p))).quasiMeasurePreserving.ae hgood] with z hz
    have hs : seed N p n 0 S (actualHistory P z)=z.1 :=
      actual_original_seed N p n 0 S P (initialState z)
    exact average_bound hN hk hp hε hb n 0 S P (initialFrame N S) (fun _ => 0)
      (fun _ => Submodule.zero_mem _) A u (actualHistory P z)
      (by rw [hs];exact hz.1) (by rw [hs];exact hz.2) (hRank z) (horth z) (hun z)
  have hgPast : ∀ᵐs ∂pastLaw N p n 0 S P μ,g s≤thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
    rw [←hPast.map_eq]
    exact (ae_map_iff hPast.measurable.aemeasurable (measurableSet_le hgm.measurable measurable_const)).mpr hgActual
  have hi := integral_mono_ae hgi (integrable_const (thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ))) hgPast
  have hid := (hLaw.hasLaw.integral_comp hfm.aestronglyMeasurable).trans
    (leaf_integral_eq_past_average N p n 0 S P μ hfm hfi)
  rw [actual_value_eq P A u] at hid
  rw [hid]
  simpa only [integral_const,probReal_univ,one_smul] using hi

end SphericalAging.FiniteDisclosureAmbientCost
