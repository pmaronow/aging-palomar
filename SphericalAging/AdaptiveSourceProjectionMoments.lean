module

public import SphericalAging.AdaptiveResidualSourceCost
public import SphericalAging.AdaptiveResidualEnergyLimit
public import SphericalAging.AdaptiveMomentComparison

public section

/-! All finite moments in the source10.7 recursion are expectations of
the literal algorithm, disclosed span and query under the original law. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveSourceProjectionMoments
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveResidualSourceCost AdaptiveResidualEnergyLimit
open ResidualGaussianMeanCost SphereGibbsEntropy SeedAlgorithmEnergyBounds
open GaussianLandscape OrthogonalGaussianDisclosure
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

@[expose] def sample {N p : ℕ} {S : Type} (z : S×Disorder N p) : S×TensorSpace N p :=
  (z.1,WithLp.toLp 2 z.2)

theorem sample_measurable {N p : ℕ} {S : Type} [MeasurableSpace S] :
    Measurable (sample : S×Disorder N p→S×TensorSpace N p) :=
  measurable_fst.prodMk ((PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp measurable_snd)

theorem sample_law {N p : ℕ} {S : Type} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    MeasurePreserving (sample : S×Disorder N p→S×TensorSpace N p)
      (μ.prod (disorderLaw N p)) (μ.prod (stdGaussian (TensorSpace N p))) := by
  exact (MeasurePreserving.id μ).prod
    ⟨(PiLp.continuous_toLp 2 (fun _ : TensorIndex N p => ℝ)).measurable,(ordered_tensor_hasLaw N p).map_eq⟩

@[expose] def algorithm {N p : ℕ} {S : Type} (A : S→TensorSpace N p→Vector N) (z : S×Disorder N p) : Vector N :=
  A z.1 (WithLp.toLp 2 z.2)

@[expose] def span {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ) (z : S×Disorder N p) : Submodule ℝ (Vector N) :=
  Space W0 u j (sample z)

@[expose] def overlap {N p : ℕ} {S : Type} (u : S×TensorSpace N p→Vector N)
    (A : S→TensorSpace N p→Vector N) (z : S×Disorder N p) : ℝ :=
  ⟪u (sample z),algorithm A z⟫_ℝ/Real.sqrt (N:ℝ)

@[expose] def powerMoment {N p : ℕ} {S : Type} [MeasurableSpace S] (μ : Measure S)
    (u : S×TensorSpace N p→Vector N) (A : S→TensorSpace N p→Vector N) : ℝ :=
  ∫z,|overlap u A z|^p ∂μ.prod (disorderLaw N p)

theorem algorithm_measurable {N p : ℕ} {S : Type} [MeasurableSpace S]
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A)) :
    Measurable (algorithm A) := hA.comp sample_measurable

theorem projection_measurable {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ)
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A)) :
    Measurable (fun z : S×Disorder N p => (span W0 u j z).starProjection (algorithm A z)) :=
  (AdaptiveResidualSourceCost.projection_measurable S W0 hW0 u hu j A hA).comp sample_measurable

theorem overlap_measurable {N p : ℕ} {S : Type} [MeasurableSpace S]
    (u : S×TensorSpace N p→Vector N) (hu : Measurable u)
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A)) :
    Measurable (overlap u A) :=
  ((hu.comp sample_measurable).inner (algorithm_measurable A hA)).div_const _

theorem overlap_bound {N p : ℕ} {S : Type} (hN : 0<N)
    (u : S×TensorSpace N p→Vector N) (A : S→TensorSpace N p→Vector N)
    (hun : ∀z,u z=0 ∨ ‖u z‖=1) (hball : ∀s J,‖A s J‖≤Real.sqrt N) (z : S×Disorder N p) :
    |overlap u A z|≤1 := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hUn : ‖u (sample z)‖≤1 := by
    rcases hun (sample z) with hz | hn
    · simp only [hz,norm_zero];norm_num
    · exact hn.le
  rw [overlap,abs_div,abs_of_pos (Real.sqrt_pos.mpr hNr)]
  apply (div_le_one (Real.sqrt_pos.mpr hNr)).mpr
  exact (abs_real_inner_le_norm _ _).trans (by
    simpa only [one_mul,algorithm] using mul_le_mul hUn (hball z.1 (WithLp.toLp 2 z.2))
      (norm_nonneg _) (by norm_num : (0:ℝ)≤1))

theorem overlap_power_integrable {N p : ℕ} {S : Type} [MeasurableSpace S]
    (hN : 0<N) (μ : Measure S) [IsProbabilityMeasure μ]
    (u : S×TensorSpace N p→Vector N) (hu : Measurable u)
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hun : ∀z,u z=0 ∨ ‖u z‖=1) (hball : ∀s J,‖A s J‖≤Real.sqrt N) (q : ℕ) :
    Integrable (fun z => |overlap u A z|^q) (μ.prod (disorderLaw N p)) := by
  apply (integrable_const (1:ℝ)).mono'
    ((continuous_abs.measurable.comp (overlap_measurable u hu A hA)).pow_const q).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg _) _)]
    exact pow_le_one₀ (abs_nonneg _) (overlap_bound hN u A hun hball z))

theorem powerMoment_bounds {N p : ℕ} {S : Type} [MeasurableSpace S]
    (hN : 0<N) (μ : Measure S) [IsProbabilityMeasure μ]
    (u : S×TensorSpace N p→Vector N) (hu : Measurable u)
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hun : ∀z,u z=0 ∨ ‖u z‖=1) (hball : ∀s J,‖A s J‖≤Real.sqrt N) :
    0≤powerMoment μ u A ∧ powerMoment μ u A≤1 := by
  refine ⟨integral_nonneg (fun z => pow_nonneg (abs_nonneg _) _),?_⟩
  have hi := overlap_power_integrable hN μ u hu A hA hun hball p
  have hh := integral_mono hi (integrable_const (1:ℝ))
    (fun z => pow_le_one₀ (abs_nonneg _) (overlap_bound hN u A hun hball z) :
      ∀z,|overlap u A z|^p≤1)
  simpa only [powerMoment,integral_const,probReal_univ,one_smul] using hh

theorem projectionEnergy_succ {N p : ℕ} {S : Type} [MeasurableSpace S]
    (hN : 0<N) (hp : 2≤p) (μ : Measure S) [IsProbabilityMeasure μ]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j))
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hball : ∀s J,‖A s J‖≤Real.sqrt N) (j : ℕ)
    (horth : ∀z,u j z∈(Space W0 u j z)ᗮ) (hun : ∀z,u j z=0 ∨ ‖u j z‖=1) :
    projectionEnergy μ (span W0 u (j+1)) (algorithm A)≤
      projectionEnergy μ (span W0 u j) (algorithm A)+(powerMoment μ (u j) A)^(2/(p:ℝ)) := by
  have hNr : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hum := AdaptiveResidualSourceCost.query_measurable S W0 hW0 u hu j
  have hsq := overlap_power_integrable hN μ (u j) hum A hA hun hball 2
  have hpm := projection_measurable S W0 hW0 u hu j A hA
  have hpb z : ‖(span W0 u j z).starProjection (algorithm A z)‖≤Real.sqrt N :=
    ((span W0 u j z).norm_starProjection_apply_le _).trans (hball z.1 _)
  have hm : MemLp (fun z => (span W0 u j z).starProjection (algorithm A z)) 2 (μ.prod (disorderLaw N p)) :=
    MemLp.of_bound hpm.aestronglyMeasurable (Real.sqrt N) (ae_of_all _ hpb)
  have hpi := ((memLp_two_iff_integrable_sq hm.norm.aestronglyMeasurable).mp hm.norm).div_const (N:ℝ)
  have he z : ‖(span W0 u (j+1) z).starProjection (algorithm A z)‖^2/(N:ℝ)=
      ‖(span W0 u j z).starProjection (algorithm A z)‖^2/(N:ℝ)+|overlap (u j) A z|^2 := by
    rw [span,Space,AdaptiveProjectionIncrement.norm_sq_sup_zero_or_unit _ _ _ (horth _) (hun _)]
    rw [add_div,overlap,sq_abs,div_pow,Real.sq_sqrt hNr.le]
    rfl
  have hid : projectionEnergy μ (span W0 u (j+1)) (algorithm A)=
      projectionEnergy μ (span W0 u j) (algorithm A)+(∫z,|overlap (u j) A z|^2 ∂μ.prod (disorderLaw N p)) := by
    simp only [projectionEnergy,he]
    exact integral_add hpi hsq
  rw [hid]
  exact add_le_add_right (AdaptiveMomentComparison.square_le_power_mean (μ.prod (disorderLaw N p)) hp
    (overlap (u j) A) (overlap_measurable (u j) hum A hA) (overlap_bound hN (u j) A hun hball)) _

theorem source_cost_integral_eq {N p : ℕ} {S : Type} [MeasurableSpace S]
    (hN : 0<N) (hp : 3≤p) (μ : Measure S) [IsProbabilityMeasure μ]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j))
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hball : ∀s J,‖A s J‖≤Real.sqrt N) (j : ℕ)
    (hun : ∀z,u j z=0 ∨ ‖u j z‖=1) :
    (∫z,AdaptiveResidualSourceCost.cost W0 u j A z ∂μ.prod (stdGaussian (TensorSpace N p)))=
      meanEnergy μ (residual (span W0 u j) (algorithm A))+betaD p*powerMoment μ (u j) A := by
  have hum := AdaptiveResidualSourceCost.query_measurable S W0 hW0 u hu j
  have hc := AdaptiveResidualSourceCost.cost_integrable S hN hp W0 hW0 u hu j μ A hA
    (ae_of_all _ hball) hun
  have hid := (sample_law (N:=N) (p:=p) μ).hasLaw.integral_comp hc.aestronglyMeasurable
  rw [←hid]
  have hR := residual_measurable (span W0 u j) (algorithm A) (algorithm_measurable A hA)
    (projection_measurable S W0 hW0 u hu j A hA)
  have hRb := residual_ball (span W0 u j) (algorithm A) (fun z => hball z.1 _) 
  have hEi := (energy_integrable_bound hN (by omega : 1≤p) μ hR
    (ae_of_all _ (fun s J => hRb (s,J)))).1
  have hmi := overlap_power_integrable hN μ (u j) hum A hA hun hball p
  change (∫z,energy (residual (span W0 u j) (algorithm A)) z+
      betaD p*|overlap (u j) A z|^p ∂μ.prod (disorderLaw N p))=
    meanEnergy μ (residual (span W0 u j) (algorithm A))+betaD p*powerMoment μ (u j) A
  rw [integral_add hEi (hmi.const_mul (betaD p)),integral_const_mul]
  simp only [meanEnergy,energy,powerMoment,integral_div]

end SphericalAging.AdaptiveSourceProjectionMoments
