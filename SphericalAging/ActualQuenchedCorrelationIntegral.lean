module

public import SphericalAging.FiniteCorrelationEquation
public import SphericalAging.ActualSphereMarkovRestart
public import SphericalAging.PhysicalStateIncrementMoments

public section

/-! The literal fixed-disorder physical SDE yields its true expected
correlation integral equation, with the constructed overlap martingale
removed by its proved zero mean. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualQuenchedCorrelationIntegral
open HardSphereDynamics FiniteModel FiniteCorrelationIto FiniteCorrelationEquation
  ActualSphereTransition ActualSphereMarkovRestart HamiltonianPicardDependence
  GlobalHamiltonianParameter PhysicalStateIncrementMoments
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem jointProcess_fixed_strongSolution (hN : N≠0) (D₀ : BrownianDriver N P F)
    (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (T : ℝ≥0) :
    RandomInitialSDE.IsStrongSolutionOn (fun i z => hamiltonianDrift β J z i)
      (fun i j z => noiseColumn z j i) continuous_noiseCoordinate (NullAugmentation.driver D₀)
      (fun _ => x) (jointProcess (NullAugmentation.driver D₀) β R hR (J,x)) T := by
  let D := NullAugmentation.driver D₀
  let X := HamiltonianJointProcess.globalProcess D β R hR (J,x)
  have hsphere := globalProcess_onSphere hN D₀ β R hR hNR J x hx
  have hbound : ∀ᵐ ω ∂P,∀ t,‖X t ω‖≤R := by
    filter_upwards [hsphere] with ω hω
    intro t
    have hsq := (onSphere_iff_norm_sq _).mp (hω t)
    nlinarith [norm_nonneg (X t ω),R.coe_nonneg]
  have hcut := GlobalSDE.process_strongSolution D
    (drift_family_lipschitz β R hR (‖J‖₊+1) ⟨J,by simp⟩) (noise_family_lipschitz N R hR) x T
  have hphysical : LocalSDE.IsLocalStrongSolutionOn
      (fun i z => hamiltonianDrift β J z i) (fun i j z => noiseColumn z j i)
      CutoffSphere.physical_noise_continuous D x X T :=
    CutoffSphere.coefficient_congr_onPath CutoffSphere.physical_noise_continuous hcut
    (fun i => hbound.mono (fun ω h t _ => (CutoffSDE.cutoffDrift_eq β J R hR _ (h t) i).symm))
    (fun i j => hbound.mono (fun ω h t _ => (CutoffSDE.cutoffNoise_eq N R hR _ (h t) i j).symm))
  have hj := jointProcess_physical hN D₀ β R hR hNR J x hx T
  exact AllPathSDE.IsLocalStrongSolutionOn.path_congr hphysical hj.2.1 hj.2.2.1
    (jointProcess_ae D β R hR (J,x))

lemma normalized_drift_pairing_abs_le (hN : 0<N) (β : ℝ≥0) (J : Disorder N p)
    {x y : State N} (hx : OnSphere x) (hy : OnSphere y) :
    |inner ℝ (hamiltonianDrift β J x) y/(N : ℝ)|≤
      1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J := by
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr hN
  rw [abs_div,abs_of_pos hn]
  calc
    _≤(‖hamiltonianDrift β J x‖*‖y‖)/(N : ℝ) :=
      div_le_div_of_nonneg_right (norm_inner_le_norm (𝕜 := ℝ) _ _) hn.le
    _≤((1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N*Real.sqrt N)/(N : ℝ) := by
      rw [LandscapeDerivatives.sphere_norm y ((onSphere_iff_norm_sq y).mp hy)]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (drift_norm_onSphere hN β J x hx)
        (Real.sqrt_nonneg _)) hn.le
    _=_ := by rw [mul_assoc,← sq,Real.sq_sqrt (Nat.cast_nonneg N)];field_simp

@[expose] def rowDrift (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0) (hR : 0<(R : ℝ))
    (J : Disorder N p) (x : State N) (s : ℝ≥0) (q : ℝ×Ω) : ℝ :=
  inner ℝ (hamiltonianDrift β J (jointProcess D β R hR (J,x) q.1.toNNReal q.2))
    (jointProcess D β R hR (J,x) s q.2)/(N : ℝ)

lemma rowDrift_stronglyMeasurable (D : BrownianDriver N P F) (β : ℝ) (R : ℝ≥0)
    (hR : 0<(R : ℝ)) (J : Disorder N p) (x : State N) (s : ℝ≥0) :
    StronglyMeasurable (rowDrift D β R hR J x s) := by
  have hX : StronglyMeasurable (fun q : ℝ×Ω => jointProcess D β R hR (J,x) q.1.toNNReal q.2) :=
    (jointProcess_measurable D β R hR).comp_measurable (measurable_const.prodMk
      (((continuous_real_toNNReal.measurable).comp measurable_fst).prodMk measurable_snd))
  have hY : StronglyMeasurable (fun q : ℝ×Ω => jointProcess D β R hR (J,x) s q.2) :=
    (((jointProcess_adapted D β R hR s).comp_measurable (measurable_const.prodMk measurable_id)).mono
      (F.le s)).comp_snd
  convert (((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable hX).inner (𝕜 := ℝ) hY).mul_const (N : ℝ)⁻¹ using 1
  funext q
  simp only [rowDrift,div_eq_mul_inv]

theorem actual_quenched_correlation_integral (hN : 0<N) (D₀ : BrownianDriver N P F)
    (β : ℝ≥0) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (s t : ℝ≥0) (hst : s≤t) :
    (∫ ω,overlap (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) t ω)
      (jointProcess (NullAugmentation.driver D₀) β R hR (J,x) s ω) ∂P)=
      1+∫ u in (s : ℝ)..(t : ℝ),∫ ω,rowDrift (NullAugmentation.driver D₀) β R hR J x s (u,ω) ∂P := by
  let D := NullAugmentation.driver D₀
  let X := jointProcess D β R hR (J,x)
  have hsol := jointProcess_fixed_strongSolution (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx t
  have hXa := hsol.1
  have hXc := hsol.2.1
  have hSphere := jointProcess_onSphere (Nat.ne_of_gt hN) D₀ β R hR hNR J x hx
  let ν := volume.restrict (Ioc (s : ℝ) (t : ℝ))
  have hB : Integrable (rowDrift D β R hR J x s) (ν.prod P) :=
    Integrable.of_bound (rowDrift_stronglyMeasurable D β R hR J x s).aestronglyMeasurable
      (1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J) (by
        filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := ν) (ν := P)).ae hSphere] with q hq
        rw [Real.norm_eq_abs]
        exact normalized_drift_pairing_abs_le hN β J (hq q.1.toNNReal) (hq s))
  have hf : Integrable (fun ω => ∫ u in (s : ℝ)..(t : ℝ),rowDrift D β R hR J x s (u,ω)) P := by
    simpa only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst)] using hB.integral_prod_right
  have hM := (Lp.memLp (rowMartingaleValue D hN hXa hXc hSphere s t)).integrable (by norm_num)
  have he := correlation_equation_coordinates D hN β J (fun _ => x) t hsol hXa hXc hSphere hst le_rfl
  have hn := rowMartingaleValue_ae_coordinateNoise D hN hXa hXc hSphere hst
  have hident : (fun ω => overlap (X t ω) (X s ω))=ᵐ[P]
      fun ω => 1+(∫ u in (s : ℝ)..(t : ℝ),rowDrift D β R hR J x s (u,ω))+
        (rowMartingaleValue D hN hXa hXc hSphere s t : Ω → ℝ) ω := by
    filter_upwards [he,hn] with ω he hn
    simpa only [rowDrift,X,D,hn] using he
  rw [integral_congr_ae hident]
  have hf' : Integrable (fun ω => 1+∫ u in (s : ℝ)..(t : ℝ),rowDrift D β R hR J x s (u,ω)) P := by
    convert (integrable_const (1 : ℝ)).add hf using 1
  rw [integral_add hf' hM,
    integral_add (integrable_const 1) hf,rowMartingaleValue_mean_zero D hN hXa hXc hSphere s t]
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul,add_zero]
  congr 1
  simp only [intervalIntegral.integral_of_le (show (s : ℝ)≤t from hst)]
  exact (integral_integral_swap (f := fun u ω => rowDrift D β R hR J x s (u,ω)) hB).symm

end SphericalAging.ActualQuenchedCorrelationIntegral
