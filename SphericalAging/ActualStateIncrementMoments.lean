module

public import SphericalAging.PhysicalStateIncrementMoments
public import SphericalAging.ActualModelOverlapVariance
public import SphericalAging.GaussianLandscapeMoments

public section

/-! Dimension-uniform time increments under the literal independent
Gaussian-disorder, uniform-sphere, and Brownian model. Actual physical
quenched increments are averaged using genuine product integrability and
the proved uniform Gaussian landscape second moment. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualStateIncrementMoments
open HardSphereDynamics FiniteModel AnnealedCutoffProcess ActualSphereTransition
open ActualSphereMarkovRestart PhysicalStateIncrementMoments GaussianLandscape GaussianLandscapeMoments
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def actualState (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0)
    (ω : Parameter N p×VectorBrownian.Space N) : State N :=
  AnnealedGlobalSDE.globalProcess (NullAugmentation.driver (VectorBrownian.driver N))
    β R hR (AnnealedModelLaw.parameter_disorder_memLp N p) t ω

theorem actualState_onSphere (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) :
    ∀ᵐ ω ∂AnnealedModelLaw.law N p,∀ t,OnSphere (actualState (p := p) β R hR t ω) :=
  (AnnealedGlobalSDE.globalProcess_physical (by omega : N≠0) (VectorBrownian.driver N)
    β R hR hNR (AnnealedModelLaw.parameter_disorder_memLp N p)
      (AnnealedModelLaw.parameter_initial_onSphere hN p)).2

theorem actualState_memLp (hN : 1≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (t : ℝ≥0) :
    MemLp (actualState (p := p) β R hR t) 2 (AnnealedModelLaw.law N p) := by
  have hm := (AnnealedGlobalSDE.globalProcess_stronglyAdapted
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p) t).mono
      ((AnnealedModelLaw.filtration N p).le t)
  apply MemLp.of_bound hm.aestronglyMeasurable (N+1 : ℝ)
  filter_upwards [actualState_onSphere hN β R hR hNR] with ω hω
  change ‖actualState (p := p) β R hR t ω‖≤(N : ℝ)+1
  have hn := (onSphere_iff_norm_sq _).mp (hω t)
  nlinarith [norm_nonneg (actualState (p := p) β R hR t ω),Nat.cast_nonneg (α := ℝ) N,sq_nonneg (N : ℝ)]

theorem actualState_ae_joint (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) :
    actualState (p := p) β R hR t=ᵐ[AnnealedModelLaw.law N p]
      fun ω => jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR ω.1 t ω.2 :=
  annealedGlobal_eq_joint (ρ := AnnealedModelLaw.parameterLaw N p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p) t

theorem driftSquare_expectation_bound (hN : 1≤N) (hp : 0<p) (β : ℝ≥0) :
    Integrable (fun J : Disorder N p => (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2)
      (disorderLaw N p) ∧
      (∫ J : Disorder N p,(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2 ∂disorderLaw N p)≤
        2+2*((β : ℝ)*(p : ℝ))^2*momentCeiling p 2 := by
  have hQ := uniform_real_power_moment hN hp (k := 2) (by norm_num)
  have hQi : Integrable (fun J : Disorder N p => (landscapeNorm N p J)^2) (disorderLaw N p) := by
    simpa only [Real.rpow_two] using hQ.1
  have hQb : (∫ J : Disorder N p,(landscapeNorm N p J)^2 ∂disorderLaw N p)≤momentCeiling p 2 := by
    simpa only [Real.rpow_two] using hQ.2
  have hm : MemLp (landscapeNorm N p) 2 (disorderLaw N p) :=
    (memLp_two_iff_integrable_sq (landscapeNorm_continuous N p).aestronglyMeasurable).mpr hQi
  have hi := ((memLp_const (1 : ℝ)).add (hm.const_mul ((β : ℝ)*(p : ℝ)))).integrable_sq
  refine ⟨hi,?_⟩
  calc
    _≤∫ J : Disorder N p,2+2*((β : ℝ)*(p : ℝ))^2*(landscapeNorm N p J)^2 ∂disorderLaw N p := by
      apply integral_mono hi ((integrable_const (2 : ℝ)).add (hQi.const_mul (2*((β : ℝ)*(p : ℝ))^2)))
      intro J
      change (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2≤
        2+2*((β : ℝ)*(p : ℝ))^2*(landscapeNorm N p J)^2
      nlinarith [sq_nonneg (1-(β : ℝ)*(p : ℝ)*landscapeNorm N p J)]
    _=2+2*((β : ℝ)*(p : ℝ))^2*(∫ J : Disorder N p,(landscapeNorm N p J)^2 ∂disorderLaw N p) := by
      rw [integral_add (integrable_const _) (hQi.const_mul _),integral_const_mul]
      simp
    _≤_ := add_le_add le_rfl (mul_le_mul_of_nonneg_left hQb (by positivity))

@[expose] def incrementCeiling (p : ℕ) (β : ℝ≥0) (t : ℝ≥0) : ℝ :=
  4*(t : ℝ)^2*(1+((β : ℝ)*(p : ℝ))^2*momentCeiling p 2)+4*(t : ℝ)

theorem incrementCeiling_nonneg (p : ℕ) (β t : ℝ≥0) : 0≤ incrementCeiling p β t := by
  unfold incrementCeiling momentCeiling
  positivity

/-- True Gaussian × sphere × Brownian normalized state increments have a
dimension-uniform quadratic-plus-linear time ceiling. -/
theorem actual_increment_secondMoment (hN : 1≤N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    (∫ ω,‖actualState (p := p) β R hR (s+t) ω-actualState β R hR s ω‖^2
      ∂AnnealedModelLaw.law N p)/(N : ℝ)≤ incrementCeiling p β t := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let f : Parameter N p×VectorBrownian.Space N → ℝ := fun ω =>
    ‖jointProcess D β R hR ω.1 (s+t) ω.2-jointProcess D β R hR ω.1 s ω.2‖^2
  have he : (fun ω => ‖actualState (p := p) β R hR (s+t) ω-actualState β R hR s ω‖^2)=ᵐ[
      AnnealedModelLaw.law N p] f := by
    filter_upwards [actualState_ae_joint β R hR (s+t),actualState_ae_joint β R hR s] with ω ha hb
    simp only [f,D,ha,hb]
  have hi : Integrable f (AnnealedModelLaw.law N p) :=
    ((actualState_memLp hN β R hR hNR (s+t)).sub
      (actualState_memLp hN β R hR hNR s)).integrable_norm_pow'.congr he
  have hD := driftSquare_expectation_bound (N := N) hN hp β
  have hDP : Integrable (fun q : Parameter N p => (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^2)
      (AnnealedModelLaw.parameterLaw N p) := hD.1.comp_fst (SphereInitialLaw.sphereLaw N)
  have hP : Integrable (fun q : Parameter N p =>
      (N : ℝ)*(2*(t : ℝ)^2*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^2+4*(t : ℝ)))
      (AnnealedModelLaw.parameterLaw N p) :=
    ((hDP.const_mul (2*(t : ℝ)^2)).add (integrable_const (4*(t : ℝ)))).const_mul (N : ℝ)
  have hpoint : ∀ᵐ q ∂AnnealedModelLaw.parameterLaw N p,
      (∫ ω,f (q,ω) ∂VectorBrownian.law N)≤
        (N : ℝ)*(2*(t : ℝ)^2*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^2+4*(t : ℝ)) := by
    filter_upwards [AnnealedModelLaw.parameter_initial_onSphere hN p] with q hq
    have hh := jointProcess_increment_secondMoment (by omega : 0<N) (VectorBrownian.driver N)
      β R hR hNR q.1 q.2 hq s t
    have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
    simpa only [f,D,mul_comm] using (div_le_iff₀ hn).mp hh
  have hh := integral_mono_ae hi.integral_prod_left hP hpoint
  have hpar : (∫ q : Parameter N p,(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p q.1)^2
      ∂AnnealedModelLaw.parameterLaw N p)=
      ∫ J : Disorder N p,(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2 ∂disorderLaw N p := by
    rw [AnnealedModelLaw.parameterLaw,integral_prod _ hDP]
    simp
  rw [← integral_prod _ hi,
    integral_const_mul,integral_add (hDP.const_mul _) (integrable_const _),
    integral_const_mul,integral_const,probReal_univ,one_smul,hpar] at hh
  rw [integral_congr_ae he]
  apply (div_le_iff₀ (Nat.cast_pos.mpr (by omega : 0<N))).mpr
  rw [mul_comm (incrementCeiling p β t) (N : ℝ)]
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg N)
  calc
    _≤2*(t : ℝ)^2*(2+2*((β : ℝ)*(p : ℝ))^2*momentCeiling p 2)+4*(t : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hD.2 (by positivity)) le_rfl
    _=incrementCeiling p β t := by unfold incrementCeiling;ring

end SphericalAging.ActualStateIncrementMoments
