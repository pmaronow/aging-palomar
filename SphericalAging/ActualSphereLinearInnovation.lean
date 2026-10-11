module

public import SphericalAging.ActualSphereLinearTransition
public import SphericalAging.ActualSphereBackwardVarianceBound

public section

/-! Sharp genuine Brownian innovation bounds for linear physical observables. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualSphereLinearInnovation
open HardSphereDynamics LocalSDE ActualSphereTransition AnnealedSDECore
open ActualSphereLinearTransition ActualSphereBackwardIto ActualSphereBackwardVarianceBound
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

/-- Actual linear Brownian innovation, conditional only on the explicit
spatial C² regularity of its actual transition. The sharp gradient estimate
is derived from the genuine tangent response rather than supplied. -/
theorem linear_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    (a : State N) (hreg : SpatialC2Transition β R hR J (fun y => ⟪a,y⟫_ℝ)) :
    (∫ ω,(⟪a,X T ω⟫_ℝ-⟪a,mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J T (Z0 ω)⟫_ℝ)^2 ∂VectorBrownian.law N)≤
      2*‖a‖^2*T*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := by
  let C : ℝ := (β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J
  have hC : 0≤C := mul_nonneg (mul_nonneg β.coe_nonneg (sq_nonneg _))
    (GaussianLandscape.landscapeNorm_nonnegative N p J)
  have hn : N≠0 := by omega
  have hb := backward_transition_variance_le hn β R hR hNR J X T hX hSphere
    (f := fun y => ⟪a,y⟫_ℝ) (innerSL ℝ a).contDiff hreg (‖a‖*Real.exp (C*T)) (by positivity)
    (fun u hu x hx v =>
      (transition_inner_tangent_derivative_norm_le hN hp (VectorBrownian.driver N) β R hR hNR J
        u a x v hx).trans (by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast hu) hC)))
  simp only [transition_inner_eq_mean] at hb
  convert hb using 1
  simp only [mul_pow,← Real.exp_nat_mul,Nat.cast_ofNat]
  rw [show (2 : ℝ)*(C*(T : ℝ))=2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*(T : ℝ) by
    dsimp only [C];ring]
  ring

/-- For a physical fixed observation vector of norm √N, the normalized
future overlap innovation has the actual O(1/N) Brownian variance bound. -/
theorem normalized_linear_innovation_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : FiniteModel.Disorder N p)
    {Z0 : VectorBrownian.Space N → State N}
    (X : ℝ≥0 → VectorBrownian.Space N → State N) (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ t,OnSphere (X t ω))
    (a : State N) (ha : OnSphere a)
    (hreg : SpatialC2Transition β R hR J (fun y => ⟪(N : ℝ)⁻¹ • a,y⟫_ℝ)) :
    (∫ ω,((⟪a,X T ω⟫_ℝ-⟪a,mean (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR J T (Z0 ω)⟫_ℝ)/(N : ℝ))^2 ∂VectorBrownian.law N)≤
      (2*T/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := by
  have hn : (N : ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
  have hn0 : 0≤(N : ℝ) := Nat.cast_nonneg _
  have hs : ‖a‖^2=(N : ℝ) := by simpa only [OnSphere,real_inner_self_eq_norm_sq] using ha
  have hb := linear_innovation_variance_le hN hp β R hR hNR J X T hX hSphere ((N : ℝ)⁻¹ • a) hreg
  have hfun : (fun ω => (⟪(N : ℝ)⁻¹ • a,X T ω⟫_ℝ-
      ⟪(N : ℝ)⁻¹ • a,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J T (Z0 ω)⟫_ℝ)^2)=
      fun ω => ((⟪a,X T ω⟫_ℝ-⟪a,mean (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR J T (Z0 ω)⟫_ℝ)/(N : ℝ))^2 := by
    funext ω
    simp only [real_inner_smul_left,div_eq_mul_inv]
    ring
  rw [hfun,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hn0),mul_pow,hs] at hb
  convert hb using 1 <;> field_simp [hn] <;> ring

end SphericalAging.ActualSphereLinearInnovation
