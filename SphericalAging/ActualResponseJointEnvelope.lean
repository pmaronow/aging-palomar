module

public import SphericalAging.ActualResponseJointKernel
public import SphericalAging.SphereSharpMeanDerivative

public section

/-! Genuine landscape exponential envelope for the joint-time backward
response trace, and its exact equality with the canonical response. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualResponseJointEnvelope
open HardSphereDynamics FiniteModel ActualSphereTransition ActualAnnealedCorrelationIntegral
  ActualResponseJointKernel ActualResponseKernel ActualPhysicalBrownianPairing
  ActualQuenchedBrownianPairing AnnealedResponseMatrixContraction
  GaussianLandscape GaussianLandscapeMoments
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma backwardTraceField_abs_le_exp (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H s : ℝ≥0) :
    ∀ᵐ q ∂AnnealedModelLaw.law N p,
      |backwardTraceField β R hR ((H,s),q)|≤
        Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(H : ℝ)) := by
  filter_upwards [trajectory_onSphere (p := p) (by omega : 0<N) (VectorBrownian.driver N)
    β R hR hNR s] with q hq
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  have hRate : 0≤(β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1 := by
    have := landscapeNorm_nonnegative N p q.1.1
    positivity
  have he : Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*((H-s : ℝ≥0) : ℝ))≤
      Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(H : ℝ)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast (tsub_le_self : H-s≤H)) hRate)
  have hj (j : Fin N) : |⟪basisVector j,fderiv ℝ
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.1 (H-s))
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q)
      (projection (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q) (basisVector j))⟫_ℝ|≤
      Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(H : ℝ)) := by
    have hh := SphereSharpMeanDerivative.mean_tangent_derivative_norm_le hN hp
      (VectorBrownian.driver N) β R hR hNR q.1.1 _ (basisVector j) hq
      ((H-s)+1) (H-s) (by simp) (by positivity)
    have hbn : ‖basisVector (N := N) j‖=1 := by simp [basisVector,EuclideanSpace.norm_single]
    have hi := (norm_inner_le_norm (𝕜 := ℝ) (basisVector j) _).trans
      (mul_le_mul_of_nonneg_left hh (norm_nonneg _))
    have hi' : |⟪basisVector j,fderiv ℝ
        (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.1 (H-s))
        (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q)
        (projection (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q) (basisVector j))⟫_ℝ|≤
        Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*((H-s : ℝ≥0) : ℝ)) := by
      simpa only [hbn,mul_one,one_mul,Real.norm_eq_abs] using hi
    exact hi'.trans he
  rw [backwardTraceField,abs_div,abs_of_pos hn]
  apply (div_le_iff₀ hn).mpr
  calc
    _≤∑ j : Fin N,|⟪basisVector j,fderiv ℝ
      (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR q.1.1 (H-s))
      (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q)
      (projection (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q) (basisVector j))⟫_ℝ| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ _j : Fin N,Real.exp (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(H : ℝ)) :=
      Finset.sum_le_sum (fun j _ => hj j)
    _=_ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul];ring

lemma backwardTraceField_integrable (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H s : ℝ≥0) :
    Integrable (fun q : ModelSample N p => backwardTraceField β R hR ((H,s),q)) (AnnealedModelLaw.law N p) := by
  have hm := (backwardTraceField_stronglyMeasurable (N := N) (p := p) β R hR).comp_measurable
    ((measurable_const (a := (H,s))).prodMk measurable_id)
  have he : Integrable (fun q : ModelSample N p => Real.exp
      (((β : ℝ)*(p : ℝ)^2*landscapeNorm N p q.1.1)*(H : ℝ))) (AnnealedModelLaw.law N p) := by
    have h := ((uniform_exponential_moment (by omega : 1≤N) (by omega : 0<p)
      ((β : ℝ)*(p : ℝ)^2*(H : ℝ))).1.comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst (VectorBrownian.law N)
    convert h using 1
    · funext q
      congr 1
      ring
    · rfl
  exact he.mono' hm.aestronglyMeasurable (backwardTraceField_abs_le_exp hN hp β R hR hNR H s)

 theorem responseMeanPair_eq_annealedResponse (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (H : ℝ≥0)
    (s : TwoTimeResponseTimeParameter.WaitingTime H) :
    responseMeanPair (N := N) (p := p) β R hR H s=
      annealedResponse (p := p) (by omega : N≠0) β R hR hNR H s := by
  have hi := backwardTraceField_integrable hN hp β R hR hNR H s
  unfold responseMeanPair AnnealedModelLaw.law
  rw [integral_prod _ hi]
  unfold annealedResponse
  apply integral_congr_ae
  filter_upwards [AnnealedTwoTimeResponseMoments.parameterLaw_onSphere (p := p) (by omega : 0<N)] with q hq
  rw [quenchedResponse_eq_backwardMeanKernel (by omega : N≠0) β R hR hNR H s q hq]
  unfold backwardMeanKernel
  rw [← integral_div]
  rfl

end SphericalAging.ActualResponseJointEnvelope
