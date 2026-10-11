module

public import SphericalAging.ActualAnnealedCorrelationIntegral

public section

/-! True finite-N factorization of the physical multiplier/correlation
product. Only correlation concentration is needed: the other factor is
bounded by genuine Gaussian landscape moments. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCorrelationEnergyFactorization
open HardSphereDynamics FiniteModel FiniteCorrelationIto ActualSphereTransition
  ActualAnnealedCorrelationIntegral AnnealedResponseMatrixContraction
  ActualMixedOverlapMean ActualMixedResponseTraceContraction
  ForkEnergyComparison GaussianLandscape GaussianLandscapeMoments ResponseTraceReplacement
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def energyField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0)
    (q : ModelSample N p) : ℝ :=
  Hamiltonian N p q.1.1
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q)/(N : ℝ)

@[expose] def pairField (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0)
    (q : ModelSample N p) : ℝ :=
  overlap (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t q)
    (trajectory (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s q)

lemma energyField_stronglyMeasurable (β R : ℝ≥0) (hR : 0<(R : ℝ)) (t : ℝ≥0) :
    StronglyMeasurable (energyField (N := N) (p := p) β R hR t) :=
  (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable
    ((SphereGibbsEntropy.Hamiltonian_joint_continuous N p).comp_stronglyMeasurable
    ((measurable_fst.comp measurable_fst).stronglyMeasurable.prodMk
      (trajectory_stronglyMeasurable (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t)))

lemma energyField_abs_le_landscape (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t : ℝ≥0) :
    ∀ᵐ q ∂AnnealedModelLaw.law N p,
      |energyField β R hR t q|≤landscapeNorm N p q.1.1 := by
  filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR t] with q hq
  rw [energyField,abs_div,abs_of_pos (show (0 : ℝ)<N from Nat.cast_pos.mpr hN)]
  exact LandscapeDerivatives.Hamiltonian_sphere_bound hN (by omega) q.1.1 _
    ((onSphere_iff_norm_sq _).mp hq)

lemma energyField_memLp_two (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t : ℝ≥0) :
    MemLp (energyField (N := N) (p := p) β R hR t) 2 (AnnealedModelLaw.law N p) := by
  have hQ : MemLp (fun q : ModelSample N p => landscapeNorm N p q.1.1) 2 (AnnealedModelLaw.law N p) :=
    ((landscape_memLp_two hN hp).comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst (VectorBrownian.law N)
  apply hQ.mono' (energyField_stronglyMeasurable β R hR t).aestronglyMeasurable
  simpa only [Real.norm_eq_abs] using energyField_abs_le_landscape hN hp β R hR hNR t

lemma energyField_secondMoment_le (hN : 0<N) (hp : 0<p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (t : ℝ≥0) :
    (∫ q : ModelSample N p,(energyField β R hR t q)^2 ∂AnnealedModelLaw.law N p)≤momentCeiling p 2 := by
  have hE := energyField_memLp_two hN hp β R hR hNR t
  have hQ : MemLp (fun q : ModelSample N p => landscapeNorm N p q.1.1) 2 (AnnealedModelLaw.law N p) :=
    ((landscape_memLp_two hN hp).comp_fst (SphereInitialLaw.sphereLaw N)).comp_fst (VectorBrownian.law N)
  have he : (∫ q : ModelSample N p,(landscapeNorm N p q.1.1)^2 ∂AnnealedModelLaw.law N p)=
      ∫ J : Disorder N p,(landscapeNorm N p J)^2 ∂disorderLaw N p := by
    unfold AnnealedModelLaw.law at hQ ⊢
    rw [integral_prod _ hQ.integrable_sq]
    simp only [integral_const,probReal_univ,one_smul]
    unfold AnnealedModelLaw.parameterLaw
    rw [integral_prod _ ((landscape_memLp_two hN hp).comp_fst (SphereInitialLaw.sphereLaw N)).integrable_sq]
    simp only [integral_const,probReal_univ,one_smul]
  calc
    _≤∫ q : ModelSample N p,(landscapeNorm N p q.1.1)^2 ∂AnnealedModelLaw.law N p :=
      integral_mono_ae hE.integrable_sq hQ.integrable_sq (by
        filter_upwards [energyField_abs_le_landscape hN hp β R hR hNR t] with q hq
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (landscapeNorm_nonnegative _ _ _)).mpr hq)
    _=_ := he
    _≤_ := by simpa only [Real.rpow_two] using
      (uniform_real_power_moment (by omega : 1≤N) hp (k := 2) (by norm_num)).2

lemma pairField_memLp_two (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    MemLp (pairField (N := N) (p := p) β R hR s t) 2 (AnnealedModelLaw.law N p) := by
  have hm := (continuous_id.div_const (N : ℝ)).comp_stronglyMeasurable ((trajectory_stronglyMeasurable (p := p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR t).inner
      (trajectory_stronglyMeasurable (p := p)
        (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s))
  apply MemLp.of_bound hm.aestronglyMeasurable 1
  filter_upwards [trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR t,
    trajectory_onSphere (p := p) hN (VectorBrownian.driver N) β R hR hNR s] with q ht hs
  exact overlap_abs_le_one hN ht hs

lemma pairField_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t T : ℝ≥0)
    (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    (∫ q : ModelSample N p,(pairField β R hR s t q-
      correlationPair (N := N) (p := p) β R hR s t)^2 ∂AnnealedModelLaw.law N p)≤
      ActualCompactJointOverlapVariance.jointVarianceCeiling p β T/(N : ℝ) :=
  actual_mixed_centered_secondMoment_le hN hp β R hR hNR t t T htT htT hT ⟨s,⟨zero_le,hst⟩⟩

 theorem actual_energy_correlation_factorization (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (s t T : ℝ≥0)
    (hst : s≤t) (htT : t≤T) (hT : 0<T) :
    |(∫ q : ModelSample N p,energyField β R hR t q*pairField β R hR s t q ∂AnnealedModelLaw.law N p)-
      (∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)*
        correlationPair (N := N) (p := p) β R hR s t|≤
      Real.sqrt (momentCeiling p 2)*
        Real.sqrt (ActualCompactJointOverlapVariance.jointVarianceCeiling p β T/(N : ℝ)) := by
  have hE := energyField_memLp_two (p := p) (by omega : 0<N) (by omega : 0<p) β R hR hNR t
  have hC := pairField_memLp_two (p := p) (by omega : 0<N) β R hR hNR s t
  have hD : MemLp (fun q : ModelSample N p => pairField β R hR s t q-
      correlationPair (N := N) (p := p) β R hR s t) 2 (AnnealedModelLaw.law N p) :=
    hC.sub (memLp_const _)
  have he : (∫ q : ModelSample N p,energyField β R hR t q*pairField β R hR s t q ∂AnnealedModelLaw.law N p)-
      (∫ q : ModelSample N p,energyField β R hR t q ∂AnnealedModelLaw.law N p)*
        correlationPair (N := N) (p := p) β R hR s t=
      ∫ q : ModelSample N p,energyField β R hR t q*(pairField β R hR s t q-
        correlationPair (N := N) (p := p) β R hR s t) ∂AnnealedModelLaw.law N p := by
    have hEC : Integrable (fun q : ModelSample N p => energyField β R hR t q*pairField β R hR s t q)
        (AnnealedModelLaw.law N p) := by convert hE.integrable_mul hC using 1
    rw [← integral_mul_const,← integral_sub hEC ((hE.integrable (by norm_num)).mul_const _)]
    congr 1
    funext q
    ring
  rw [he]
  exact abs_integral_le_integral_abs.trans ((integral_abs_mul_le_sqrt hE hD).trans
    (mul_le_mul (Real.sqrt_le_sqrt (energyField_secondMoment_le (by omega) (by omega) β R hR hNR t))
      (Real.sqrt_le_sqrt (pairField_centered_secondMoment_le hN hp β R hR hNR s t T hst htT hT))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))

end SphericalAging.ActualCorrelationEnergyFactorization
