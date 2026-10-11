module

public import SphericalAging.ActualCompactJointOverlapVariance
public import SphericalAging.AnnealedGlobalSDE

public section

/-! The full-law overlap variance bound concerns the literal constructed
annealed physical SDE. Its equality to the jointly measurable process
family is proved by actual strong-solution uniqueness. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualModelOverlapVariance
open FiniteModel HardSphereDynamics AnnealedCutoffProcess ActualSphereBackwardIto
open ActualCompactOverlapInnovation ActualCompactJointOverlapVariance
open ActualBackgroundOverlapLaw ActualSphereMarkovRestart
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def actualOverlap (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0)
    (ω : Parameter N p × VectorBrownian.Space N) : ℝ :=
  ⟪AnnealedGlobalSDE.globalProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR (AnnealedModelLaw.parameter_disorder_memLp N p) s ω,
    AnnealedGlobalSDE.globalProcess (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR (AnnealedModelLaw.parameter_disorder_memLp N p) t ω⟫_ℝ/(N : ℝ)

theorem actualOverlap_ae_joint (β R : ℝ≥0) (hR : 0<(R : ℝ)) (s t : ℝ≥0) :
    actualOverlap (p := p) β R hR s t=ᵐ[AnnealedModelLaw.law N p]
      jointOverlap (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s t := by
  filter_upwards [annealedGlobal_eq_joint (ρ := AnnealedModelLaw.parameterLaw N p)
    (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
    (AnnealedModelLaw.parameter_disorder_memLp N p) s,
    annealedGlobal_eq_joint (ρ := AnnealedModelLaw.parameterLaw N p)
      (NullAugmentation.driver (VectorBrownian.driver N)) β R hR
      (AnnealedModelLaw.parameter_disorder_memLp N p) t] with ω hs ht
  simp only [actualOverlap,jointOverlap,hs,ht]

theorem actualOverlap_memLp (hN : 3≤N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (s t : ℝ≥0) :
    MemLp (actualOverlap (p := p) β R hR s t) 2 (AnnealedModelLaw.law N p) := by
  let f := jointOverlap (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s t
  have hf := jointOverlap_stronglyMeasurable (p := p) (NullAugmentation.driver (VectorBrownian.driver N)) β R hR s t
  have hn : 0<N := by omega
  have hY (a : ℝ≥0) : Measurable (fun q : Parameter N p × VectorBrownian.Space N =>
      ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR q.1 a q.2) :=
    ((ActualSphereTransition.jointProcess_measurable (NullAugmentation.driver (VectorBrownian.driver N))
      β R hR).comp_measurable (measurable_fst.prodMk (measurable_const.prodMk measurable_snd))).measurable
  have hsp : ∀ᵐ q ∂AnnealedModelLaw.law N p,
      OnSphere (ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR q.1 s q.2) ∧
      OnSphere (ActualSphereTransition.jointProcess (NullAugmentation.driver (VectorBrownian.driver N))
        β R hR q.1 t q.2) := by
    have hm := (ActualSphereKernelSupport.measurableSet_onSphere.preimage (hY s)).inter
      (ActualSphereKernelSupport.measurableSet_onSphere.preimage (hY t))
    apply (Measure.ae_prod_iff_ae_ae hm).mpr
    filter_upwards [AnnealedModelLaw.parameter_initial_onSphere (by omega : 1≤N) p] with q hq
    exact (ActualSphereTransition.jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N)
      β R hR hNR q.1 q.2 hq).mono (fun ω h => ⟨h s,h t⟩)
  have hfm : MemLp f 2 (AnnealedModelLaw.law N p) := MemLp.of_bound hf.aestronglyMeasurable 1
    (hsp.mono (fun q hq => by
      simpa only [f,jointOverlap,FiniteCorrelationIto.overlap,Real.norm_eq_abs] using
        FiniteCorrelationIto.overlap_abs_le_one hn hq.1 hq.2))
  exact hfm.ae_eq (actualOverlap_ae_joint β R hR s t).symm

theorem actual_model_overlap_variance (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T)
    (hreg : ∀ J : Disorder N p,SpatialC2Transition β R hR J (compactOverlapTest β R hR J u)) :
    variance (actualOverlap (p := p) β R hR s (s+u)) (AnnealedModelLaw.law N p)≤
      jointVarianceCeiling p β T/(N : ℝ) := by
  rw [variance_congr (actualOverlap_ae_joint β R hR s (s+u))]
  exact actual_joint_overlap_variance hN hp β R hR hNR s u T hsu hT hreg

theorem actual_model_overlap_deviation_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T)
    (hreg : ∀ J : Disorder N p,SpatialC2Transition β R hR J (compactOverlapTest β R hR J u))
    (ε : ℝ) (hε : 0<ε) :
    (AnnealedModelLaw.law N p) {ω | ε≤|actualOverlap β R hR s (s+u) ω-
      ∫ z,actualOverlap β R hR s (s+u) z ∂AnnealedModelLaw.law N p|}≤
      ENNReal.ofReal (jointVarianceCeiling p β T/((N : ℝ)*ε^2)) := by
  refine (meas_ge_le_variance_div_sq (actualOverlap_memLp hN β R hR hNR s (s+u)) hε).trans ?_
  apply ENNReal.ofReal_le_ofReal
  refine (div_le_div_of_nonneg_right
    (actual_model_overlap_variance hN hp β R hR hNR s u T hsu hT hreg) (sq_nonneg ε)).trans_eq ?_
  ring

end SphericalAging.ActualModelOverlapVariance
