module

public import SphericalAging.ActualMeanKernelExtraction
public import SphericalAging.ActualResponsePrimitiveInterchange

public section

/-! The compact extraction concerns the exact correlation and Γ kernels
in the closed finite-N CK rows, at the genuine canonical model radius. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.ActualCanonicalMeanKernelExtraction
open HardSphereDynamics ActualModelOverlapVariance ActualMeanKernelTimeCompactness
  ActualMeanKernelExtraction ActualAnnealedCorrelationIntegral ActualAnnealedGammaIntegral
  ActualResponsePrimitiveInterchange ActualBackgroundOverlapLaw AnnealedResponseMatrixContraction
  AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

lemma overlapMean_eq_correlationPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (z : ℝ≥0×ℝ≥0) :
    overlapMean (N := N) (p := p) β R hR z=
      correlationPair (N := N) (p := p) β R hR z.1 z.2 := by
  unfold overlapMean correlationPair
  apply integral_congr_ae
  filter_upwards [actualOverlap_ae_joint (N := N) (p := p) β R hR z.1 z.2] with q hq
  rw [hq]
  simp only [jointOverlap,trajectory,FiniteCorrelationIto.overlap,real_inner_comm]

lemma gammaMean_eq_annealedGammaPair (β R : ℝ≥0) (hR : 0<(R : ℝ)) (z : ℝ≥0×ℝ≥0) :
    gammaMean (N := N) (p := p) β R hR z=
      annealedGammaPair (N := N) (p := p) β R hR z.1 z.2 :=
  (annealedGammaPair_eq_actualMean β R hR z.1 z.2).symm

 theorem actual_canonical_means_common_subsequence (dim : ℕ→ℕ) (hD : ∀n,1≤dim n)
    (p : ℕ) (hp : 0<p) (β : ℝ≥0) :
    ∃c g : C(ℝ≥0×ℝ≥0,ℝ),∃φ : ℕ→ℕ,StrictMono φ ∧
      ∀K : Set (ℝ≥0×ℝ≥0),IsCompact K →
        TendstoUniformlyOn (fun n z => correlationPair (N := dim (φ n)) (p := p) β
          (dim (φ n)+1) (modelRadius_pos (dim (φ n))) z.1 z.2) c atTop K ∧
        TendstoUniformlyOn (fun n z => annealedGammaPair (N := dim (φ n)) (p := p) β
          (dim (φ n)+1) (modelRadius_pos (dim (φ n))) z.1 z.2) g atTop K := by
  obtain ⟨c,g,φ,hφ,hlim⟩ := actual_means_common_subsequence dim hD p hp β
    (fun n => dim n+1) (fun n => modelRadius_pos (dim n)) (fun n => modelRadius_sq (dim n))
  refine ⟨c,g,φ,hφ,?_⟩
  intro K hK
  refine ⟨(hlim K hK).1.congr ?_,(hlim K hK).2.congr ?_⟩
  · exact Eventually.of_forall (fun n z _ => overlapMean_eq_correlationPair β
      (dim (φ n)+1) (modelRadius_pos (dim (φ n))) z)
  · exact Eventually.of_forall (fun n z _ => gammaMean_eq_annealedGammaPair β
      (dim (φ n)+1) (modelRadius_pos (dim (φ n))) z)

end SphericalAging.ActualCanonicalMeanKernelExtraction
