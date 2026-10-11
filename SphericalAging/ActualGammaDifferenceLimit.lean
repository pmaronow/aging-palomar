module

public import SphericalAging.GammaDifferenceLimitIdentification
public import SphericalAging.ActualCKGammaDifferenceResidual

public section

/-! The literal actual mean Γ two-terminal row is inherited by every
subsequence with convergent means and a uniform CK slope limit. The true
finite-dimensional defect and integrability are discharged from the model. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualGammaDifferenceLimit
open ActualAnnealedGammaIntegral ActualCKGammaDifferenceResidual
  ActualCKGammaCompactDefect ActualCKGammaSlopeResidual ActualCKGammaUniformResidual
  AnnealedHamiltonianEnergyStein GammaDifferenceLimitIdentification
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {p : ℕ}

/-- Arbitrary diverging dimensions inherit the true two-terminal defect limit. -/
theorem gammaDifferenceResidual_dimension_tendsto_zero {ι : Type*} {l : Filter ι}
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) (t a s : ℝ≥0)
    (hsa : s≤a) (hat : a≤t) (htT : t≤T) :
    Tendsto (fun i => gammaDifferenceResidual (N := dim i)
      (by have := hD i;omega) p β t a s) l (𝓝 0) := by
  have hCeil : Tendsto (gammaCompactDefectCeiling p β T) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 3).mp (gammaCompactDefectCeiling_tendsto_zero p β T)
  have htend : Tendsto (fun i => 2*gammaCompactDefectCeiling p β T (dim i)) l (𝓝 0) :=
    by simpa only [mul_zero,Function.comp_def] using (hCeil.comp hDim).const_mul 2
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [htend.eventually (gt_mem_nhds hε)] with i hi
  rw [Real.dist_eq,sub_zero]
  exact (actual_gamma_difference_residual_uniform (hD i) hp β T hT t a s hsa hat htT).trans_lt hi

/-- The limiting two-terminal Γ row follows from the checked actual finite-N
residual and the preceding uniform slope convergence. -/
theorem actual_gamma_difference_row_limit {ι : Type*} {l : Filter ι} [NeBot l]
    (dim : ι→ℕ) (hDim : Tendsto dim l atTop) (hD : ∀ i,3≤dim i)
    (hp : 3≤p) (β T : ℝ≥0) (hT : 0<T) (t a s : ℝ≥0)
    (hsa : s≤a) (hat : a≤t) (htT : t≤T) {G S : ℝ≥0→ℝ≥0→ℝ}
    (hGt : Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) t s) l (𝓝 (G t s)))
    (hGa : Tendsto (fun i => annealedGammaPair (N := dim i) (p := p) β
      (dim i+1) (modelRadius_pos (dim i)) a s) l (𝓝 (G a s)))
    (hS : IntervalIntegrable (fun u : ℝ => S u.toNNReal s) volume (a : ℝ) (t : ℝ))
    (hSlim : TendstoUniformlyOn (fun i => fun u : ℝ =>
      ckGammaSlope (N := dim i) (by have := hD i;omega) p β u.toNNReal s)
        (fun u : ℝ => S u.toNNReal s) l (uIcc (a : ℝ) (t : ℝ))) :
    G t s-G a s=∫ u in (a : ℝ)..(t : ℝ),S u.toNNReal s := by
  have hSn : ∀ᶠ i in l,IntervalIntegrable (fun u : ℝ =>
      ckGammaSlope (N := dim i) (by have := hD i;omega) p β u.toNNReal s)
        volume (a : ℝ) (t : ℝ) := by
    refine Filter.Eventually.of_forall (fun i => ?_)
    have hi := ckGammaSlope_intervalIntegrable (hD i) hp β s t T (hsa.trans hat) htT hT
    apply hi.mono_set
    rw [uIcc_of_le (show (a : ℝ)≤t from hat),
      uIcc_of_le (show (s : ℝ)≤t from hsa.trans hat)]
    exact Icc_subset_Icc (show (s : ℝ)≤a from hsa) le_rfl
  have hres := gammaDifferenceResidual_dimension_tendsto_zero dim hDim hD hp β T hT t a s hsa hat htT
  have hInt := ResponsePrimitiveLimitIdentification.intervalIntegral_tendsto_of_uniform_integrable
    hSn hS hSlim
  have hh := tendsto_nhds_unique ((hGt.sub hGa).sub hInt) hres
  exact sub_eq_zero.mp hh

end SphericalAging.ActualGammaDifferenceLimit
