module

public import SphericalAging.OrthogonalGaussianDisclosure

public section

/-! A Gaussian residual remains fresh under a measurable orthogonal change
of coordinates chosen from the already disclosed data. The rotation law is
proved from the actual product law, not assumed as a conditional Gaussian
receipt. -/
noncomputable section
set_option maxHeartbeats 1300000
namespace SphericalAging.AdaptiveGaussianRotation
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open OrthogonalGaussianDisclosure
open scoped Topology InnerProductSpace

variable {S E : Type*} [MeasurableSpace S]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

 theorem rotation_preserves_product (μ : Measure S) [SFinite μ]
    (U : S→E≃ₗᵢ[ℝ]E) (hm : Measurable (fun z : S×E => U z.1 z.2)) :
    MeasurePreserving (fun z : S×E => (z.1,U z.1 z.2))
      (μ.prod (stdGaussian E)) (μ.prod (stdGaussian E)) := by
  exact (MeasurePreserving.id μ).skew_product (μc:=stdGaussian E) (μd:=stdGaussian E)
    (g:=fun s x => U s x) hm
    (ae_of_all _ (fun s => stdGaussian_map (U s)))

 theorem rotated_residual_pair_law {N p : ℕ} (T : Submodule ℝ (TensorSpace N p))
    (U : Tᗮ→T≃ₗᵢ[ℝ]T) (hm : Measurable (fun z : Tᗮ×T => U z.1 z.2)) :
    (disorderLaw N p).map (fun J : Disorder N p =>
      (Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J),
        U (Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J))
          (T.orthogonalProjectionOnto (WithLp.toLp 2 J))))=
      (stdGaussian Tᗮ).prod (stdGaussian T) := by
  let P := fun J : Disorder N p => (Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J),
    T.orthogonalProjectionOnto (WithLp.toLp 2 J))
  have hp : (disorderLaw N p).map P=(stdGaussian Tᗮ).prod (stdGaussian T) := by
    rw [(tensor_subtype_projections_independent T).symm.map_prod_eq_prod_map_map (by fun_prop) (by fun_prop),
      (ordered_projection_hasLaw Tᗮ).map_eq,(ordered_projection_hasLaw T).map_eq]
  have hr := (rotation_preserves_product (stdGaussian Tᗮ) U hm).map_eq
  rw [←hp,Measure.map_map (measurable_fst.prodMk hm) (by fun_prop)] at hr
  exact hr.trans hp

 theorem rotated_residual_independent {N p : ℕ} (T : Submodule ℝ (TensorSpace N p))
    (U : Tᗮ→T≃ₗᵢ[ℝ]T) (hm : Measurable (fun z : Tᗮ×T => U z.1 z.2)) :
    IndepFun (fun J : Disorder N p => Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J))
      (fun J : Disorder N p => U (Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J))
        (T.orthogonalProjectionOnto (WithLp.toLp 2 J))) (disorderLaw N p) := by
  have hp := rotated_residual_pair_law T U hm
  let X := fun J : Disorder N p => Tᗮ.orthogonalProjectionOnto (WithLp.toLp 2 J)
  let Y := fun J : Disorder N p => U (X J) (T.orthogonalProjectionOnto (WithLp.toLp 2 J))
  have hx : Measurable X := by fun_prop
  have hy : Measurable Y := hm.comp (hx.prodMk (by fun_prop))
  have hY : (disorderLaw N p).map Y=stdGaussian T := by
    have hh := congrArg (Measure.map Prod.snd) hp
    rw [Measure.map_map measurable_snd (hx.prodMk hy),Measure.map_snd_prod,measure_univ,one_smul] at hh
    exact hh
  exact (indepFun_iff_map_prod_eq_prod_map_map hx.aemeasurable hy.aemeasurable).mpr (by
    rw [(ordered_projection_hasLaw Tᗮ).map_eq,hY]
    exact hp)

end SphericalAging.AdaptiveGaussianRotation
