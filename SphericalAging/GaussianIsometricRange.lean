module

public import SphericalAging.GaussianSubspaceRegeneration

public section

/-! An actual isometric embedding of a finite standard Gaussian has the
literal law of the ambient standard Gaussian projected onto its range. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianIsometricRange
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

theorem map_isometry_eq_projected {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E→ₗᵢ[ℝ]F) :
    (stdGaussian E).map f=(stdGaussian F).map (LinearMap.range f.toLinearMap).starProjection := by
  let K := LinearMap.range f.toLinearMap
  let e : E≃ₗᵢ[ℝ]K := f.equivRange
  have hf : (f:E→F)=K.subtype∘e := rfl
  have hP : (K.starProjection:F→F)=K.subtype∘K.orthogonalProjectionOnto := rfl
  rw [hf,hP,←Measure.map_map (by fun_prop) (by fun_prop),stdGaussian_map e,
    ←Measure.map_map (by fun_prop) (by fun_prop),GaussianSubspaceRegeneration.projection_law]

theorem integral_isometry_eq_projected {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [MeasurableSpace F] [BorelSpace F] (f : E→ₗᵢ[ℝ]F)
    (φ : F→ℝ) (hφ : StronglyMeasurable φ) :
    (∫x,φ (f x) ∂stdGaussian E)=
      ∫x,φ ((LinearMap.range f.toLinearMap).starProjection x) ∂stdGaussian F := by
  have he : HasLaw f ((stdGaussian E).map f) (stdGaussian E) :=
    ⟨f.continuous.measurable.aemeasurable,rfl⟩
  have hP : HasLaw (LinearMap.range f.toLinearMap).starProjection
      ((stdGaussian F).map (LinearMap.range f.toLinearMap).starProjection) (stdGaussian F) :=
    ⟨(LinearMap.range f.toLinearMap).starProjection.measurable.aemeasurable,rfl⟩
  change (∫x,(φ∘f) x ∂stdGaussian E)=
    ∫x,(φ∘(LinearMap.range f.toLinearMap).starProjection) x ∂stdGaussian F
  rw [he.integral_comp hφ.aestronglyMeasurable,map_isometry_eq_projected,
    ←hP.integral_comp hφ.aestronglyMeasurable]

end SphericalAging.GaussianIsometricRange
