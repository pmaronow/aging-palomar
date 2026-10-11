module

public import SphericalAging.GaussianLinearMixtureLaw
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

public section

/-! The actual Gaussian noise coupling is symmetric, proved by an
explicit measure-preserving reflection of the two independent inputs. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianNoiseSymmetry
open Set MeasureTheory ProbabilityTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def noise (ρ : ℝ) (x y : E) : E := ρ•x+Real.sqrt (1-ρ^2)•y
@[expose] def transform (ρ : ℝ) (z : E×E) : E×E :=
  (noise ρ z.1 z.2,Real.sqrt (1-ρ^2)•z.1-ρ•z.2)

theorem transform_measurePreserving (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1) :
    MeasurePreserving (transform (E:=E) ρ)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
  let O : E≃ₗᵢ[ℝ]E := LinearIsometryEquiv.neg ℝ
  have hneg : MeasurePreserving O (stdGaussian E) (stdGaussian E) :=
    ⟨O.continuous.measurable,stdGaussian_map O⟩
  have hflip : MeasurePreserving (fun z : E×E => (z.1,-z.2))
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) := by
    have hh := (MeasurePreserving.id (stdGaussian E)).prod hneg
    change MeasurePreserving (fun z : E×E => (z.1,-z.2)) _ _ at hh
    exact hh
  have hrot : MeasurePreserving (ContinuousLinearMap.rotation (-Real.arccos ρ) : E×E→E×E)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).prod (stdGaussian E)) :=
    ⟨(ContinuousLinearMap.rotation (-Real.arccos ρ) : E×E→L[ℝ]E×E).measurable,
      IsGaussian.map_rotation_eq_self (μ:=stdGaussian E) integral_id_stdGaussian _⟩
  have he : (ContinuousLinearMap.rotation (-Real.arccos ρ) : E×E→E×E)∘
      (fun z : E×E => (z.1,-z.2))=transform (E:=E) ρ := by
    funext z
    simp only [Function.comp_apply,ContinuousLinearMap.rotation_apply,
      Real.cos_neg,Real.sin_neg,Real.cos_arccos (by linarith : -1≤ρ) h1,
      Real.sin_arccos,smul_neg,neg_smul,neg_neg,transform,noise]
    congr 1 <;> module
  exact he ▸ hrot.comp hflip

theorem noise_transform (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1) (z : E×E) :
    noise ρ (transform ρ z).1 (transform ρ z).2=z.1 := by
  have hs : Real.sqrt (1-ρ^2)^2=1-ρ^2 := Real.sq_sqrt (by nlinarith)
  have he : ρ^2+Real.sqrt (1-ρ^2)^2=1 := by linarith
  dsimp only [noise,transform]
  rw [smul_add,smul_sub,smul_smul,smul_smul,smul_smul,smul_smul]
  have hcross : ρ*Real.sqrt (1-ρ^2)=Real.sqrt (1-ρ^2)*ρ := mul_comm _ _
  rw [←sq,←sq,hcross]
  have he' : ρ^2•z.1+Real.sqrt (1-ρ^2)^2•z.1=z.1 := by rw [←add_smul,he,one_smul]
  calc
    _=ρ^2•z.1+Real.sqrt (1-ρ^2)^2•z.1 := by module
    _=z.1 := he'

/-- Symmetry holds under the literal independent input law, for every
integrable observable of the two correlated Gaussian outputs. -/
theorem actual_noise_pair_integral_swap (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1)
    (f : E×E→ℝ) (hf : Integrable (fun z : E×E => f (z.1,noise ρ z.1 z.2))
      ((stdGaussian E).prod (stdGaussian E))) :
    (∫z : E×E,f (z.1,noise ρ z.1 z.2) ∂(stdGaussian E).prod (stdGaussian E))=
      ∫z : E×E,f (noise ρ z.1 z.2,z.1) ∂(stdGaussian E).prod (stdGaussian E) := by
  have hh := (transform_measurePreserving (E:=E) ρ h0 h1).hasLaw.integral_comp hf.aestronglyMeasurable
  simp only [Function.comp_def,noise_transform ρ h0 h1] at hh
  exact hh.symm

end SphericalAging.GaussianNoiseSymmetry
