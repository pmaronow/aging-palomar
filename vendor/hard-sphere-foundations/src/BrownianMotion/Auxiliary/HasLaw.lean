module


/-
Modified for this project: compatibility adaptations and source-comment cleanup.
Apache-2.0: vendor/LICENSE. Provenance: vendor/PROVENANCE.json.
-/

public import Mathlib.Probability.Distributions.Gaussian.Real

@[expose] public section

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}


section dirac


lemma HasLaw.ae_eq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac

end dirac

end HasLaw

end ProbabilityTheory
