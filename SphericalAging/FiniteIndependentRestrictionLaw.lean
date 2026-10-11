module

public import Mathlib.Probability.Independence.Basic

public section

/-! Restricting a genuine finite iid sample along an injective index map
preserves its product law. The coordinates' independence is proved from the
original product measure; no restriction-law premise is assumed. -/

noncomputable section
open MeasureTheory ProbabilityTheory

namespace SphericalAging.FiniteIndependentRestrictionLaw

variable {G : Type*} [MeasurableSpace G] {k K : ℕ}

theorem restriction_measurable (σ : Fin k ↪ Fin K) :
    Measurable (fun z : Fin K → G => fun i : Fin k => z (σ i)) :=
  Measurable.of_eval (fun i => measurable_pi_apply (σ i))

/-- The actual pushforward of the finite iid sample is the smaller iid law,
including empty index sets and arbitrary measurable state spaces. -/
theorem restriction_map (μ : Measure G) [IsProbabilityMeasure μ]
    (σ : Fin k ↪ Fin K) :
    (Measure.pi (fun _ : Fin K => μ)).map
      (fun z : Fin K → G => fun i : Fin k => z (σ i)) =
        Measure.pi (fun _ : Fin k => μ) := by
  have hIndependent : iIndepFun
      (fun i : Fin K => fun z : Fin K → G => z i)
      (Measure.pi (fun _ : Fin K => μ)) := by
    simpa only [id_eq] using
      (iIndepFun_pi (μ := fun _ : Fin K => μ) (X := fun _ => id)
        (fun _ => aemeasurable_id))
  have hRestriction := hIndependent.precomp (g := σ) σ.injective
  have hMap := hRestriction.map_fun_eq_pi_map
    (fun i => (measurable_pi_apply (σ i)).aemeasurable)
  have hEval (i : Fin k) :
      (Measure.pi (fun _ : Fin K => μ)).map (fun z : Fin K → G => z (σ i)) = μ :=
    (measurePreserving_eval (fun _ : Fin K => μ) (σ i)).map_eq
  simpa only [hEval] using hMap

/-- Injectively selected coordinates of a finite iid family genuinely have
the corresponding finite product law. -/
theorem restriction_measurePreserving (μ : Measure G) [IsProbabilityMeasure μ]
    (σ : Fin k ↪ Fin K) :
    MeasurePreserving (fun z : Fin K → G => fun i : Fin k => z (σ i))
      (Measure.pi (fun _ : Fin K => μ)) (Measure.pi (fun _ : Fin k => μ)) :=
  ⟨restriction_measurable σ, restriction_map μ σ⟩

end SphericalAging.FiniteIndependentRestrictionLaw
