module

public import SphericalAging.FiniteDisclosureDisclosed
public import SphericalAging.FiniteDisclosureQuerySpan

public section

/-! The two complete finite adaptive disclosure conclusions for actual
ambient Gaussian disorder and the literal span of its actual queries. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureTheorem
open Set Filter MeasureTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureAmbient FiniteDisclosureDisclosed FiniteDisclosureQuerySpan

 theorem actual_gradient_measurable_history {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (hp : 2≤p) (P : Plan N p n 0 S) {y : S×TensorSpace N p→Vector N}
    (hy : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] y)
    (hmem : ∀z,y z∈actualSpace P z) :
    Measurable[MeasurableSpace.comap (actualHistory P) inferInstance]
      (fun z : S×TensorSpace N p => gradient (Hamiltonian N p z.2.ofLp) (y z)) := by
  have hD : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance]
      (fun z : S×TensorSpace N p => disclosedDisorder (actualSpace P z) z.2.ofLp) := by
    simpa only [disclosedDisorder,WithLp.toLp_ofLp,Function.comp_def] using
      ((PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp
        (actual_disclosed_measurable_history P))
  exact GradientDisclosureMeasurability.gradient_measurable_from_disclosure hp
    (actualSpace P) (fun z => z.2.ofLp) y hD hy hmem

 theorem actual_span_eq_generated_queries {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (z : S×TensorSpace N p) :
    actualSpace P z=vectorListSpan (queries N p n 0 S P (initialFrame N S) (initialState z)) := by
  have hh := actual_terminal_query_span N p n 0 S P (initialFrame N S) (initialState z)
  simpa only [actualSpace,actualHistory,Function.comp_def,CanonicalVectorSpan.space_zero,
    TensorResidualRotation.rotatedSpace,Submodule.map_bot,bot_sup_eq] using hh

end SphericalAging.FiniteDisclosureTheorem
