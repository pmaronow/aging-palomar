module

public import SphericalAging.AdaptiveTensorDisclosureSource
public import SphericalAging.FiniteDisclosureSpaceMeasurable

public section

/-! The literal gradient direction allowed in source Lemma 10.6 is
measurable in the current source history, orthogonal to the current span,
and is exactly zero or a unit vector. -/
noncomputable section
set_option maxHeartbeats 750000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveTensorDisclosureGradientDirection
open MeasureTheory FiniteModel AdaptiveGradientDisclosure PredictableGramStep
open FiniteDisclosureTree FiniteDisclosureAmbient FiniteDisclosureExactHistory
open AdaptiveTensorDisclosureSource FiniteDisclosureSpaceMeasurable

 theorem vector_projection_measurable {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ)
    {y : S×TensorSpace N p→Vector N}
    (hy : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] y) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => (Space W0 u j z).starProjection (y z)) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix S W0 hW0 u hu j
  have hS : MeasurableSpace.comap (actualHistory P) inferInstance=
      MeasurableSpace.comap (History W0 u j) inferInstance :=
    (comap_actualHistory_eq_literal P).trans hHistory
  have hy' : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] y := by rw [hS];exact hy
  have hh := actual_vector_projection_measurable P hy'
  rw [hS] at hh
  simpa only [hSpace] using hh

@[expose]  def direction {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ) (x : S×TensorSpace N p→Vector N)
    (z : S×TensorSpace N p) : Vector N :=
  unitResidual (Space W0 u j z) (gradient (Hamiltonian N p z.2.ofLp) (x z))

 theorem direction_measurable {N p : ℕ} (hp : 2≤p) (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ)
    (x : S×TensorSpace N p→Vector N)
    (hx : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] x)
    (hmem : ∀z,x z∈Space W0 u j z) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (direction W0 u j x) := by
  have hg := gradient_measurable hp S W0 hW0 u hu j x hx hmem
  have hpj := vector_projection_measurable S W0 hW0 u hu j hg
  have hr : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => residual (Space W0 u j z) (gradient (Hamiltonian N p z.2.ofLp) (x z))) := hg.sub hpj
  exact ((continuous_norm.measurable.comp hr).inv).smul hr

 theorem direction_orthogonal {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ) (x : S×TensorSpace N p→Vector N)
    (z : S×TensorSpace N p) : direction W0 u j x z∈(Space W0 u j z)ᗮ :=
  unitResidual_mem_orthogonal _ _

 theorem direction_zero_or_unit {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ) (x : S×TensorSpace N p→Vector N)
    (z : S×TensorSpace N p) : direction W0 u j x z=0 ∨ ‖direction W0 u j x z‖=1 := by
  classical
  by_cases hg : gradient (Hamiltonian N p z.2.ofLp) (x z)∈Space W0 u j z
  · left
    have hr := (residual_eq_zero_iff (Space W0 u j z) _).mpr hg
    simp only [direction,unitResidual,hr,smul_zero]
  · right
    exact unitResidual_norm hg

end SphericalAging.AdaptiveTensorDisclosureGradientDirection
