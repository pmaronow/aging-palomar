module

public import SphericalAging.SeedSubspaceGenerators
public import SphericalAging.VectorSeedDisclosureInitial
public import SphericalAging.FiniteDisclosureExactHistory
public import SphericalAging.FiniteDisclosureTheorem

public section

/-! Genuine initialization of adaptive disclosure for every measurable
seed subspace. The frame is constructed from projected coordinate
columns; the conditioning sigma algebra is the literal source F0. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SeedSubspaceDisclosureInitial
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosureAmbient FiniteDisclosureExactHistory
open SeedSubspaceGenerators

@[expose]  def stream {N : ℕ} {S : Type} (W : S→Submodule ℝ (Vector N))
    (j : ℕ) (s : S) : Vector N :=
  if h : j<N then vectors (W s) ⟨j,h⟩ else 0

 theorem stream_measurable {N : ℕ} {S : Type} [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) (j : ℕ) :
    Measurable (stream W j) := by
  classical
  by_cases hj : j<N
  · have he : stream W j=(fun s => vectors (W s) ⟨j,hj⟩) := by funext s; simp only [stream,dif_pos hj]
    rw [he]
    exact vectors_measurable W hW ⟨j,hj⟩
  · have he : stream W j=(fun _ => (0 : Vector N)) := by funext s;simp only [stream,dif_neg hj]
    rw [he]
    exact measurable_const

@[expose]  def plan {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) : Plan N p N 0 S :=
  VectorSeedDisclosureInitial.plan N S (stream W) (stream_measurable W hW)

 theorem actual_space {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (z : S×TensorSpace N p) : actualSpace (plan (p:=p) S W hW) z=W z.1 := by
  have he : (fun j : Fin N => stream W j.val z.1)=vectors (W z.1) := by
    funext j
    simp only [stream,dif_pos j.isLt]
  exact (VectorSeedDisclosureInitial.actual_space N S (stream W) (stream_measurable W hW) z).trans
    (by rw [he,span_range_vectors])

@[expose]  def initialHistory {N p : ℕ} {S : Type} (W : S→Submodule ℝ (Vector N))
    (z : S×TensorSpace N p) : S×TensorSpace N p :=
  (z.1,(residualTensorSpace (W z.1))ᗮ.starProjection z.2)

 theorem comap_history_eq_initial {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) :
    MeasurableSpace.comap (actualHistory (plan (p:=p) S W hW)) inferInstance=
      MeasurableSpace.comap (initialHistory (p:=p) W) inferInstance := by
  have he : literalHistory (plan (p:=p) S W hW)=initialHistory (p:=p) W := by
    funext z
    simp only [literalHistory,initialHistory,actual_space]
  rw [←he]
  exact comap_actualHistory_eq_literal (plan (p:=p) S W hW)

 theorem actual_initial_conditional_gaussian {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2))
    (μ : Measure S) [IsFiniteMeasure μ]
    (φ : TensorSpace N p→ℝ) (hφ : StronglyMeasurable φ) (C : ℝ) (hC : ∀J,‖φ J‖≤C) :
    (μ.prod (stdGaussian (TensorSpace N p)))[(fun z => φ ((residualTensorSpace (W z.1)).starProjection z.2)) |
      MeasurableSpace.comap (initialHistory (p:=p) W) inferInstance]=ᵐ[μ.prod (stdGaussian (TensorSpace N p))]
      fun z => ∫J,φ ((residualTensorSpace (W z.1)).starProjection J) ∂stdGaussian (TensorSpace N p) := by
  rw [←comap_history_eq_initial S W hW]
  simpa only [actual_space] using
    actual_projected_conditional_gaussian (plan (p:=p) S W hW) μ φ hφ C hC

end SphericalAging.SeedSubspaceDisclosureInitial
