module

public import SphericalAging.VectorSeedDisclosurePlan

public section

/-! Actual independent seed and ambient Gaussian disorder initialize the
finite seed-vector disclosure with the identity frame and zero past tensor. -/
noncomputable section
namespace SphericalAging.VectorSeedDisclosureInitial
open Set MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics AdaptiveGradientDisclosure
open TensorOrthogonalAction TensorResidualRotation CanonicalVectorSpan
open FiniteDisclosureTree FiniteDisclosurePhysicalState FiniteDisclosureAmbient
open FiniteDisclosureQuerySpan GenericEulerDisclosureMemory
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[expose] def memory (N p : ℕ) (S : Type) [MeasurableSpace S] : Memory N p 0 S where
  frame := initialFrame N S
  frame_measurable := measurable_snd
  disclosed := fun _ => 0
  disclosed_measurable := measurable_const
  disclosed_mem := fun _ => Submodule.zero_mem _
  state := fun _ => 0
  state_measurable := measurable_const
  increments := fun _ _ => 0
  increments_measurable := fun _ => measurable_const

@[expose] def plan {N p : ℕ} (n : ℕ) (S : Type) [MeasurableSpace S]
    (u : ℕ→S→Vector N) (hu : ∀j,Measurable (u j)) : Plan N p n 0 S :=
  VectorSeedDisclosurePlan.plan 0 n 0 S (memory N p S) u hu

theorem vectors_eq_ofFn {N : ℕ} {S : Type} (u : ℕ→S→Vector N) (i n : ℕ) (s : S) :
    VectorSeedDisclosurePlan.vectors u i n s=List.ofFn (fun j : Fin n => u (i+j.val) s) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [VectorSeedDisclosurePlan.vectors,List.ofFn_succ,ih]
    congr 1
    apply congrArg List.ofFn
    funext j
    simp only [Fin.val_succ]
    congr 1 <;> omega

theorem actual_space {N p : ℕ} (n : ℕ) (S : Type) [MeasurableSpace S]
    (u : ℕ→S→Vector N) (hu : ∀j,Measurable (u j)) (z : S×TensorSpace N p) :
    actualSpace (plan (p:=p) n S u hu) z=
      Submodule.span ℝ (Set.range (fun j : Fin n => u j.val z.1)) := by
  have hh := VectorSeedDisclosurePlan.actual_terminal_span 0 n 0 S (memory N p S) u hu (initialState z)
  have hb : rotatedSpace (initialFrame N S z.1) (space N 0)=⊥ := by
    rw [space_zero]
    exact Submodule.map_bot _
  simpa only [actualSpace,actualHistory,Function.comp_def,plan,memory,initialState,hb,
    bot_sup_eq,vectors_eq_ofFn,Nat.zero_add,vectorListSpan,List.mem_ofFn,Set.range] using hh

theorem actual_conditional_gaussian {N p : ℕ} (n : ℕ) (S : Type) [MeasurableSpace S]
    (u : ℕ→S→Vector N) (hu : ∀j,Measurable (u j)) (μ : Measure S) [IsFiniteMeasure μ]
    (φ : TensorSpace N p→ℝ) (hφ : StronglyMeasurable φ) (C : ℝ) (hC : ∀J,‖φ J‖≤C) :
    (μ.prod (stdGaussian (TensorSpace N p)))[(fun z => φ
      ((residualTensorSpace (Submodule.span ℝ (Set.range (fun j : Fin n => u j.val z.1)))).starProjection z.2)) |
      MeasurableSpace.comap (actualHistory (plan (p:=p) n S u hu)) inferInstance]=ᵐ[μ.prod (stdGaussian (TensorSpace N p))]
      fun z => ∫J,φ ((residualTensorSpace (Submodule.span ℝ (Set.range (fun j : Fin n => u j.val z.1)))).starProjection J)
        ∂stdGaussian (TensorSpace N p) := by
  simpa only [actual_space] using actual_projected_conditional_gaussian (plan (p:=p) n S u hu) μ φ hφ C hC

end SphericalAging.VectorSeedDisclosureInitial
