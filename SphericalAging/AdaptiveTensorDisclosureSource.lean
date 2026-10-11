module

public import SphericalAging.SeedSubspaceDisclosureInitial
public import SphericalAging.FiniteDisclosureSourceExtension
public import SphericalAging.GradientDisclosureMeasurability

public section

/-! Source Lemma 10.6 for the literal recursively generated disclosure
sigma algebras and arbitrary seed-measurable initial subspace. Every
finite prefix is constructed from original independent Gaussian disorder;
no conditional Gaussian law or random orthogonal frame is an input. -/
noncomputable section
set_option maxHeartbeats 950000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveTensorDisclosureSource
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosureAmbient FiniteDisclosureExactHistory
open FiniteDisclosureSourceExtension

@[expose]  def Space {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) : ℕ→S×TensorSpace N p→Submodule ℝ (Vector N)
  | 0,z => W0 z.1
  | j+1,z => Space W0 u j z⊔ℝ ∙ u j z

@[expose]  def HistoryType (N p : ℕ) (S : Type) : ℕ→Type
  | 0 => S×TensorSpace N p
  | j+1 => HistoryType N p S j×TensorSpace N p

 instance historyMeasurable (N p : ℕ) (S : Type) [MeasurableSpace S] (j : ℕ) :
    MeasurableSpace (HistoryType N p S j) := by
  induction j with
  | zero => exact inferInstanceAs (MeasurableSpace (S×TensorSpace N p))
  | succ j ih =>
    letI := ih
    exact inferInstanceAs (MeasurableSpace (HistoryType N p S j×TensorSpace N p))

@[expose]  def History {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) : (j : ℕ)→S×TensorSpace N p→HistoryType N p S j
  | 0,z => SeedSubspaceDisclosureInitial.initialHistory W0 z
  | j+1,z => (History W0 u j z,
      (residualTensorSpace (Space W0 u j z)⊓(residualTensorSpace (Space W0 u (j+1) z))ᗮ).starProjection z.2)

 theorem exists_actual_prefix {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ) :
    ∃P : Plan N p (N+j) 0 S,
      (∀z,actualSpace P z=Space W0 u j z) ∧
      MeasurableSpace.comap (literalHistory P) inferInstance=
        MeasurableSpace.comap (History W0 u j) inferInstance := by
  induction j with
  | zero =>
    refine ⟨SeedSubspaceDisclosureInitial.plan S W0 hW0,?_,?_⟩
    · exact SeedSubspaceDisclosureInitial.actual_space S W0 hW0
    · exact (comap_actualHistory_eq_literal _).symm.trans
        (SeedSubspaceDisclosureInitial.comap_history_eq_initial S W0 hW0)
  | succ j ih =>
    obtain ⟨P,hSpace,hHistory⟩ := ih
    have huj : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] (u j) := by
      rw [hHistory]
      exact hu j
    refine ⟨extend P (u j) huj,?_,?_⟩
    · intro z
      rw [actual_extended_space,hSpace]
      rfl
    · rw [comap_extendedHistory_eq_step]
      have hb : newBlock P (u j) huj=(fun z : S×TensorSpace N p =>
          (residualTensorSpace (Space W0 u j z)⊓(residualTensorSpace (Space W0 u (j+1) z))ᗮ).starProjection z.2) := by
        funext z
        simp only [newBlock,actual_extended_space,hSpace,Space]
      change MeasurableSpace.comap (fun z => (literalHistory P z,newBlock P (u j) huj z)) inferInstance=
        MeasurableSpace.comap (fun z => (History W0 u j z,
          (residualTensorSpace (Space W0 u j z)⊓(residualTensorSpace (Space W0 u (j+1) z))ᗮ).starProjection z.2)) inferInstance
      calc
        _=MeasurableSpace.comap (literalHistory P) inferInstance⊔
            MeasurableSpace.comap (newBlock P (u j) huj) inferInstance :=
          MeasurableSpace.comap_prodMk _ _
        _=MeasurableSpace.comap (History W0 u j) inferInstance⊔
            MeasurableSpace.comap (fun z : S×TensorSpace N p =>
              (residualTensorSpace (Space W0 u j z)⊓(residualTensorSpace (Space W0 u (j+1) z))ᗮ).starProjection z.2) inferInstance := by
          rw [hHistory,hb]
        _=_ := (MeasurableSpace.comap_prodMk _ _).symm

 theorem conditional_gaussian {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j))
    (μ : Measure S) [IsFiniteMeasure μ] (j : ℕ)
    (φ : TensorSpace N p→ℝ) (hφ : StronglyMeasurable φ) (C : ℝ) (hC : ∀J,‖φ J‖≤C) :
    (μ.prod (stdGaussian (TensorSpace N p)))[(fun z => φ ((residualTensorSpace (Space W0 u j z)).starProjection z.2)) |
      MeasurableSpace.comap (History W0 u j) inferInstance]=ᵐ[μ.prod (stdGaussian (TensorSpace N p))]
      fun z => ∫J,φ ((residualTensorSpace (Space W0 u j z)).starProjection J) ∂stdGaussian (TensorSpace N p) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix S W0 hW0 u hu j
  simpa only [hSpace,hHistory] using actual_projected_conditional_gaussian_literal P μ φ hφ C hC

 theorem disclosed_measurable {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z : S×TensorSpace N p => (residualTensorSpace (Space W0 u j z))ᗮ.starProjection z.2) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix S W0 hW0 u hu j
  have hh := FiniteDisclosureDisclosed.actual_disclosed_measurable_history P
  rw [comap_actualHistory_eq_literal,hHistory] at hh
  simpa only [hSpace] using hh

 theorem gradient_measurable {N p : ℕ} (hp : 2≤p) (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ)
    (x : S×TensorSpace N p→Vector N)
    (hx : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] x)
    (hmem : ∀z,x z∈Space W0 u j z) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => gradient (Hamiltonian N p z.2.ofLp) (x z)) := by
  have hD : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z : S×TensorSpace N p => disclosedDisorder (Space W0 u j z) z.2.ofLp) := by
    simpa only [disclosedDisorder,WithLp.toLp_ofLp,Function.comp_def] using
      ((PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp
        (disclosed_measurable S W0 hW0 u hu j))
  exact GradientDisclosureMeasurability.gradient_measurable_from_disclosure hp
    (Space W0 u j) (fun z => z.2.ofLp) x hD hx hmem

end SphericalAging.AdaptiveTensorDisclosureSource
