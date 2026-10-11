module

public import SphericalAging.AdaptiveTensorDisclosureGradientDirection

public section

/-! Finite-prefix variants for constructing genuine source-history queries
by induction. Current query measurability uses only the previously proved
queries, avoiding a circular assumption about the entire infinite stream. -/
noncomputable section
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveTensorHistoryFinitePrefix
open Set MeasureTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosureAmbient FiniteDisclosureExactHistory
open FiniteDisclosureSourceExtension AdaptiveTensorDisclosureSource
open FiniteDisclosureSpaceMeasurable PredictableGramStep

 theorem exists_actual_prefix_finite {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (j : ℕ)
    (hu : ∀i,i<j→Measurable[MeasurableSpace.comap (History W0 u i) inferInstance] (u i)) :
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
    obtain ⟨P,hSpace,hHistory⟩ := ih (fun i hi => hu i (by omega))
    have huj : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] (u j) := by
      rw [hHistory]
      exact hu j (by omega)
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


theorem history_comap_le_succ {N p : ℕ} {S : Type} [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ) :
    MeasurableSpace.comap (History W0 u j) inferInstance≤
      MeasurableSpace.comap (History W0 u (j+1)) inferInstance := by
  exact MeasurableSpace.comap_le_comap_of_eq_comp Prod.fst measurable_fst rfl

theorem history_comap_mono {N p : ℕ} {S : Type} [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) {i j : ℕ} (hij : i≤j) :
    MeasurableSpace.comap (History W0 u i) inferInstance≤
      MeasurableSpace.comap (History W0 u j) inferInstance := by
  induction j with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i=j+1
    · subst i;exact le_rfl
    · exact (ih (by omega)).trans (history_comap_le_succ W0 u j)

theorem seed_measurable {N p : ℕ} {S : Type} [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (Prod.fst : S×TensorSpace N p→S) := by
  have hH : Measurable[MeasurableSpace.comap (History W0 u 0) inferInstance]
      (History W0 u 0) := Measurable.of_comap_le le_rfl
  have hh0 : Measurable[MeasurableSpace.comap (History W0 u 0) inferInstance]
      (fun z : S×TensorSpace N p => (History W0 u 0 z).1) :=
    (measurable_fst : Measurable (Prod.fst : S×TensorSpace N p→S)).comp hH
  have hh : Measurable[MeasurableSpace.comap (History W0 u 0) inferInstance]
      (Prod.fst : S×TensorSpace N p→S) := by
    simpa only [History,SeedSubspaceDisclosureInitial.initialHistory] using hh0
  exact hh.mono (history_comap_mono W0 u (Nat.zero_le j)) le_rfl

theorem disclosed_measurable_finite {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ)
    (hu : ∀i,i<j→Measurable[MeasurableSpace.comap (History W0 u i) inferInstance] (u i)) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z : S×TensorSpace N p => (residualTensorSpace (Space W0 u j z))ᗮ.starProjection z.2) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix_finite S W0 hW0 u j hu
  have hh := FiniteDisclosureDisclosed.actual_disclosed_measurable_history P
  rw [comap_actualHistory_eq_literal,hHistory] at hh
  simpa only [hSpace] using hh

theorem gradient_measurable_finite {N p : ℕ} (hp : 2≤p) (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ)
    (hu : ∀i,i<j→Measurable[MeasurableSpace.comap (History W0 u i) inferInstance] (u i))
    (x : S×TensorSpace N p→Vector N)
    (hx : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] x)
    (hmem : ∀z,x z∈Space W0 u j z) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => gradient (Hamiltonian N p z.2.ofLp) (x z)) := by
  have hD : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z : S×TensorSpace N p => disclosedDisorder (Space W0 u j z) z.2.ofLp) := by
    simpa only [disclosedDisorder,WithLp.toLp_ofLp,Function.comp_def] using
      ((PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp
        (disclosed_measurable_finite S W0 hW0 u j hu))
  exact GradientDisclosureMeasurability.gradient_measurable_from_disclosure hp
    (Space W0 u j) (fun z => z.2.ofLp) x hD hx hmem

theorem vector_projection_measurable_finite {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ)
    (hu : ∀i,i<j→Measurable[MeasurableSpace.comap (History W0 u i) inferInstance] (u i))
    {y : S×TensorSpace N p→Vector N}
    (hy : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] y) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => (Space W0 u j z).starProjection (y z)) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix_finite S W0 hW0 u j hu
  have hS : MeasurableSpace.comap (actualHistory P) inferInstance=
      MeasurableSpace.comap (History W0 u j) inferInstance :=
    (comap_actualHistory_eq_literal P).trans hHistory
  have hy' : Measurable[MeasurableSpace.comap (actualHistory P) inferInstance] y := by rw [hS];exact hy
  have hh := actual_vector_projection_measurable P hy'
  rw [hS] at hh
  simpa only [hSpace] using hh

theorem unitResidual_measurable_finite {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ)
    (hu : ∀i,i<j→Measurable[MeasurableSpace.comap (History W0 u i) inferInstance] (u i))
    {y : S×TensorSpace N p→Vector N}
    (hy : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] y) :
    Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => unitResidual (Space W0 u j z) (y z)) := by
  have hp := vector_projection_measurable_finite S W0 hW0 u j hu hy
  have hr : Measurable[MeasurableSpace.comap (History W0 u j) inferInstance]
      (fun z => residual (Space W0 u j z) (y z)) := hy.sub hp
  exact ((continuous_norm.measurable.comp hr).inv).smul hr

end SphericalAging.AdaptiveTensorHistoryFinitePrefix
