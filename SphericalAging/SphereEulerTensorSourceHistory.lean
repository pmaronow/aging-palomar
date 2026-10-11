module

public import SphericalAging.AdaptiveTensorHistoryFinitePrefix
public import SphericalAging.SphereEulerSeedSpan

public section

/-! A genuine source-history query stream for the clipped Euler recursion.
Each query direction is the normalized orthogonal residual of the actual
queried gradient. Queries stop after the prescribed finite mesh. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.SphereEulerTensorSourceHistory
open Set MeasureTheory FiniteModel HardSphereDynamics PredictableGramStep AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveTensorHistoryFinitePrefix
open scoped InnerProductSpace
variable {N p : ℕ} {S : Type} [MeasurableSpace S]

@[expose] def initial (x : S→State N) (inc : ℕ→S→State N) (M : ℕ) (s : S) : Submodule ℝ (State N) :=
  Submodule.span ℝ (SphereEulerSeedSpan.seedGenerators (x s) (fun j => inc j s) M : Set (State N))

@[expose] def rawState (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N)
    (j : ℕ) (z : S×TensorSpace N p) : State N :=
  SphereEulerQuerySpan.state β h z.2.ofLp (x z.1) (fun i => inc i z.1) j

@[expose] def rawQuery (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N)
    (j : ℕ) (z : S×TensorSpace N p) : State N := SphereEulerCoefficients.clip (rawState β h x inc j z)

@[expose] def rawGradient (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N)
    (j : ℕ) (z : S×TensorSpace N p) : State N := hamiltonianGradient z.2.ofLp (rawQuery β h x inc j z)

@[expose] def actualSpace (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N)
    (M j : ℕ) (z : S×TensorSpace N p) : Submodule ℝ (State N) :=
  SphereEulerSeedSpan.space β h z.2.ofLp (x z.1) (fun i => inc i z.1) M j

@[expose] def direction (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N)
    (M j : ℕ) (z : S×TensorSpace N p) : State N :=
  if j<M then unitResidual (actualSpace β h x inc M j z) (rawGradient β h x inc j z) else 0

theorem sup_span_unitResidual_all (W : Submodule ℝ (State N)) (v : State N) :
    W⊔ℝ ∙ unitResidual W v=W⊔ℝ ∙ v := by
  classical
  by_cases hv : v∈W
  · have hr : residual W v=0 := (residual_eq_zero_iff W v).mpr hv
    have hu : unitResidual W v=0 := by simp only [unitResidual,hr,smul_zero]
    rw [hu,Submodule.span_zero_singleton,sup_bot_eq]
    exact (sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem v W).mpr hv)).symm
  · exact PredictableTensorSpanIdentification.sup_span_unitResidual W hv

theorem sourceSpace_eq (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N) (M j : ℕ)
    (z : S×TensorSpace N p) :
    Space (initial x inc M) (direction β h x inc M) j z=actualSpace β h x inc M (min j M) z := by
  classical
  induction j with
  | zero =>
    simp only [Space,Nat.zero_min,actualSpace,SphereEulerSeedSpan.space,
      SphereEulerSeedSpan.generators,Finset.range_zero,Finset.image_empty,Finset.union_empty,initial]
  | succ j ih =>
    by_cases hj : j<M
    · rw [Space,ih,Nat.min_eq_left (Nat.le_of_lt hj),direction,if_pos hj,
        sup_span_unitResidual_all,Nat.min_eq_left (by omega)]
      exact (SphereEulerSeedSpan.space_succ_eq β h z.2.ofLp (x z.1) (fun i => inc i z.1) M j).symm
    · rw [Space,ih,Nat.min_eq_right (by omega),direction,if_neg hj,
        Submodule.span_zero_singleton,sup_bot_eq,Nat.min_eq_right (by omega)]

theorem direction_orthogonal (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N) (M j : ℕ)
    (z : S×TensorSpace N p) :
    direction β h x inc M j z∈(Space (initial x inc M) (direction β h x inc M) j z)ᗮ := by
  classical
  rw [sourceSpace_eq]
  by_cases hj : j<M
  · rw [direction,if_pos hj,Nat.min_eq_left (Nat.le_of_lt hj)]
    exact unitResidual_mem_orthogonal _ _
  · rw [direction,if_neg hj]
    exact Submodule.zero_mem _

theorem direction_zero_or_unit (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N) (M j : ℕ)
    (z : S×TensorSpace N p) : direction β h x inc M j z=0 ∨ ‖direction β h x inc M j z‖=1 := by
  classical
  by_cases hj : j<M
  · rw [direction,if_pos hj]
    by_cases hv : rawGradient β h x inc j z∈actualSpace β h x inc M j z
    · left
      simp only [unitResidual,(residual_eq_zero_iff _ _).mpr hv,smul_zero]
    · exact Or.inr (unitResidual_norm hv)
  · exact Or.inl (by rw [direction,if_neg hj])

theorem rawQuery_mem (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N) (M j : ℕ)
    (hj : j≤M) (z : S×TensorSpace N p) :
    rawQuery β h x inc j z∈Space (initial x inc M) (direction β h x inc M) j z := by
  rw [sourceSpace_eq,Nat.min_eq_left hj]
  exact SphereEulerSeedSpan.query_mem β h z.2.ofLp (x z.1) (fun i => inc i z.1) M hj

theorem direction_history_measurable (hp : 2≤p) (β h : ℝ) (x : S→State N) (inc : ℕ→S→State N)
    (M : ℕ) (hx : Measurable x) (hinc : ∀i,Measurable (inc i))
    (hW : Measurable (fun z : S×State N => (initial x inc M z.1).starProjection z.2)) :
    ∀j,Measurable[MeasurableSpace.comap (History (initial x inc M) (direction (p:=p) β h x inc M) j) inferInstance]
      (direction (p:=p) β h x inc M j) := by
  classical
  let W := initial x inc M
  let u := direction (p:=p) β h x inc M
  have hboth : ∀j,(∀i,i<j→Measurable[MeasurableSpace.comap (History W u i) inferInstance] (u i)) ∧
      (j≤M→Measurable[MeasurableSpace.comap (History W u j) inferInstance] (rawState β h x inc j)) := by
    intro j
    induction j with
    | zero =>
      refine ⟨fun i hi => by omega,fun _ => ?_⟩
      exact hx.comp (seed_measurable W u 0)
    | succ j ih =>
      have huj : Measurable[MeasurableSpace.comap (History W u j) inferInstance] (u j) := by
        by_cases hj : j<M
        · have hc : Measurable[MeasurableSpace.comap (History W u j) inferInstance] (rawQuery β h x inc j) :=
            SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp (ih.2 (Nat.le_of_lt hj))
          have hg : Measurable[MeasurableSpace.comap (History W u j) inferInstance] (rawGradient β h x inc j) :=
            gradient_measurable_finite hp S W hW u j ih.1 _ hc
              (fun z => rawQuery_mem β h x inc M j (Nat.le_of_lt hj) z)
          have hu := unitResidual_measurable_finite S W hW u j ih.1 hg
          have he : u j=(fun z => unitResidual (Space W u j z) (rawGradient β h x inc j z)) := by
            funext z
            simp only [u,direction,if_pos hj,sourceSpace_eq,Nat.min_eq_left (Nat.le_of_lt hj),W]
          rw [he]
          exact hu
        · have he : u j=(fun _ => (0:State N)) := by funext z;exact if_neg hj
          rw [he]
          exact measurable_const
      refine ⟨?_,?_⟩
      · intro i hi
        by_cases he : i=j
        · subst i
          exact huj
        · exact ih.1 i (by omega)
      · intro hj
        have hy := ih.2 (by omega)
        have hc : Measurable[MeasurableSpace.comap (History W u j) inferInstance] (rawQuery β h x inc j) :=
          SphereEulerCoefficients.clip_lipschitz.continuous.measurable.comp hy
        have hg := gradient_measurable_finite hp S W hW u j ih.1 (rawQuery β h x inc j) hc
          (fun z => rawQuery_mem β h x inc M j (by omega) z)
        have hk := (hinc j).comp (seed_measurable W u j)
        have hd := (hg.sub ((hc.inner hg).div_const (N:ℝ) |>.smul hc)).const_smul β
        have hd' := hd.sub (hc.const_smul (kappa N))
        have hn := (hk.sub ((hc.inner hk).div_const (N:ℝ) |>.smul hc)).const_smul (Real.sqrt 2)
        have hh := (hy.add (hd'.const_smul h)).add hn
        exact hh.mono (history_comap_le_succ W u j) le_rfl
  intro j
  exact (hboth (j+1)).1 j (Nat.lt_succ_self j)

end SphericalAging.SphereEulerTensorSourceHistory
