module

public import SphericalAging.TensorBoundarySpaces

public section

/-! Literal coordinate spans and their next Gram direction, including
rank saturation. Their projections are jointly measurable when the rank
is selected from the past. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.CanonicalVectorSpan
open Set MeasureTheory FiniteModel HardSphereDynamics
open scoped InnerProductSpace BigOperators

@[expose] def space (N k : ℕ) : Submodule ℝ (Vector N) :=
  Submodule.span ℝ {v | ∃i : Fin N,i.val<k ∧ v=basisVector i}

theorem basis_mem {N k : ℕ} (i : Fin N) (hi : i.val<k) : basisVector i∈space N k :=
  Submodule.subset_span ⟨i,hi,rfl⟩

theorem space_mono (N : ℕ) {i j : ℕ} (h : i≤j) : space N i≤space N j := by
  apply Submodule.span_mono
  rintro v ⟨k,hk,rfl⟩
  exact ⟨k,lt_of_lt_of_le hk h,rfl⟩

theorem space_zero (N : ℕ) : space N 0=⊥ := by
  simp [space]

theorem next_mem_orthogonal {N k : ℕ} (hk : k<N) :
    basisVector ⟨k,hk⟩∈(space N k)ᗮ := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨i,hi,rfl⟩ := hv
    have hne : i≠⟨k,hk⟩ := by intro h; have hh : i.val=k := congrArg Fin.val h; omega
    simp [basisVector,EuclideanSpace.inner_single_left,hne]
  | zero => simp
  | add a b ha hb ia ib => rw [inner_add_left,ia,ib,add_zero]
  | smul c a ha ia => rw [real_inner_smul_left,ia,mul_zero]

theorem next_norm {N k : ℕ} (hk : k<N) : ‖basisVector ⟨k,hk⟩‖=1 := by
  simp [basisVector]

theorem space_succ {N k : ℕ} (hk : k<N) :
    space N (k+1)=space N k⊔ℝ ∙ basisVector ⟨k,hk⟩ := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro v ⟨i,hi,rfl⟩
    by_cases hil : i.val<k
    · exact Submodule.mem_sup_left (basis_mem i hil)
    · have hie : i=⟨k,hk⟩ := by apply Fin.ext; change i.val=k; omega
      subst i
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · apply sup_le
    · exact space_mono N (by omega)
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr (basis_mem _ (by simp))

theorem space_top {N k : ℕ} (h : N≤k) : space N k=⊤ := by
  classical
  apply top_unique
  intro x _
  let b := EuclideanSpace.basisFun (Fin N) ℝ
  rw [←b.sum_repr x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  simpa only [b,EuclideanSpace.basisFun_apply,basisVector] using
    basis_mem (N:=N) i (lt_of_lt_of_le i.isLt h)

theorem projection_joint_measurable {N : ℕ} {S : Type*} [MeasurableSpace S]
    {r : S→ℕ} (hr : Measurable r) :
    Measurable (fun z : S×Vector N => (space N (r z.1)).starProjection z.2) := by
  let F : ℕ→Vector N→L[ℝ]Vector N := fun k => (space N k).starProjection
  have hF : Measurable F := measurable_of_countable F
  have harg : Measurable (fun z : S×Vector N => (F (r z.1),z.2)) :=
    ((hF.comp hr).comp measurable_fst).prodMk measurable_snd
  exact (continuous_fst.clm_apply continuous_snd).measurable.comp harg

end SphericalAging.CanonicalVectorSpan
