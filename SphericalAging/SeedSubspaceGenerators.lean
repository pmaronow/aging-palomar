module

public import SphericalAging.CanonicalVectorSpan

public section

/-! Every seed-measurable finite-dimensional subspace has a literal
finite seed vector list: the projected ambient coordinate basis.
No measurable orthogonal frame or selected basis is assumed. -/
noncomputable section
set_option maxHeartbeats 350000
namespace SphericalAging.SeedSubspaceGenerators
open Set MeasureTheory FiniteModel HardSphereDynamics
open scoped BigOperators

@[expose] def vectors {N : ℕ} (W : Submodule ℝ (Vector N)) (i : Fin N) : Vector N :=
  W.starProjection (basisVector i)

theorem span_range_vectors {N : ℕ} (W : Submodule ℝ (Vector N)) :
    Submodule.span ℝ (Set.range (vectors W))=W := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro y ⟨i,rfl⟩
    exact (W.orthogonalProjectionOnto (basisVector i)).property
  · intro x hx
    let b := EuclideanSpace.basisFun (Fin N) ℝ
    have hsum : x=∑i : Fin N,(b.repr x i) • vectors W i := by
      calc
        x=W.starProjection x := (W.starProjection_eq_self_iff.mpr hx).symm
        _=W.starProjection (∑i : Fin N,(b.repr x i) • b i) := congrArg W.starProjection (b.sum_repr x).symm
        _=∑i : Fin N,(b.repr x i) • vectors W i := by
          simp only [map_sum,map_smul,vectors,b,EuclideanSpace.basisFun_apply,basisVector]
    rw [hsum]
    apply Submodule.sum_mem
    intro i _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩)

theorem vectors_measurable {N : ℕ} {S : Type*} [MeasurableSpace S]
    (W : S→Submodule ℝ (Vector N))
    (hW : Measurable (fun z : S×Vector N => (W z.1).starProjection z.2)) (i : Fin N) :
    Measurable (fun s => vectors (W s) i) := by
  have harg : Measurable (fun s : S => (s,basisVector i)) := measurable_id.prodMk measurable_const
  have hh : Measurable ((fun z : S×Vector N => (W z.1).starProjection z.2)∘(fun s : S => (s,basisVector i))) :=
    hW.comp harg
  simpa only [vectors,Function.comp_def] using hh

end SphericalAging.SeedSubspaceGenerators
