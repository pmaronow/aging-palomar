module

public import SphericalAging.TensorHamiltonianRotation

public section

/-! A residual ordered tensor has literal Euclidean coordinates in the
p-fold tensor products of an orthonormal basis of the vector complement.
The coordinate isometry and its Gaussian law are constructed. -/
noncomputable section
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResidualTensorCoordinates
open Set MeasureTheory ProbabilityTheory FiniteModel HardSphereDynamics AdaptiveGradientDisclosure
open SphereTensorObservable TensorHamiltonianRotation
open scoped InnerProductSpace BigOperators

@[expose]  def family {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (I : TensorIndex n p) : TensorSpace N p :=
  pureTensor (fun k => (b (I k) : Vector N))

 theorem family_mem {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (I : TensorIndex n p) : family W b I∈residualTensorSpace W :=
  Submodule.subset_span ⟨(fun k => b (I k)),rfl⟩

 theorem family_orthonormal {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) : Orthonormal ℝ (family (p:=p) W b) := by
  classical
  rw [orthonormal_iff_ite]
  intro I J
  rw [family,family,pureTensor_inner]
  have hb : ∀k,⟪(b (I k) : Vector N),(b (J k) : Vector N)⟫_ℝ=if I k=J k then 1 else 0 :=
    fun k => b.inner_eq_ite _ _
  simp_rw [hb]
  by_cases h : I=J
  · subst J;simp
  · rw [if_neg h]
    obtain ⟨k,hk⟩ : ∃k,I k≠J k := by
      by_contra hh
      push_neg at hh
      exact h (funext hh)
    exact Finset.prod_eq_zero (Finset.mem_univ k) (if_neg hk)

 theorem pureTensor_expansion {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (v : Fin p→Wᗮ) :
    pureTensor (fun k => (v k : Vector N))=
      ∑I : TensorIndex n p,(∏k : Fin p,b.repr (v k) (I k)) • family W b I := by
  classical
  have hv : ∀k,(v k : Vector N)=∑i : Fin n,b.repr (v k) i • (b i : Vector N) := by
    intro k
    simpa only [Submodule.coe_sum,Submodule.coe_smul] using
      congrArg (fun y : Wᗮ => (y : Vector N)) (b.sum_repr (v k)).symm
  have hh := (pureForm N p).toMultilinearMap.map_sum
    (fun k : Fin p => fun i : Fin n => b.repr (v k) i • (b i : Vector N))
  change pureForm N p (fun k => ∑i : Fin n,b.repr (v k) i • (b i : Vector N))=
    ∑I : TensorIndex n p,pureForm N p (fun k => b.repr (v k) (I k) • (b (I k) : Vector N)) at hh
  rw [show (fun k => ∑i : Fin n,b.repr (v k) i • (b i : Vector N))=(fun k => (v k : Vector N))
    from funext (fun k => (hv k).symm)] at hh
  rw [←pureForm_apply]
  rw [hh]
  apply Finset.sum_congr rfl
  intro I _
  exact (pureForm N p).toMultilinearMap.map_smul_univ _ _

 theorem span_family {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) :
    Submodule.span ℝ (Set.range (family (p:=p) W b))=residualTensorSpace W := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro J ⟨I,rfl⟩
    exact family_mem W b I
  · apply Submodule.span_le.mpr
    rintro J ⟨v,rfl⟩
    change pureTensor (fun k => (v k : Vector N))∈Submodule.span ℝ (Set.range (family W b))
    rw [pureTensor_expansion W b v]
    apply Submodule.sum_mem
    intro I _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨I,rfl⟩)

@[expose]  def subtypeFamily {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (I : TensorIndex n p) : residualTensorSpace (p:=p) W :=
  ⟨family W b I,family_mem W b I⟩

 theorem subtypeFamily_orthonormal {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) : Orthonormal ℝ (subtypeFamily (p:=p) W b) := by
  classical
  rw [orthonormal_iff_ite]
  intro I J
  exact (orthonormal_iff_ite.mp (family_orthonormal (p:=p) W b)) I J

 theorem span_subtypeFamily {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) :
    Submodule.span ℝ (Set.range (subtypeFamily (p:=p) W b))=⊤ := by
  apply Submodule.map_injective_of_injective (residualTensorSpace (p:=p) W).injective_subtype
  rw [Submodule.map_span,Submodule.map_top,Submodule.range_subtype]
  have he : (residualTensorSpace (p:=p) W).subtype '' Set.range (subtypeFamily (p:=p) W b)=
      Set.range (family (p:=p) W b) := by
    rw [←Set.range_comp]
    rfl
  rw [he,span_family]

@[expose]  def basis {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) :
    OrthonormalBasis (TensorIndex n p) ℝ (residualTensorSpace (p:=p) W) :=
  OrthonormalBasis.mk (subtypeFamily_orthonormal W b) (le_of_eq (span_subtypeFamily W b).symm)

 theorem basis_apply {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (I : TensorIndex n p) : basis (p:=p) W b I=subtypeFamily W b I := by
  exact congrFun (OrthonormalBasis.coe_mk (subtypeFamily_orthonormal (p:=p) W b)
    (le_of_eq (span_subtypeFamily (p:=p) W b).symm)) I

@[expose]  def coordinates {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) :
    residualTensorSpace (p:=p) W≃ₗᵢ[ℝ]TensorSpace n p := (basis W b).repr

 theorem coordinates_pureTensor {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) (v : Fin p→Wᗮ) :
    coordinates W b ⟨pureTensor (fun k => (v k : Vector N)),Submodule.subset_span ⟨v,rfl⟩⟩=
      pureTensor (fun k => b.repr (v k)) := by
  ext I
  change (basis W b).repr _ I=(pureTensor (fun k => b.repr (v k))) I
  rw [OrthonormalBasis.repr_apply_apply,basis_apply]
  change ⟪family W b I,pureTensor (fun k => (v k : Vector N))⟫_ℝ=_
  rw [family,pureTensor_inner]
  simp only [pureTensor,WithLp.ofLp_toLp,OrthonormalBasis.repr_apply_apply]
  rfl

 theorem coordinates_gaussian {N n p : ℕ} (W : Submodule ℝ (Vector N))
    (b : OrthonormalBasis (Fin n) ℝ Wᗮ) :
    MeasurePreserving (coordinates (p:=p) W b) (stdGaussian (residualTensorSpace (p:=p) W))
      (stdGaussian (TensorSpace n p)) :=
  ⟨(coordinates W b).continuous.measurable,stdGaussian_map (coordinates W b)⟩

end SphericalAging.ResidualTensorCoordinates
