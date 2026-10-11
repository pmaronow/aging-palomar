module

public import SphericalAging.SphereEulerCoefficients
public import SphericalAging.GradientDisclosureMeasurability
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner

public section

/-! The literal hard-noise Euler recursion with clipped query points.
Every state and its final ball projection belong to the finite span of the
initial vector, Brownian increments and the actual queried gradients. -/
noncomputable section
namespace SphericalAging.SphereEulerQuerySpan
open HardSphereDynamics FiniteModel SphereEulerCoefficients
open scoped BigOperators InnerProductSpace
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def step (β h : ℝ) (J : Disorder N p) (y increment : State N) : State N :=
  y+h • SphereEulerCoefficients.drift β J y+
    Real.sqrt 2 • projection (clip y) increment

@[expose] def state (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N) : ℕ→State N
  | 0 => x
  | k+1 => step β h J (state β h J x increments k) (increments k)

@[expose] def query (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N) (k : ℕ) :=
  clip (state β h J x increments k)
@[expose] def output (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N) (k : ℕ) :=
  clip (state β h J x increments k)

@[expose] def generators (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N)
    (k : ℕ) : Finset (State N) := by
  classical
  exact {x} ∪ (Finset.range k).image increments ∪
    (Finset.range k).image (fun j => hamiltonianGradient J (query β h J x increments j))
@[expose] def querySpace (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N) (k : ℕ) :=
  Submodule.span ℝ (generators β h J x increments k : Set (State N))

variable (β h : ℝ) (J : Disorder N p) (x : State N) (increments : ℕ→State N)

theorem clip_mem (W : Submodule ℝ (State N)) {y : State N} (hy : y∈W) : clip y∈W := by
  unfold clip ForkBallProjection.clip
  split_ifs
  · exact hy
  · exact W.smul_mem _ hy

theorem step_mem (W : Submodule ℝ (State N)) {y z : State N}
    (hy : y∈W) (hz : z∈W) (hg : hamiltonianGradient J (clip y)∈W) :
    step β h J y z∈W := by
  have hclip := clip_mem W hy
  have hd : SphereEulerCoefficients.drift β J y∈W :=
    W.sub_mem (W.smul_mem β (W.sub_mem hg (W.smul_mem _ hclip))) (W.smul_mem _ hclip)
  exact W.add_mem (W.add_mem hy (W.smul_mem h hd))
    (W.smul_mem _ (W.sub_mem hz (W.smul_mem _ hclip)))

theorem generators_mono {k l : ℕ} (hkl : k≤l) :
    generators β h J x increments k⊆generators β h J x increments l := by
  classical
  unfold generators
  exact Finset.union_subset_union
    (Finset.union_subset_union (by rfl) (Finset.image_subset_image (Finset.range_mono hkl)))
    (Finset.image_subset_image (Finset.range_mono hkl))

theorem querySpace_mono {k l : ℕ} (hkl : k≤l) :
    querySpace β h J x increments k≤querySpace β h J x increments l :=
  Submodule.span_mono (generators_mono β h J x increments hkl)

theorem initial_mem (k : ℕ) : x∈querySpace β h J x increments k := by
  classical
  apply Submodule.subset_span
  simp only [generators,Finset.mem_coe,Finset.mem_union,Finset.mem_singleton]
  exact Or.inl (Or.inl trivial)

theorem increment_mem {j k : ℕ} (hj : j<k) : increments j∈querySpace β h J x increments k := by
  classical
  apply Submodule.subset_span
  simp only [generators,Finset.mem_coe,Finset.mem_union]
  exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩))

theorem gradient_mem {j k : ℕ} (hj : j<k) :
    hamiltonianGradient J (query β h J x increments j)∈querySpace β h J x increments k := by
  classical
  apply Submodule.subset_span
  simp only [generators,Finset.mem_coe,Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_range.mpr hj,rfl⟩)

theorem state_mem (k : ℕ) : state β h J x increments k∈querySpace β h J x increments k := by
  induction k with
  | zero => exact initial_mem β h J x increments 0
  | succ k ih =>
    exact step_mem β h J (querySpace β h J x increments (k+1))
      (querySpace_mono β h J x increments (Nat.le_succ k) ih)
      (increment_mem β h J x increments (Nat.lt_succ_self k))
      (gradient_mem β h J x increments (Nat.lt_succ_self k))

theorem query_mem (k : ℕ) : query β h J x increments k∈querySpace β h J x increments k :=
  clip_mem _ (state_mem β h J x increments k)
theorem output_mem (k : ℕ) : output β h J x increments k∈querySpace β h J x increments k :=
  clip_mem _ (state_mem β h J x increments k)

theorem output_norm_le (k : ℕ) : ‖output β h J x increments k‖≤Real.sqrt N :=
  clip_norm_le _

theorem querySpace_finrank_le (k : ℕ) :
    Module.finrank ℝ (querySpace β h J x increments k)≤1+2*k := by
  classical
  refine (finrank_span_finset_le_card (R:=ℝ) (generators β h J x increments k)).trans ?_
  unfold generators
  calc
    _ ≤ ({x} ∪ (Finset.range k).image increments).card+
        ((Finset.range k).image (fun j => hamiltonianGradient J (query β h J x increments j))).card :=
      Finset.card_union_le _ _
    _ ≤ (({x}:Finset (State N)).card+((Finset.range k).image increments).card)+
        ((Finset.range k).image (fun j => hamiltonianGradient J (query β h J x increments j))).card :=
      Nat.add_le_add_right (Finset.card_union_le _ _) _
    _ ≤ (1+k)+k := by
      simp only [Finset.card_singleton]
      exact Nat.add_le_add (Nat.add_le_add_left ((Finset.card_image_le).trans_eq (Finset.card_range _)) _)
        ((Finset.card_image_le).trans_eq (Finset.card_range _))
    _ = _ := by omega

/-- The query only sees the actual disclosed tensor coordinates. -/
theorem query_gradient_eq_disclosed (hp : 2≤p) (k : ℕ) :
    hamiltonianGradient J (query β h J x increments k)=
      hamiltonianGradient (AdaptiveGradientDisclosure.disclosedDisorder
        (querySpace β h J x increments k) J) (query β h J x increments k) :=
  AdaptiveGradientDisclosure.gradient_eq_disclosed hp _ J (query_mem β h J x increments k)

theorem state_measurable_prefix {Ω : Type*} [MeasurableSpace Ω]
    (Jf : Ω→Disorder N p) (xf : Ω→State N) (zf : ℕ→Ω→State N)
    (hJ : Measurable Jf) (hx : Measurable xf) (k : ℕ) (hz : ∀j,j<k → Measurable (zf j)) :
    Measurable (fun omega => state β h (Jf omega) (xf omega) (fun j => zf j omega) k) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    have hi := ih (fun j hj => hz j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    have hzk := hz k (Nat.lt_succ_self k)
    have hc : Measurable (fun omega => clip (state β h (Jf omega) (xf omega) (fun j => zf j omega) k)) :=
      clip_lipschitz.continuous.measurable.comp hi
    have hg := (GradientDisclosureMeasurability.gradient_joint_continuous N p).measurable.comp
      (hJ.prodMk hc)
    have hd := (hg.sub ((hc.inner hg).div_const (N:ℝ) |>.smul hc)).const_smul β
    have hd' := hd.sub (hc.const_smul (kappa N))
    have hn := (hzk.sub ((hc.inner hzk).div_const (N:ℝ) |>.smul hc)).const_smul (Real.sqrt 2)
    have hh := (hi.add (hd'.const_smul h)).add hn
    exact hh

theorem state_measurable {Ω : Type*} [MeasurableSpace Ω]
    (Jf : Ω→Disorder N p) (xf : Ω→State N) (zf : ℕ→Ω→State N)
    (hJ : Measurable Jf) (hx : Measurable xf) (hz : ∀k,Measurable (zf k)) (k : ℕ) :
    Measurable (fun omega => state β h (Jf omega) (xf omega) (fun j => zf j omega) k) :=
  state_measurable_prefix β h Jf xf zf hJ hx k (fun j _ => hz j)

theorem noise_sum (y z : State N) :
    (∑j : Fin N,(z j) • noiseColumn y j)=Real.sqrt 2 • projection y z := by
  calc
    _ = Real.sqrt 2 • (∑j : Fin N,(z j) • projection y (basisVector j)) := by
      simp only [noiseColumn,Finset.smul_sum,smul_smul,mul_comm]
    _ = Real.sqrt 2 • projection y (∑j : Fin N,(z j) • basisVector j) := by
      rw [HamiltonianParameter.projection_sum]
      simp only [projection_smul]
    _ = _ := by rw [LocalSDE.state_sum_basis]

end SphericalAging.SphereEulerQuerySpan
