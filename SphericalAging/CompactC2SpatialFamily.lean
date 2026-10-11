module

public import SphericalAging.C2ObservableDerivative
public import Mathlib.Analysis.Normed.Module.Convex

public section

/-! Uniform first-order Taylor bounds on an actual compact parameter/state
family, derived from joint spatial derivative continuity. -/
noncomputable section
open Set Filter Topology
open scoped BigOperators
namespace SphericalAging.CompactC2SpatialFamily
open HardSphereDynamics LocalSDE
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {A : Type*} {E : Type} [TopologicalSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linear_norm_bound (L : State N→L[ℝ]E) : ‖L‖≤∑ i : Fin N,‖L (basisVector i)‖ := by
  apply L.opNorm_le_bound (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  intro x
  have hx := state_sum_basis x
  nth_rw 1 [←hx]
  rw [map_sum]
  calc
    _≤∑ i : Fin N,‖L (x i • basisVector i)‖ := norm_sum_le _ _
    _≤∑ i : Fin N,‖L (basisVector i)‖*‖x‖ := by
      apply Finset.sum_le_sum
      intro i _
      rw [map_smul,norm_smul,mul_comm]
      exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le x i) (norm_nonneg _)
    _=_ := (Finset.sum_mul _ _ _).symm

theorem bilinear_norm_bound (H : State N→L[ℝ](State N→L[ℝ]E)) :
    ‖H‖≤∑ i : Fin N,∑ j : Fin N,‖H (basisVector i) (basisVector j)‖ :=
  (linear_norm_bound H).trans (Finset.sum_le_sum (fun i _ => linear_norm_bound (H (basisVector i))))

theorem firstOrder_taylor_bound {f : State N→E} (hf : ContDiff ℝ 2 f)
    (R C : ℝ) (hC : 0≤C)
    (hH : ∀ z∈Metric.closedBall (0 : State N) R,‖fderiv ℝ (fderiv ℝ f) z‖≤C)
    (x y : State N) (hx : x∈Metric.closedBall (0 : State N) R)
    (hy : y∈Metric.closedBall (0 : State N) R) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖≤C*‖y-x‖^2 := by
  have hdf := (hf.fderiv_right (m:=1) (by norm_num)).differentiable (by norm_num)
  have hLip (z : State N) (hz : z∈Metric.closedBall (0 : State N) R) :
      ‖fderiv ℝ f z-fderiv ℝ f x‖≤C*‖z-x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun w _ => hdf w)
      hH (convex_closedBall (0 : State N) R) hx hz
  let g : State N→E := fun z => f z-f x-fderiv ℝ f x (z-x)
  have hd (z : State N) : HasFDerivAt g (fderiv ℝ f z-fderiv ℝ f x) z :=
    (((hf.differentiable (by norm_num)).differentiableAt.hasFDerivAt).sub_const _).sub
      ((fderiv ℝ f x).hasFDerivAt.comp z ((hasFDerivAt_id z).sub_const x))
  have hseg : segment ℝ x y⊆Metric.closedBall (0 : State N) R :=
    (convex_closedBall (0 : State N) R).segment_subset hx hy
  have hb : ∀ z∈segment ℝ x y,‖fderiv ℝ g z‖≤C*‖y-x‖ := by
    intro z hz
    rw [(hd z).fderiv]
    exact (hLip z (hseg hz)).trans (mul_le_mul_of_nonneg_left (norm_sub_le_of_mem_segment hz) hC)
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => (hd z).differentiableAt)
    hb (convex_segment (𝕜:=ℝ) x y) (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  simpa only [g,sub_self,map_zero,sub_zero,mul_assoc,←pow_two] using hh

theorem exists_uniform_bounds (f : A→State N→E) (hf : ∀ a,ContDiff ℝ 2 (f a))
    (hD : Continuous (fun q : A×State N => fderiv ℝ (f q.1) q.2))
    (hH : Continuous (fun q : A×State N => fderiv ℝ (fderiv ℝ (f q.1)) q.2))
    (K : Set A) (hK : IsCompact K) (R : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ a∈K,∀ x∈Metric.closedBall (0 : State N) R,
      ‖fderiv ℝ (f a) x‖≤C ∧ ∀ y∈Metric.closedBall (0 : State N) R,
        ‖f a y-f a x‖≤C*‖y-x‖ ∧
        ‖f a y-f a x-fderiv ℝ (f a) x (y-x)‖≤C*‖y-x‖^2 := by
  have hcompact := hK.prod (isCompact_closedBall (0 : State N) R)
  obtain ⟨Cd,hCd⟩ := hcompact.exists_bound_of_continuousOn hD.norm.continuousOn
  have hhc : Continuous (fun q : A×State N => ∑ i : Fin N,∑ j : Fin N,
      ‖fderiv ℝ (fderiv ℝ (f q.1)) q.2 (basisVector i) (basisVector j)‖) := by
    apply continuous_finset_sum
    intro i _
    apply continuous_finset_sum
    intro j _
    exact ((hH.clm_apply continuous_const).clm_apply continuous_const).norm
  obtain ⟨Ch,hCh⟩ := hcompact.exists_bound_of_continuousOn hhc.continuousOn
  let C : ℝ := max 0 (max Cd Ch)
  have hC : 0≤C := le_max_left _ _
  have hCdC : Cd≤C := (le_max_left Cd Ch).trans (le_max_right _ _)
  have hChC : Ch≤C := (le_max_right Cd Ch).trans (le_max_right _ _)
  refine ⟨C,hC,?_⟩
  intro a ha x hx
  have hd : ∀ z∈Metric.closedBall (0 : State N) R,‖fderiv ℝ (f a) z‖≤C :=
    fun z hz => le_trans (by simpa only [norm_norm] using hCd (a,z) ⟨ha,hz⟩) hCdC
  have hh : ∀ z∈Metric.closedBall (0 : State N) R,‖fderiv ℝ (fderiv ℝ (f a)) z‖≤C :=
    fun z hz => (bilinear_norm_bound _).trans (((le_abs_self _).trans
      (by simpa only [Real.norm_eq_abs] using hCh (a,z) ⟨ha,hz⟩)).trans hChC)
  refine ⟨hd x hx,?_⟩
  intro y hy
  exact ⟨Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf a).differentiable (by norm_num) z)
    hd (convex_closedBall (0 : State N) R) hx hy,
    firstOrder_taylor_bound (hf a) R C hC hh x y hx hy⟩

end SphericalAging.CompactC2SpatialFamily
