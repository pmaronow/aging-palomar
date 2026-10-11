module

public import SphericalAging.OrthogonalForkNonempty
public import SphericalAging.NormedVectorRescaling

public section

/-! A literal exact orthogonal increment family at a fixed base, including
zero increments. The only dimension hypothesis is the necessary K<N. -/
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ExactOrthogonalIncrements
open FiniteModel OrthogonalForkNonempty GaussianOrthogonalForkCovariance GaussianFixedBaseForkConcentration
open NormedVectorRescaling
open scoped InnerProductSpace
variable {N K : ℕ}

theorem exists_exact_increments (hKN : K<N) (x : Vector N) (q q' : ℝ)
    (hq : 0≤q) (hq' : 0≤q') (hx : ‖x‖^2=q) :
    ∃z : Fin K→Vector N,(∀i,‖z i‖^2=q') ∧ (∀i,⟪x,z i⟫_ℝ=0) ∧
      (∀i j,i≠j→⟪z i,z j⟫_ℝ=0) := by
  have hN : 0<(N:ℝ) := Nat.cast_pos.mpr (by omega)
  have hbase : ‖x‖^2=(N:ℝ)*(q/(N:ℝ)) := by rw [hx];field_simp
  have horder : q/(N:ℝ)≤(q+q')/(N:ℝ) := div_le_div_of_nonneg_right (by linarith) hN.le
  obtain ⟨y,hy⟩ := leafDomain_nonempty hKN x (q/(N:ℝ)) ((q+q')/(N:ℝ))
    (div_nonneg hq hN.le) horder hbase
  refine ⟨fun i => y i-x,?_,?_,?_⟩
  · intro i
    have hi := hy.increment_base i
    rw [inner_sub_left,real_inner_self_eq_norm_sq,hx] at hi
    have hl := hy.leaf_norm i
    have hnorm : ‖y i‖^2=q+q' := by
      rw [hl];field_simp
    rw [norm_sub_sq_real,hnorm,hx]
    linarith
  · intro i
    rw [real_inner_comm]
    exact hy.increment_base i
  · exact hy.increment_orthogonal

theorem small_increment_exactification (hKN : K<N) (x : Vector N) (y : Fin K→Vector N)
    (q q' ε : ℝ) (hq : 0≤q) (hq' : 0≤q') (hε : 0≤ε) (hx : ‖x‖^2=q)
    (hy : ∀i,|‖y i‖^2-q'|≤ε) :
    ∃z : Fin K→Vector N,(∀i,‖z i‖^2=q') ∧ (∀i,⟪x,z i⟫_ℝ=0) ∧
      (∀i j,i≠j→⟪z i,z j⟫_ℝ=0) ∧
      (∀i,‖z i-y i‖≤2*Real.sqrt q'+Real.sqrt ε) := by
  obtain ⟨z,hzn,hzx,hzz⟩ := exists_exact_increments hKN x q q' hq hq' hx
  refine ⟨z,hzn,hzx,hzz,?_⟩
  intro i
  have hzroot : ‖z i‖=Real.sqrt q' := by
    rw [←hzn i,Real.sqrt_sq (norm_nonneg _)]
  have hyr := nonnegative_square_difference ‖y i‖ (Real.sqrt q') ε (norm_nonneg _)
    (Real.sqrt_nonneg _) hε (by rw [Real.sq_sqrt hq'];exact hy i)
  have hybound : ‖y i‖≤Real.sqrt q'+Real.sqrt ε := by
    have hh := (abs_le.mp hyr).2
    linarith
  calc
    _≤‖z i‖+‖y i‖ := norm_sub_le _ _
    _≤Real.sqrt q'+(Real.sqrt q'+Real.sqrt ε) := by rw [hzroot];exact add_le_add_right hybound _
    _=_ := by ring

end SphericalAging.ExactOrthogonalIncrements
