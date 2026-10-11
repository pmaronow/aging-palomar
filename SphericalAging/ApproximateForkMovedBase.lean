module

public import SphericalAging.UniformOrthogonalForkExactification

public section

/-! Moving the actual base of a locally constrained fork changes its
increment Gram entries by a controlled amount, derived from Cauchy-Schwarz. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ApproximateForkMovedBase
open FiniteModel UniformOrthogonalForkExactification
open scoped InnerProductSpace
variable {N K : ℕ}

theorem child_moved_base_inner (x τ : Vector N) (y : Fin K→Vector N)
    (q0 η e : ℝ) (hyball : ∀i,‖y i‖≤1) (he : ‖τ-x‖≤e)
    (hyx : ∀i,|⟪y i,x⟫_ℝ-q0|≤η) (i : Fin K) :
    |⟪y i,τ⟫_ℝ-q0|≤η+e := by
  have hh : |⟪y i,τ-x⟫_ℝ|≤e := by
    calc
      _≤‖y i‖*‖τ-x‖ := abs_real_inner_le_norm _ _
      _≤1*‖τ-x‖ := mul_le_mul_of_nonneg_right (hyball i) (norm_nonneg _)
      _≤e := by simpa only [one_mul] using he
  calc
    _=|(⟪y i,x⟫_ℝ-q0)+⟪y i,τ-x⟫_ℝ| := by rw [inner_sub_right];congr 1;ring
    _≤|⟪y i,x⟫_ℝ-q0|+|⟪y i,τ-x⟫_ℝ| := abs_add_le _ _
    _≤η+e := add_le_add (hyx i) hh

theorem actual_moved_base_gram (x τ : Vector N) (y : Fin K→Vector N)
    (q0 q1 η e : ℝ) (hτ : ‖τ‖^2=q0) (hyball : ∀i,‖y i‖≤1) (he : ‖τ-x‖≤e)
    (hyn : ∀i,|‖y i‖^2-q1|≤η) (hyx : ∀i,|⟪y i,x⟫_ℝ-q0|≤η)
    (hyy : ∀i j,i≠j→|⟪y i,y j⟫_ℝ-q0|≤η) :
    (∀i,|‖y i-τ‖^2-(q1-q0)|≤3*η+2*e) ∧
    (∀i,|⟪τ,y i-τ⟫_ℝ|≤η+e) ∧
    (∀i j,i≠j→|⟪y i-τ,y j-τ⟫_ℝ|≤3*η+2*e) := by
  have hi := child_moved_base_inner x τ y q0 η e hyball he hyx
  refine ⟨?_,?_,?_⟩
  · intro i
    have heq : ‖y i-τ‖^2-(q1-q0)=(‖y i‖^2-q1)-2*(⟪y i,τ⟫_ℝ-q0) := by
      rw [norm_sub_sq_real,hτ];ring
    rw [heq]
    calc
      _≤|‖y i‖^2-q1|+|2*(⟪y i,τ⟫_ℝ-q0)| := abs_sub _ _
      _=|‖y i‖^2-q1|+2*|⟪y i,τ⟫_ℝ-q0| := by rw [abs_mul];norm_num
      _≤η+2*(η+e) := add_le_add (hyn i) (mul_le_mul_of_nonneg_left (hi i) (by norm_num))
      _=_ := by ring
  · intro i
    simpa only [inner_sub_right,real_inner_self_eq_norm_sq,hτ,real_inner_comm] using hi i
  · intro i j hij
    have heq : ⟪y i-τ,y j-τ⟫_ℝ=(⟪y i,y j⟫_ℝ-q0)-
        (⟪y i,τ⟫_ℝ-q0)-(⟪y j,τ⟫_ℝ-q0) := by
      rw [inner_sub_left,inner_sub_right,inner_sub_right,real_inner_self_eq_norm_sq,hτ]
      rw [real_inner_comm τ (y j)]
      ring
    rw [heq]
    calc
      _≤|(⟪y i,y j⟫_ℝ-q0)-(⟪y i,τ⟫_ℝ-q0)|+|⟪y j,τ⟫_ℝ-q0| := abs_sub _ _
      _≤(|⟪y i,y j⟫_ℝ-q0|+|⟪y i,τ⟫_ℝ-q0|)+|⟪y j,τ⟫_ℝ-q0| :=
        add_le_add_left (abs_sub _ _) _
      _≤(η+(η+e))+(η+e) := add_le_add (add_le_add (hyy i j hij) (hi i)) (hi j)
      _=_ := by ring

theorem actual_moved_base_exactification (hKN : K<N) (x τ : Vector N) (y : Fin K→Vector N)
    (qmin q0 q1 η e : ℝ) (hmin : 0<qmin) (h0min : qmin≤q0) (h01 : q0≤q1)
    (hη : 0≤η) (he0 : 0≤e) (hτ : ‖τ‖^2=q0) (hyball : ∀i,‖y i‖≤1) (he : ‖τ-x‖≤e)
    (hyn : ∀i,|‖y i‖^2-q1|≤η) (hyx : ∀i,|⟪y i,x⟫_ℝ-q0|≤η)
    (hyy : ∀i j,i≠j→|⟪y i,y j⟫_ℝ-q0|≤η)
    (hbaseSmall : Real.sqrt (3*η+2*e)≤qmin)
    (hsmall : 4*((K+1:ℕ):ℝ)*Real.sqrt (3*η+2*e)≤1) :
    ∃z : Fin K→Vector N,
      (∀i,‖z i‖^2=q1) ∧ (∀i,⟪z i-τ,τ⟫_ℝ=0) ∧
      (∀i j,i≠j→⟪z i-τ,z j-τ⟫_ℝ=0) ∧
      (∀i,‖z i-y i‖≤error K (3*η+2*e)) := by
  obtain ⟨hn,hxg,hh⟩ := actual_moved_base_gram x τ y q0 q1 η e hτ hyball he hyn hyx hyy
  have hδ : 0≤3*η+2*e := by positivity
  have hbase : ∀i,|⟪τ,y i-τ⟫_ℝ|≤3*η+2*e :=
    fun i => (hxg i).trans (by linarith)
  obtain ⟨u,hun,hux,huu,hd⟩ := actual_uniform_exactification hKN τ (fun i => y i-τ)
    qmin q0 (q1-q0) (3*η+2*e) hmin h0min (sub_nonneg.mpr h01) hδ
    hbaseSmall hsmall hτ hn hbase hh
  refine ⟨fun i => τ+u i,?_,?_,?_,?_⟩
  · intro i;rw [norm_add_sq_real,hτ,hux i,hun i];ring
  · intro i;rw [add_sub_cancel_left,real_inner_comm];exact hux i
  · intro i j hij;rw [add_sub_cancel_left,add_sub_cancel_left];exact huu i j hij
  · intro i
    have heq : τ+u i-y i=u i-(y i-τ) := by abel
    rw [heq];exact hd i

end SphericalAging.ApproximateForkMovedBase
