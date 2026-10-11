module

public import SphericalAging.SeedSpanProjectionIdentity
public import Mathlib.Algebra.Order.Chebyshev

public section

/-! Elementary Gram coherence bounds, proved from the actual finite vector
family. No spectral or projection estimate is assumed. -/
noncomputable section
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteGramCoherence
open FiniteModel SeedSpanOrthonormalFrame SeedSpanProjectionIdentity
open scoped BigOperators InnerProductSpace
variable {N K m : ℕ}

@[expose] def weightedSum (c : Fin K→ℝ) (x : Fin K→Vector N) : Vector N := ∑i,c i • x i

theorem weightedSum_norm_sq_le (x : Fin K→Vector N) (c : Fin K→ℝ)
    (D η : ℝ) (hη : 0≤η) (hdiag : ∀i,‖x i‖^2≤D)
    (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤η) :
    ‖weightedSum c x‖^2≤(D+(K:ℝ)*η)*(∑i,(c i)^2) := by
  classical
  have hterm (i j : Fin K) : c i*c j*⟪x i,x j⟫_ℝ≤
      (if i=j then D*(c i)^2 else 0)+η* |c i| * |c j| := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,real_inner_self_eq_norm_sq]
      have hh := mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg (c i))
      have he : 0≤η* |c i| * |c i| := by positivity
      nlinarith
    · rw [if_neg hij,zero_add]
      calc
        _≤|c i*c j*⟪x i,x j⟫_ℝ| := le_abs_self _
        _=|c i| * |c j| * |⟪x i,x j⟫_ℝ| := by rw [abs_mul,abs_mul]
        _≤|c i| * |c j| *η :=
          mul_le_mul_of_nonneg_left (hcross i j hij) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _=_ := by ring
  have habs : (∑i,|c i|)^2≤(K:ℝ)*(∑i,(c i)^2) := by
    have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin K => |c i|)
    simpa only [Finset.card_univ,Fintype.card_fin,sq_abs] using hh
  calc
    _=∑i,∑j,c i*c j*⟪x i,x j⟫_ℝ := by
      rw [weightedSum,←real_inner_self_eq_norm_sq,sum_inner]
      simp only [inner_sum,real_inner_smul_left,real_inner_smul_right]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤∑i,∑j,((if i=j then D*(c i)^2 else 0)+η* |c i| * |c j|) :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _=D*(∑i,(c i)^2)+η*(∑i,|c i|)^2 := by
      have hd : (∑i : Fin K,∑j : Fin K,if i=j then D*(c i)^2 else 0)=D*(∑i,(c i)^2) := by
        simp [Finset.sum_ite,Finset.mul_sum]
      simp only [Finset.sum_add_distrib]
      rw [hd]
      simp only [←Finset.mul_sum,←Finset.sum_mul]
      ring
    _≤D*(∑i,(c i)^2)+η*((K:ℝ)*(∑i,(c i)^2)) :=
      add_le_add_right (mul_le_mul_of_nonneg_left habs hη) _
    _=_ := by ring

theorem inner_square_sum_le (x : Fin K→Vector N) (e : Vector N)
    (D η : ℝ) (hD : 0≤D) (hη : 0≤η) (hdiag : ∀i,‖x i‖^2≤D)
    (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤η) :
    (∑i,⟪e,x i⟫_ℝ^2)≤‖e‖^2*(D+(K:ℝ)*η) := by
  let c : Fin K→ℝ := fun i => ⟪e,x i⟫_ℝ
  let S : ℝ := ∑i,(c i)^2
  have hS0 : 0≤S := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have heq : ⟪e,weightedSum c x⟫_ℝ=S := by
    rw [weightedSum,inner_sum]
    simp only [real_inner_smul_right,c,S,pow_two]
  have hcs := real_inner_mul_inner_self_le e (weightedSum c x)
  rw [heq,real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq] at hcs
  have hnorm := weightedSum_norm_sq_le x c D η hη hdiag hcross
  have hh : S*S≤(‖e‖^2*(D+(K:ℝ)*η))*S := by
    calc
      _≤‖e‖^2*‖weightedSum c x‖^2 := hcs
      _≤‖e‖^2*((D+(K:ℝ)*η)*S) := mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)
      _=_ := by ring
  change S≤_
  by_cases hS : S=0
  · rw [hS]
    positivity
  · exact (mul_le_mul_iff_right₀ (lt_of_le_of_ne hS0 (Ne.symm hS))).mp (by simpa only [mul_comm] using hh)

theorem actual_projection_square_sum_le (W : Submodule ℝ (Vector N))
    (hm : Module.finrank ℝ W≤m) (x : Fin K→Vector N)
    (D η : ℝ) (hD : 0≤D) (hη : 0≤η) (hdiag : ∀i,‖x i‖^2≤D)
    (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤η) :
    (∑i,‖W.starProjection (x i)‖^2)≤(m:ℝ)*(D+(K:ℝ)*η) := by
  have hconst : 0≤D+(K:ℝ)*η := by positivity
  simp_rw [projection_norm_sq_eq_frame_sum W hm]
  rw [Finset.sum_comm]
  calc
    _≤∑_j : Fin m,(D+(K:ℝ)*η) := by
      apply Finset.sum_le_sum
      intro j _
      have hh := inner_square_sum_le x (frame W m j) D η hD hη hdiag hcross
      have hnorm : ‖frame W m j‖^2≤1 := by
        rcases frame_zero_or_unit W m j with hz | hu
        · simp [hz]
        · simp [hu]
      exact hh.trans (by simpa using mul_le_mul_of_nonneg_right hnorm hconst)
    _=_ := by simp; ring

end SphericalAging.FiniteGramCoherence
