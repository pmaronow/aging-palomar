module

public import SphericalAging.FiniteGramCoherence
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

public section

/-! Dimension-independent conditioning of a literal nearly orthogonal family.
The lower Gram bound and projection estimate are derived by finite sums. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteGramConditioning
open FiniteModel FiniteGramCoherence
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

theorem weightedSum_norm_sq_lower (x : Fin K→Vector N) (c : Fin K→ℝ)
    (γ δ : ℝ) (hδ : 0≤δ) (hdiag : ∀i,γ≤‖x i‖^2)
    (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤δ) :
    (γ-(K:ℝ)*δ)*(∑i,(c i)^2)≤‖weightedSum c x‖^2 := by
  classical
  have hterm (i j : Fin K) :
      (if i=j then γ*(c i)^2 else 0)-δ* |c i| * |c j|≤c i*c j*⟪x i,x j⟫_ℝ := by
    by_cases hij : i=j
    · subst j
      rw [if_pos rfl,real_inner_self_eq_norm_sq]
      have hh := mul_le_mul_of_nonneg_left (hdiag i) (sq_nonneg (c i))
      have he : 0≤δ* |c i| * |c i| := by positivity
      nlinarith
    · rw [if_neg hij,zero_sub]
      have hh : |c i*c j*⟪x i,x j⟫_ℝ|≤δ* |c i| * |c j| := by
        rw [abs_mul,abs_mul]
        calc
          _≤|c i| * |c j| *δ :=
            mul_le_mul_of_nonneg_left (hcross i j hij) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
          _=_ := by ring
      exact (neg_le_neg hh).trans (neg_abs_le _)
  have habs : (∑i,|c i|)^2≤(K:ℝ)*(∑i,(c i)^2) := by
    have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin K => |c i|)
    simpa only [Finset.card_univ,Fintype.card_fin,sq_abs] using hh
  have heq : ‖weightedSum c x‖^2=∑i,∑j,c i*c j*⟪x i,x j⟫_ℝ := by
    rw [weightedSum,←real_inner_self_eq_norm_sq,sum_inner]
    simp only [inner_sum,real_inner_smul_left,real_inner_smul_right]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hd : (∑i : Fin K,∑j : Fin K,if i=j then γ*(c i)^2 else 0)=γ*(∑i,(c i)^2) := by
    simp [Finset.mul_sum]
  calc
    _=γ*(∑i,(c i)^2)-δ*((K:ℝ)*(∑i,(c i)^2)) := by ring
    _≤γ*(∑i,(c i)^2)-δ*(∑i,|c i|)^2 :=
      sub_le_sub_left (mul_le_mul_of_nonneg_left habs hδ) _
    _=∑i,∑j,((if i=j then γ*(c i)^2 else 0)-δ* |c i| * |c j|) := by
      simp only [Finset.sum_sub_distrib]
      rw [hd]
      simp only [←Finset.mul_sum,←Finset.sum_mul]
      ring
    _≤∑i,∑j,c i*c j*⟪x i,x j⟫_ℝ :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hterm i j))
    _=_ := heq.symm

theorem actual_linearIndependent (x : Fin K→Vector N) (γ δ : ℝ)
    (hδ : 0≤δ) (hgap : 0<γ-(K:ℝ)*δ)
    (hdiag : ∀i,γ≤‖x i‖^2) (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤δ) :
    LinearIndependent ℝ x := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  have hh := weightedSum_norm_sq_lower x c γ δ hδ hdiag hcross
  have hs : (∑j,(c j)^2)=0 := by
    have hnon : 0≤∑j,(c j)^2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hzero : weightedSum c x=0 := hc
    rw [hzero,norm_zero,zero_pow (by omega)] at hh
    nlinarith
  have hle := Finset.single_le_sum (fun j _ => sq_nonneg (c j)) (Finset.mem_univ i)
  rw [hs] at hle
  nlinarith [sq_nonneg (c i)]

theorem actual_span_projection_bound (x : Fin K→Vector N) (v : Vector N)
    (γ δ : ℝ) (hδ : 0≤δ) (hgap : 0<γ-(K:ℝ)*δ)
    (hdiag : ∀i,γ≤‖x i‖^2) (hcross : ∀i j,i≠j→|⟪x i,x j⟫_ℝ|≤δ)
    (hv : ∀i,|⟪x i,v⟫_ℝ|≤δ) :
    ‖(Submodule.span ℝ (Set.range x)).starProjection v‖^2≤
      (K:ℝ)*δ^2/(γ-(K:ℝ)*δ) := by
  let W := Submodule.span ℝ (Set.range x)
  let P := W.starProjection v
  obtain ⟨c,hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp
    (Submodule.starProjection_apply_mem W v)
  have hc' : weightedSum c x=P := hc
  let S : ℝ := ∑i,(c i)^2
  let A : ℝ := ∑i,|c i|
  let T : ℝ := ‖P‖^2
  let g := γ-(K:ℝ)*δ
  have hT : 0≤T := sq_nonneg _
  have hA : 0≤A := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hlower : g*S≤T := by
    simpa only [hc'] using weightedSum_norm_sq_lower x c γ δ hδ hdiag hcross
  have hinner : T=⟪P,v⟫_ℝ := by
    have hh := W.starProjection_inner_eq_zero v P (Submodule.starProjection_apply_mem W v)
    rw [inner_sub_left,sub_eq_zero,real_inner_self_eq_norm_sq,real_inner_comm] at hh
    exact hh.symm
  have hTA : T≤δ*A := by
    rw [hinner,←hc',weightedSum,sum_inner]
    calc
      _≤∑i,|c i| * |⟪x i,v⟫_ℝ| := Finset.sum_le_sum (fun i _ => by
        rw [real_inner_smul_left]
        simpa only [abs_mul] using le_abs_self (c i*⟪x i,v⟫_ℝ))
      _≤∑i,|c i| *δ := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (hv i) (abs_nonneg _))
      _=δ*A := by rw [←Finset.sum_mul]; ring
  have hAS : A^2≤(K:ℝ)*S := by
    have hh := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin K => |c i|)
    simpa only [Finset.card_univ,Fintype.card_fin,sq_abs] using hh
  have hT2 : T*T≤δ^2*((K:ℝ)*S) := by
    have hh := (sq_le_sq₀ hT (mul_nonneg hδ hA)).mpr hTA
    rw [mul_pow] at hh
    calc
      _≤δ^2*A^2 := by simpa only [pow_two] using hh
      _≤δ^2*((K:ℝ)*S) := mul_le_mul_of_nonneg_left hAS (sq_nonneg δ)
  have hcancel : (g*T)*T≤((K:ℝ)*δ^2)*T := by
    calc
      _=g*(T*T) := by ring
      _≤g*(δ^2*((K:ℝ)*S)) := mul_le_mul_of_nonneg_left hT2 hgap.le
      _=((K:ℝ)*δ^2)*(g*S) := by ring
      _≤((K:ℝ)*δ^2)*T := mul_le_mul_of_nonneg_left hlower (by positivity)
  change T≤_
  apply (le_div_iff₀ hgap).mpr
  by_cases hzero : T=0
  · rw [hzero,zero_mul]
    positivity
  · have hh : g*T≤(K:ℝ)*δ^2 := le_of_mul_le_mul_right hcancel
      (lt_of_le_of_ne hT (Ne.symm hzero))
    simpa only [g,mul_comm] using hh

end SphericalAging.FiniteGramConditioning
