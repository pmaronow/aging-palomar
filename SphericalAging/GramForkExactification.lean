module

public import SphericalAging.GramSchmidtProjection
public import SphericalAging.NormedVectorRescaling

public section

/-! Exactification by the literal Gram-Schmidt algorithm. All conditioning
and correction bounds are derived from the original finite Gram entries. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GramForkExactification
open FiniteModel FiniteGramConditioning GramSchmidtProjection NormedVectorRescaling InnerProductSpace
open scoped BigOperators InnerProductSpace
variable {N K : ℕ}

private theorem gramSchmidt_distance_uniform (v : Fin K→Vector N)
    (γ δ : ℝ) (hδ : 0≤δ) (hgap : 0<γ-(K:ℝ)*δ)
    (hdiag : ∀i,γ≤‖v i‖^2) (hcross : ∀i j,i≠j→|⟪v i,v j⟫_ℝ|≤δ) (i : Fin K) :
    ‖gramSchmidt ℝ v i-v i‖≤Real.sqrt ((K:ℝ)*δ^2/(γ-(K:ℝ)*δ)) := by
  have hi : (i.val:ℝ)≤K := Nat.cast_le.mpr (Nat.le_of_lt i.isLt)
  have hg : γ-(K:ℝ)*δ≤γ-(i.val:ℝ)*δ := by nlinarith
  have hh := actual_gramSchmidt_distance_bound v i γ δ hδ (hgap.trans_le hg) hdiag hcross
  have hr : (i.val:ℝ)*δ^2/(γ-(i.val:ℝ)*δ)≤(K:ℝ)*δ^2/(γ-(K:ℝ)*δ) :=
    div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_right hi (sq_nonneg δ)) hgap hg
  have hnon : 0≤(K:ℝ)*δ^2/(γ-(K:ℝ)*δ) := div_nonneg (by positivity) hgap.le
  have hroot := Real.sq_sqrt hnon
  nlinarith [norm_nonneg (gramSchmidt ℝ v i-v i),Real.sqrt_nonneg ((K:ℝ)*δ^2/(γ-(K:ℝ)*δ))]

@[expose] def exactVector (v : Fin K→Vector N) (q : Fin K→ℝ) (i : Fin K) : Vector N :=
  rescale (q i) (gramSchmidt ℝ v i)

theorem actual_exactification (v : Fin K→Vector N) (q : Fin K→ℝ)
    (γ δ ε : ℝ) (hδ : 0≤δ) (hε : 0≤ε) (hgap : 0<γ-(K:ℝ)*δ)
    (hq : ∀i,0≤q i) (hdiag : ∀i,γ≤‖v i‖^2)
    (hcross : ∀i j,i≠j→|⟪v i,v j⟫_ℝ|≤δ)
    (hnorm : ∀i,|‖v i‖^2-q i|≤ε) :
    (∀i,‖exactVector v q i‖^2=q i) ∧
    (∀i j,i≠j→⟪exactVector v q i,exactVector v q j⟫_ℝ=0) ∧
    (∀i,‖exactVector v q i-v i‖≤
      2*Real.sqrt ((K:ℝ)*δ^2/(γ-(K:ℝ)*δ))+Real.sqrt ε) := by
  have hli := actual_linearIndependent v γ δ hδ hgap hdiag hcross
  have hne (i : Fin K) := gramSchmidt_ne_zero i hli
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [exactVector,rescale_norm _ _ (hne i),Real.sq_sqrt (hq i)]
  · intro i j hij
    simp only [exactVector,rescale,real_inner_smul_left,real_inner_smul_right,
      gramSchmidt_orthogonal ℝ v hij,mul_zero]
  · intro i
    exact (rescale_distance (q i) ε (hq i) hε _ _ (hne i) (hnorm i)).trans
      (add_le_add_left (mul_le_mul_of_nonneg_left
        (gramSchmidt_distance_uniform v γ δ hδ hgap hdiag hcross i) (by norm_num)) _)

theorem exactVector_zero (x : Vector N) (y : Fin K→Vector N) (q q' : ℝ)
    (hx : ‖x‖^2=q) (hqn : 0<q) :
    exactVector (Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y) (Fin.cons (α := fun _ : Fin (K+1) => ℝ) q (fun _ => q')) 0=x := by
  have hxne : x≠0 := by intro h;rw [h,norm_zero,zero_pow (by omega)] at hx;linarith
  have hn : Real.sqrt q=‖x‖ := by rw [←hx,Real.sqrt_sq (norm_nonneg x)]
  have hgs : gramSchmidt ℝ (Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y) 0=x := by
    have h0 : (0 : Fin (K+1))=⊥ := by apply Fin.ext;rfl
    rw [h0,gramSchmidt_bot]
    rfl
  simp only [exactVector,hgs,Fin.cons_zero,rescale,hn,smul_smul,
    mul_inv_cancel₀ (norm_ne_zero_iff.mpr hxne),one_smul]

theorem actual_base_preserving_exactification (x : Vector N) (y : Fin K→Vector N)
    (q q' γ ε : ℝ) (hq : 0<q) (hq' : 0≤q') (hε : 0≤ε)
    (hgap : 0<γ-((K+1:ℕ):ℝ)*ε) (hx : ‖x‖^2=q)
    (hdiag : ∀i : Fin (K+1),γ≤‖Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y i‖^2)
    (hcross : ∀i j : Fin (K+1),i≠j→|⟪Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y i,Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y j⟫_ℝ|≤ε)
    (hy : ∀i,|‖y i‖^2-q'|≤ε) :
    ∃z : Fin K→Vector N,
      (∀i,‖z i‖^2=q') ∧ (∀i,⟪x,z i⟫_ℝ=0) ∧
      (∀i j,i≠j→⟪z i,z j⟫_ℝ=0) ∧
      (∀i,‖z i-y i‖≤2*Real.sqrt (((K+1:ℕ):ℝ)*ε^2/(γ-((K+1:ℕ):ℝ)*ε))+Real.sqrt ε) := by
  let v : Fin (K+1)→Vector N := Fin.cons (α := fun _ : Fin (K+1) => Vector N) x y
  let target : Fin (K+1)→ℝ := Fin.cons (α := fun _ : Fin (K+1) => ℝ) q (fun _ => q')
  have ht : ∀i,0≤target i := by
    intro i;refine Fin.cases ?_ (fun _ => ?_) i
    · exact hq.le
    · exact hq'
  have hnorm : ∀i,|‖v i‖^2-target i|≤ε := by
    intro i;refine Fin.cases ?_ (fun j => ?_) i
    · simpa only [v,target,Fin.cons_zero,hx,sub_self,abs_zero] using hε
    · simpa only [v,target,Fin.cons_succ] using hy j
  obtain ⟨hn,ho,hd⟩ := actual_exactification v target γ ε ε hε hε hgap ht hdiag hcross hnorm
  have hz : exactVector v target 0=x := exactVector_zero x y q q' hx hq
  refine ⟨fun i => exactVector v target i.succ,?_,?_,?_,?_⟩
  · intro i;simpa only [target,Fin.cons_succ] using hn i.succ
  · intro i;rw [←hz];exact ho 0 i.succ (Fin.succ_ne_zero i).symm
  · intro i j hij;exact ho i.succ j.succ (fun h => hij (Fin.succ_inj.mp h))
  · intro i;simpa only [v,Fin.cons_succ] using hd i.succ

end SphericalAging.GramForkExactification
