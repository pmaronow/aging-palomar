module

public import SphericalAging.CentroidOverlapEstimates

public section

/-! Literal innerPairing expansion along two finite paths after their shared
prefix. Every error comes from actual root/edge and edge/edge pairings. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
namespace SphericalAging.FinitePathInnerExpansion
open FiniteModel
open scoped BigOperators InnerProductSpace
variable {N A B C : ℕ}

@[expose] def innerPairing (x y : Vector N) : ℝ := ⟪x,y⟫_ℝ

theorem innerPairing_add_left (x y z : Vector N) :
    innerPairing (x+y) z=innerPairing x z+innerPairing y z := by
  simp only [innerPairing,inner_add_left]

theorem innerPairing_add_right (x y z : Vector N) :
    innerPairing x (y+z)=innerPairing x y+innerPairing x z := by
  simp only [innerPairing,inner_add_right]

theorem innerPairing_sum_left {K : ℕ} (a : Fin K→Vector N) (x : Vector N) :
    innerPairing (∑i,a i) x=∑i,innerPairing (a i) x := by
  simp only [innerPairing,sum_inner]

theorem innerPairing_sum_right {K : ℕ} (x : Vector N) (a : Fin K→Vector N) :
    innerPairing x (∑i,a i)=∑i,innerPairing x (a i) := by
  simp only [innerPairing,inner_sum]

theorem innerPairing_comm (x y : Vector N) : innerPairing x y=innerPairing y x := by
  simp only [innerPairing,real_inner_comm]

theorem finite_abs_sum_bound {K : ℕ} (f : Fin K→ℝ) (e : ℝ)
    (hf : ∀i,|f i|≤e) : |∑i,f i|≤(K:ℝ)*e := by
  calc
    _≤∑i,|f i| := Finset.abs_sum_le_sum_abs _ _
    _≤∑_i : Fin K,e := Finset.sum_le_sum (fun i _ => hf i)
    _=_ := by simp

theorem shared_branch_innerPairing_bound (x : Vector N) (c : Fin C→Vector N)
    (v : Vector N) (ε : ℝ) (hx : |innerPairing x v|≤ε)
    (hc : ∀i,|innerPairing (c i) v|≤ε) :
    |innerPairing (x+∑i,c i) v|≤((C:ℝ)+1)*ε := by
  rw [innerPairing_add_left,innerPairing_sum_left]
  exact (abs_add_le _ _).trans ((add_le_add hx (finite_abs_sum_bound _ ε hc)).trans
    (by ring_nf; rfl))

theorem path_innerPairing_expansion (x : Vector N) (c : Fin C→Vector N)
    (a : Fin A→Vector N) (b : Fin B→Vector N) (r η ε : ℝ)
    (hw : |innerPairing (x+∑i,c i) (x+∑i,c i)-r|≤η)
    (hxa : ∀i,|innerPairing x (a i)|≤ε) (hxb : ∀j,|innerPairing x (b j)|≤ε)
    (hca : ∀i j,|innerPairing (c i) (a j)|≤ε)
    (hcb : ∀i j,|innerPairing (c i) (b j)|≤ε)
    (hab : ∀i j,|innerPairing (a i) (b j)|≤ε) :
    |innerPairing ((x+∑i,c i)+∑i,a i) ((x+∑i,c i)+∑j,b j)-r|≤
      η+(((A:ℝ)+(B:ℝ))*((C:ℝ)+1)+(A:ℝ)*(B:ℝ))*ε := by
  let w := x+∑i,c i
  have hwa : |innerPairing (∑i,a i) w|≤(A:ℝ)*(((C:ℝ)+1)*ε) := by
    rw [innerPairing_comm,innerPairing_sum_right]
    exact finite_abs_sum_bound _ _ (fun i => shared_branch_innerPairing_bound x c (a i) ε
      (hxa i) (fun j => hca j i))
  have hwb : |innerPairing w (∑j,b j)|≤(B:ℝ)*(((C:ℝ)+1)*ε) := by
    rw [innerPairing_sum_right]
    exact finite_abs_sum_bound _ _ (fun j => shared_branch_innerPairing_bound x c (b j) ε
      (hxb j) (fun i => hcb i j))
  have habs : |innerPairing (∑i,a i) (∑j,b j)|≤(A:ℝ)*((B:ℝ)*ε) := by
    rw [innerPairing_sum_left]
    apply finite_abs_sum_bound
    intro i
    rw [innerPairing_sum_right]
    exact finite_abs_sum_bound _ ε (hab i)
  have he : innerPairing (w+∑i,a i) (w+∑j,b j)-r=
      (innerPairing w w-r)+innerPairing w (∑j,b j)+
        innerPairing (∑i,a i) w+innerPairing (∑i,a i) (∑j,b j) := by
    simp only [innerPairing_add_left,innerPairing_add_right]
    ring
  change |innerPairing (w+∑i,a i) (w+∑j,b j)-r|≤_
  rw [he]
  calc
    _≤(|innerPairing w w-r|+|innerPairing w (∑j,b j)|)+|innerPairing (∑i,a i) w|+
        |innerPairing (∑i,a i) (∑j,b j)| :=
      (abs_add_le _ _).trans (add_le_add
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) (le_refl _))) (le_refl _))
    _≤(η+(B:ℝ)*(((C:ℝ)+1)*ε))+(A:ℝ)*(((C:ℝ)+1)*ε)+(A:ℝ)*((B:ℝ)*ε) :=
      add_le_add (add_le_add (add_le_add hw hwb) hwa) habs
    _=_ := by ring

theorem path_innerPairing_depth_bound (x : Vector N) (c : Fin C→Vector N)
    (a : Fin A→Vector N) (b : Fin B→Vector N) (r η ε : ℝ) (hε : 0≤ε)
    (D : ℕ) (hD : 1≤D) (hA : A≤D) (hB : B≤D) (hC : C≤D)
    (hw : |innerPairing (x+∑i,c i) (x+∑i,c i)-r|≤η)
    (hxa : ∀i,|innerPairing x (a i)|≤ε) (hxb : ∀j,|innerPairing x (b j)|≤ε)
    (hca : ∀i j,|innerPairing (c i) (a j)|≤ε)
    (hcb : ∀i j,|innerPairing (c i) (b j)|≤ε)
    (hab : ∀i j,|innerPairing (a i) (b j)|≤ε) :
    |innerPairing ((x+∑i,c i)+∑i,a i) ((x+∑i,c i)+∑j,b j)-r|≤η+5*(D:ℝ)^2*ε := by
  have ha : (A:ℝ)≤D := Nat.cast_le.mpr hA
  have hb : (B:ℝ)≤D := Nat.cast_le.mpr hB
  have hc : (C:ℝ)≤D := Nat.cast_le.mpr hC
  have hd : (1:ℝ)≤D := by exact_mod_cast hD
  have hc2 : (C:ℝ)+1≤2*D := by linarith
  have hab2 : (A:ℝ)+(B:ℝ)≤2*D := by linarith
  have hprod := mul_le_mul hab2 hc2 (by positivity : 0≤(C:ℝ)+1) (by positivity : 0≤2*(D:ℝ))
  have habprod := mul_le_mul ha hb (Nat.cast_nonneg B) (Nat.cast_nonneg D)
  have hcoeff : ((A:ℝ)+(B:ℝ))*((C:ℝ)+1)+(A:ℝ)*(B:ℝ)≤5*(D:ℝ)^2 := by nlinarith
  exact (path_innerPairing_expansion x c a b r η ε hw hxa hxb hca hcb hab).trans
    (add_le_add (le_refl η) (mul_le_mul_of_nonneg_right hcoeff hε))

end SphericalAging.FinitePathInnerExpansion
