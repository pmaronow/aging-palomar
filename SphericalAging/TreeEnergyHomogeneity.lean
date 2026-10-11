module

public import SphericalAging.CenterNormalization
public import SphericalAging.TreeEnergyCeilings

public section

/-! Genuine homogeneity of the completed tree energy and normalization. -/
noncomputable section
set_option maxHeartbeats 600000
open scoped InnerProductSpace TensorProduct
namespace SphericalAging.TreeEnergyHomogeneity
open CausalTree TreeCeilings CenterNormalization CausalTreeRealization

namespace HilbertDatum

theorem pure_smul_smul (A B : CausalTree.HilbertDatum) (a b : ℝ)
    (x : A.Carrier) (y : B.Carrier) :
    CausalTree.HilbertDatum.pure A B (a • x) (b • y) =
      (a*b) • CausalTree.HilbertDatum.pure A B x y := by
  simp [CausalTree.HilbertDatum.pure, TensorProduct.smul_tmul, TensorProduct.tmul_smul,
    smul_smul, mul_comm]

theorem finitePure_diagonal_smul (n : ℕ) (A : Fin n → CausalTree.HilbertDatum)
    (x : ∀ i, (A i).Carrier) (a : ℝ) :
    CausalTree.HilbertDatum.finitePure n A (fun i => a • x i) =
      a^n • CausalTree.HilbertDatum.finitePure n A x := by
  induction n with
  | zero => simp [CausalTree.HilbertDatum.finitePure]
  | succ n ih =>
    rw [CausalTree.HilbertDatum.finitePure, ih, pure_smul_smul]
    simp only [CausalTree.HilbertDatum.finitePure,pow_succ]
    rw [mul_comm]

end HilbertDatum

theorem graftPower_smul {m : ℕ} (a : ℝ) (v : Space m) :
    graftPower (a • v) = a^m • graftPower v := by
  ext τ
  cases τ with
  | leaf => simp
  | graft ts =>
    simp only [graftPower_graft,lp.coeFn_smul,Pi.smul_apply]
    exact HilbertDatum.finitePure_diagonal_smul m (fun i => fiber (ts i)) (fun i => v (ts i)) a

theorem functional_smul {m : ℕ} (a : ℝ) (v : Space m) :
    functional (a • v) = a^(m+1)*functional v := by
  unfold functional
  rw [graftPower_smul,real_inner_smul_left,real_inner_smul_right,pow_succ]
  ring

theorem functional_unitize (v : Space 2) :
    functional (unitize v) = functional v/‖v‖^3 := by
  rw [unitize,functional_smul]
  simp only [inv_pow,div_eq_mul_inv]
  ring

theorem functional_unitize_treeEnergy (v : Space 2) :
    functional (unitize v) = treeEnergy 3 v/(Real.sqrt 3*‖v‖^3) := by
  rw [functional_unitize]
  change _ = (Real.sqrt 3*functional v)/(Real.sqrt 3*‖v‖^3)
  field_simp [Real.sqrt_ne_zero'.mpr (by norm_num : (0:ℝ)<3)]

theorem functional_unitize_any {m : ℕ} (v : Space m) :
    functional (unitize v)=functional v/‖v‖^(m+1) := by
  rw [unitize,functional_smul]
  simp only [inv_pow,div_eq_mul_inv]
  ring

theorem functional_unitize_treeEnergy_any {p : ℕ} (hp : 0<p) (v : Space (p-1)) :
    functional (unitize v)=treeEnergy p v/(Real.sqrt p*‖v‖^p) := by
  rw [functional_unitize_any,Nat.sub_add_cancel (show 1≤p by omega)]
  change _=(Real.sqrt p*functional v)/(Real.sqrt p*‖v‖^p)
  field_simp [Real.sqrt_ne_zero'.mpr (Nat.cast_pos.mpr hp : (0:ℝ)<p)]

theorem treeEnergy_unitize {p : ℕ} (hp : 0<p) (v : Space (p-1)) :
    treeEnergy p (unitize v)=treeEnergy p v/‖v‖^p := by
  change Real.sqrt p*functional (unitize v)=(Real.sqrt p*functional v)/‖v‖^p
  rw [functional_unitize_any,Nat.sub_add_cancel (show 1≤p by omega)]
  ring

end SphericalAging.TreeEnergyHomogeneity
