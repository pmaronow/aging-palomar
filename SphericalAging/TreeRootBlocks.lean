module

public import SphericalAging.TreeCoherentRoot
public import SphericalAging.HilbertTensorContraction

public section

/-! Genuine binary height blocks of the completed-tensor coherent root. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open scoped InnerProductSpace ENNReal NNReal TensorProduct Topology
open Set MeasureTheory Filter UniformSpace
namespace SphericalAging.TreeRootBlocks
open CausalTree CausalTree.HilbertDatum TreeCeilings TreeCoherentRoot
local instance (α : Type) : DecidableEq α := Classical.decEq α

/-- The actual ordered two-factor pure tensor, including its canonical right unit. -/
@[expose] def binaryPure (x y : Space 2) : TensorSpace 2 := finitePure 2 (fun _ => spaceDatum 2) ![x,y]

@[expose] def binaryGraft (x y : Space 2) : Space 2 := graftTensor 2 (binaryPure x y)

theorem binaryPure_inner (x y u v : Space 2) :
    inner ℝ (binaryPure x y) (binaryPure u v)=inner ℝ x u*inner ℝ y v := by
  rw [binaryPure,binaryPure,inner_finitePure]
  simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,mul_one]

theorem binaryGraft_coordinate (x y : Space 2) (ts : Fin 2 → CausalTree.Tree 2) :
    binaryGraft x y (CausalTree.Tree.graft ts)=
      finitePure 2 (fun i => fiber (ts i)) (fun i => (![x,y] i) (ts i)) := by
  change graft (tensorDomainEquiv 2 (binaryPure x y)) (CausalTree.Tree.graft ts)=_
  rw [graft_graft,binaryPure,tensorDomainEquiv_pure]

/-- Actual grafts of two height-pure factors live at one plus the larger height. -/
theorem binaryGraft_height_support (i k : ℕ) (x y : Space 2) :
    heightProjection (max i k+1) (binaryGraft (heightProjection i x) (heightProjection k y))=
      binaryGraft (heightProjection i x) (heightProjection k y) := by
  apply lp.ext
  funext τ
  cases τ with
  | leaf =>
    rw [heightProjection_apply]
    have hz : binaryGraft (heightProjection i x) (heightProjection k y) CausalTree.Tree.leaf=0 := by
      change graft _ CausalTree.Tree.leaf=0
      exact graft_leaf _
    rw [hz]
    split_ifs <;> rfl
  | graft ts =>
    have hheight : (CausalTree.Tree.graft ts).height=1+max (ts 0).height (ts 1).height := by
      rw [CausalTree.Tree.height_graft,Finset.univ_fin2]
      simp only [Finset.sup_insert,Finset.sup_singleton]
    by_cases hi : (ts 0).height=i
    · by_cases hk : (ts 1).height=k
      · rw [heightProjection_apply,hheight,hi,hk,show 1+max i k=max i k+1 from by omega,if_pos rfl]
      · have hz : binaryGraft (heightProjection i x) (heightProjection k y) (CausalTree.Tree.graft ts)=0 := by
          rw [binaryGraft_coordinate]
          apply norm_eq_zero.mp
          rw [norm_finitePure]
          simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,
            heightProjection_apply,show (Fin.succ (0 : Fin 1) : Fin 2)=1 from rfl,
            if_neg hk,norm_zero,mul_zero,zero_mul]
        rw [heightProjection_apply,hz]
        split_ifs <;> rfl
    · have hz : binaryGraft (heightProjection i x) (heightProjection k y) (CausalTree.Tree.graft ts)=0 := by
        rw [binaryGraft_coordinate]
        apply norm_eq_zero.mp
        rw [norm_finitePure]
        simp only [Fin.prod_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_zero,
          heightProjection_apply,if_neg hi,norm_zero,zero_mul]
      rw [heightProjection_apply,hz]
      split_ifs <;> rfl

/-- Height projections are genuinely self-adjoint on the actual Hilbert direct sum. -/
theorem heightProjection_selfAdjoint {m : ℕ} (j : ℕ) (v w : Space m) :
    inner ℝ (heightProjection j v) w=inner ℝ v (heightProjection j w) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro τ
  simp only [heightProjection_apply]
  split_ifs <;> simp

/-- The coherent root's exact actual child-height block pairing. -/
theorem coherentRoot_block_pairing (v x y : Space 2) (i k : ℕ) :
    inner ℝ (coherentRoot v) (binaryPure (heightProjection i x) (heightProjection k y)) =
      (cubicWeight v (max i k+1))⁻¹*
        (inner ℝ v (heightProjection i x)*inner ℝ v (heightProjection k y)) := by
  have hs := binaryGraft_height_support i k x y
  have hmove (u : Space 2) : inner ℝ u (binaryGraft (heightProjection i x) (heightProjection k y))=
      inner ℝ (heightProjection (max i k+1) u)
        (binaryGraft (heightProjection i x) (heightProjection k y)) := by
    rw [heightProjection_selfAdjoint,hs]
  calc
    _ = inner ℝ (coherentTree v) (binaryGraft (heightProjection i x) (heightProjection k y)) := by
      exact ((graftTensor 2).inner_map_map (coherentRoot v)
        (binaryPure (heightProjection i x) (heightProjection k y))).symm.trans
          (by rw [graft_coherentRoot]; rfl)
    _ = _ := by
      rw [hmove,coherentTree_height_succ,coherentShell,real_inner_smul_left,←hmove (graftPower v)]
      rw [←graftTensor_power]
      unfold binaryGraft
      rw [(graftTensor 2).inner_map_map]
      have hp : standardTensorPower v=binaryPure v v := by
        unfold standardTensorPower binaryPure
        congr 1
        funext j
        fin_cases j <;> rfl
      rw [hp,binaryPure_inner]

end SphericalAging.TreeRootBlocks
