module

public import SphericalAging.BinaryRootTransport
public import SphericalAging.CoherentRootSamplingTheorem

public section

/-! Actual finite rectangle expansions of the coherent root and their
strong convergence, with no step-kernel identification assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.CoherentRootFiniteGrid
open CausalTree CausalTree.HilbertDatum TreeCeilings TreeCoherentRoot TreeRootBlocks
open HeightCoordinateIntervals UniversalRootInterval BinaryRootTransport
local instance (α : Type*) : DecidableEq α := Classical.decEq α

@[expose] def coefficient (v : Space 2) (i j : ℕ) : ℝ := (cubicWeight v (max i j+1))⁻¹

@[expose] def gridTensor (v : Space 2) (n : ℕ) : TensorSpace 2 :=
  ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1),
    coefficient v i j • binaryPure (heightProjection i v) (heightProjection j v)

@[expose] def gridKernel (v : Space 2) (n : ℕ) : KernelL2 :=
  ∑ i ∈ Finset.range (n+1), ∑ j ∈ Finset.range (n+1),
    coefficient v i j • LpProductTensor.product (heightIndicator v i) (heightIndicator v j)

theorem heightPairing (v x : Space 2) (a i : ℕ) :
    inner ℝ (heightProjection a v) (heightProjection i x)=
      if a=i then inner ℝ v (heightProjection i x) else 0 := by
  by_cases h : a=i
  · subst a
    rw [heightProjection_selfAdjoint,heightProjection_idempotent,if_pos rfl]
  · rw [heightProjection_orthogonal a i h,if_neg h]

theorem gridTensor_height_pairing (v x y : Space 2) (n i j : ℕ) :
    inner ℝ (gridTensor v n) (binaryPure (heightProjection i x) (heightProjection j y))=
      if i≤n ∧ j≤n then coefficient v i j*
        (inner ℝ v (heightProjection i x)*inner ℝ v (heightProjection j y)) else 0 := by
  unfold gridTensor
  simp only [sum_inner,real_inner_smul_left]
  have he (a b : ℕ) : inner ℝ (binaryPure (heightProjection a v) (heightProjection b v))
      (binaryPure (heightProjection i x) (heightProjection j y))=
      (if a=i then inner ℝ v (heightProjection i x) else 0)*
        (if b=j then inner ℝ v (heightProjection j y) else 0) := by
    rw [TreeRootBlocks.binaryPure_inner,heightPairing,heightPairing]
  simp only [he]
  by_cases hi : i≤n
  · by_cases hj : j≤n
    · rw [if_pos ⟨hi,hj⟩]
      rw [Finset.sum_eq_single i]
      · rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp only [if_neg hbj,mul_zero]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr (by omega))).elim
      · intro a ha hai
        simp only [if_neg hai,zero_mul,mul_zero,Finset.sum_const_zero]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim
    · rw [if_neg (by tauto)]
      apply Finset.sum_eq_zero
      intro a ha
      apply Finset.sum_eq_zero
      intro b hb
      have hbj : b≠j := by intro he; subst b; have := Finset.mem_range.mp hb; omega
      simp only [if_neg hbj,mul_zero]
  · rw [if_neg (by tauto)]
    apply Finset.sum_eq_zero
    intro a ha
    have hai : a≠i := by intro he; subst a; have := Finset.mem_range.mp ha; omega
    simp only [if_neg hai,zero_mul,mul_zero,Finset.sum_const_zero]

theorem heightPrefix_selfAdjoint (n : ℕ) (x y : Space 2) :
    inner ℝ (heightPrefix n x) y=inner ℝ x (heightPrefix n y) := by
  rw [lp.inner_eq_tsum,lp.inner_eq_tsum]
  apply tsum_congr
  intro t
  simp only [heightPrefix_apply]
  split_ifs <;> simp

theorem heightPrefix_of_pureHeight (n k : ℕ) (x : Space 2) (hx : heightProjection k x=x) :
    heightPrefix n x=if k≤n then x else 0 := by
  by_cases hk : k≤n
  · rw [if_pos hk,←hx]
    apply lp.ext
    funext t
    simp only [heightPrefix_apply,heightProjection_apply]
    by_cases ht : t.height=k
    · have hn : t.height≤n := ht.symm ▸ hk
      simp [ht,hn,hk]
    · simp [ht]
  · rw [if_neg hk,←hx]
    apply lp.ext
    funext t
    simp only [heightPrefix_apply,heightProjection_apply,lp.coeFn_zero]
    by_cases ht : t.height=k
    · have hn : ¬t.height≤n := ht.symm ▸ hk
      simp [ht,hn,hk]
    · simp [ht]


theorem rootPrefix_height_pairing (v x y : Space 2) (n i j : ℕ) :
    inner ℝ (graftTensorAdjoint 2 (heightPrefix (n+1) (coherentTree v)))
      (binaryPure (heightProjection i x) (heightProjection j y))=
      if i≤n ∧ j≤n then coefficient v i j*
        (inner ℝ v (heightProjection i x)*inner ℝ v (heightProjection j y)) else 0 := by
  rw [real_inner_comm,←graftTensor_adjoint_identity,real_inner_comm]
  change inner ℝ (heightPrefix (n+1) (coherentTree v))
    (binaryGraft (heightProjection i x) (heightProjection j y))=_
  rw [heightPrefix_selfAdjoint,heightPrefix_of_pureHeight (n+1) (max i j+1) _
    (binaryGraft_height_support i j x y)]
  by_cases h : i≤n ∧ j≤n
  · rw [if_pos (by omega),if_pos h]
    change inner ℝ (coherentTree v) (graftTensor 2 (binaryPure (heightProjection i x) (heightProjection j y)))=_
    rw [real_inner_comm,graftTensor_adjoint_identity,real_inner_comm]
    exact coherentRoot_block_pairing v x y i j
  · rw [if_neg (by omega),if_neg h,inner_zero_right]

theorem binary_tensor_eq_of_height_pairings {u w : TensorSpace 2}
    (h : ∀ x y i j, inner ℝ u (binaryPure (heightProjection i x) (heightProjection j y))=
      inner ℝ w (binaryPure (heightProjection i x) (heightProjection j y))) : u=w := by
  have hp (x y : Space 2) : inner ℝ u (binaryPure x y)=inner ℝ w (binaryPure x y) := by
    have hfinite (n : ℕ) : inner ℝ u (binaryPure (heightPrefix n x) (heightPrefix n y))=
        inner ℝ w (binaryPure (heightPrefix n x) (heightPrefix n y)) := by
      rw [TreeCoherentOperator.heightPrefix_eq_sum,TreeCoherentOperator.heightPrefix_eq_sum]
      have he : binaryPure (∑ i ∈ Finset.range (n+1),heightProjection i x)
          (∑ j ∈ Finset.range (n+1),heightProjection j y)=
          ∑ i ∈ Finset.range (n+1),∑ j ∈ Finset.range (n+1),
            binaryPure (heightProjection i x) (heightProjection j y) := by
        apply binaryEquiv.injective
        have hp (a b : Space 2) : binaryEquiv (binaryPure a b)=
            pure (spaceDatum 2) (spaceDatum 2) a b := BinaryRootTransport.binaryEquiv_pure a b
        rw [hp]
        simp only [map_sum]
        calc
          _ = ∑ i ∈ Finset.range (n+1),∑ j ∈ Finset.range (n+1),
              pure (spaceDatum 2) (spaceDatum 2) (heightProjection i x) (heightProjection j y) := by
            simp only [CausalTree.HilbertDatum.pure,TensorProduct.sum_tmul,TensorProduct.tmul_sum]
            change UniformSpace.Completion.toCompl
                (∑ j ∈ Finset.range (n+1),∑ i ∈ Finset.range (n+1),
                  heightProjection i x ⊗ₜ[ℝ] heightProjection j y)=_
            simp only [map_sum]
            rw [Finset.sum_comm]
            rfl
          _ = _ := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro j hj
            exact (hp _ _).symm
      rw [he]
      simp only [inner_sum,h]
    have hcont : Continuous (fun z : Space 2 × Space 2 => binaryPure z.1 z.2) := by
      have he : (fun z : Space 2 × Space 2 => binaryPure z.1 z.2)=
          fun z => binaryEquiv.symm (pure (spaceDatum 2) (spaceDatum 2) z.1 z.2) := by
        funext z
        rw [←binaryEquiv_pure,LinearIsometryEquiv.symm_apply_apply]
      rw [he]
      apply binaryEquiv.symm.continuous.comp
      exact (UniformSpace.Completion.continuous_coe _).comp TensorProduct.continuous_tmul
    have ht := hcont.tendsto (x,y) |>.comp ((heightPrefix_tendsto x).prodMk_nhds (heightPrefix_tendsto y))
    have hu := (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u)).inner (𝕜:=ℝ) ht
    have hw := (tendsto_const_nhds : Tendsto (fun _ : ℕ => w) atTop (𝓝 w)).inner (𝕜:=ℝ) ht
    apply tendsto_nhds_unique hu
    apply hw.congr'
    exact Eventually.of_forall (fun n => (hfinite n).symm)
  apply binaryEquiv.injective
  apply HilbertSchmidtTensor.operator_injective (spaceDatum 2) (spaceDatum 2)
  apply ContinuousLinearMap.ext
  intro y
  apply ext_inner_left ℝ
  intro x
  rw [HilbertSchmidtTensor.operator_pairing,HilbertSchmidtTensor.operator_pairing,←binaryEquiv_pure,
    binaryEquiv.inner_map_map,binaryEquiv.inner_map_map,real_inner_comm]
  exact (hp x y).trans (by rw [real_inner_comm])

theorem gridTensor_eq_rootPrefix (v : Space 2) (n : ℕ) :
    gridTensor v n=graftTensorAdjoint 2 (heightPrefix (n+1) (coherentTree v)) := by
  apply binary_tensor_eq_of_height_pairings
  intro x y i j
  rw [gridTensor_height_pairing,rootPrefix_height_pairing]

theorem gridTensor_tendsto (v : Space 2) :
    Tendsto (gridTensor v) atTop (𝓝 (coherentRoot v)) := by
  change Tendsto (fun n => gridTensor v n) atTop (𝓝 (coherentRoot v))
  simp_rw [gridTensor_eq_rootPrefix]
  exact (graftTensorAdjoint 2).continuous.tendsto (coherentTree v) |>.comp
    ((heightPrefix_tendsto (coherentTree v)).comp (tendsto_add_atTop_nat 1))

theorem transported_gridKernel (v : Space 2) (hv : ‖v‖=1) (n : ℕ) :
    transport v hv (gridTensor v n)=kernelInclusion (gridKernel v n) := by
  simp only [gridTensor,gridKernel,map_sum,map_smul]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [transport_height_rankOne,kernelInclusion_product]

end SphericalAging.CoherentRootFiniteGrid
