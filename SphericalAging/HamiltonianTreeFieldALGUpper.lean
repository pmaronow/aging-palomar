module

public import SphericalAging.HamiltonianTreeExpectedEdgeUpper
public import SphericalAging.PurePFiniteFieldExtension
public import SphericalAging.HamiltonianTreeFieldBand

public section

/-! Genuine finite expected-tree field ceiling, through the arbitrary-mesh
pure-p variational bound. The actual expected edges and finite branching
correction are retained; the leaf radius need only be at most one. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeFieldALGUpper
open Set MeasureTheory FiniteModel
open HamiltonianTreeExpectedEdgeUpper HamiltonianTreeFieldBand FieldAlignedSphereBase
open PurePFiniteFieldExtension PurePFiniteFieldBranchingBound PurePBranchingHighFieldBound
open PurePBranchingVariationalBound ExternalFieldElementaryPenalty
open scoped BigOperators
variable {N p K : ℕ}

@[expose]  def ascending (D : ℕ) (f : ℕ→ℝ) (i : ℕ) : ℝ := f (D-i)

 theorem ascending_monotone (D : ℕ) (f : ℕ→ℝ) (hf : ∀j,f (j+1)≤f j) :
     Monotone (ascending D f) := by
   intro i j hij
   exact (antitone_nat_of_succ_le hf) (Nat.sub_le_sub_left hij D)

 theorem ascending_mesh (D : ℕ) (Q : ℕ→ℝ) {δ : ℝ}
     (hmesh : ∀j<D,Q j-Q (j+1)≤δ) :
     ∀i<D,ascending D Q (i+1)-ascending D Q i≤δ := by
   intro i hi
   have hidx : D-(i+1)+1=D-i := by omega
   exact (show Q (D-(i+1))-Q (D-i)≤δ by
     rw [←hidx]
     exact hmesh (D-(i+1)) (by omega))

 theorem scalar_field_eq_ascending_sum (p D : ℕ) (κ : ℝ) (V Q : ℕ→ℝ) :
     discreteCeiling p D V Q+κ*Real.sqrt (Q D)=
       fieldBranchingSum p D κ (ascending D Q) (ascending D V) := by
   unfold fieldBranchingSum discreteCeiling
   simp only [ascending,Nat.sub_zero]
   rw [add_comm]
   congr 1
   rw [←Finset.sum_range_reflect]
   apply Finset.sum_congr rfl
   intro i hi
   have hiD : i<D := Finset.mem_range.mp hi
   have hidx : D-1-i+1=D-i := by omega
   have hidx' : D-(i+1)=D-1-i := by omega
   rw [hidx,hidx']
   unfold prime
   congr 1
   ring

 theorem expected_center_le_ascending_sum (hN : 0<N) (hp : 2≤p) (hK : 0<K) (hKN : K<N)
     (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
     (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (D : ℕ)
     (h : Vector N) {H : ℝ} (hfield : fieldSize N h≤H) :
     center (p:=p) (K:=K) hN V Q D h≤
       fieldBranchingSum p D H (ascending D Q) (ascending D V)+(D:ℝ)*Real.sqrt ((p:ℝ)/K) := by
   have he := expectedEdge_sum_upper hN hp hK hKN V Q hV hVm hQ hQm D
   have hf := mul_le_mul_of_nonneg_right hfield (Real.sqrt_nonneg (Q D))
   rw [←scalar_field_eq_ascending_sum]
   unfold HamiltonianTreeFieldBand.center
   linarith

 /-- The mesh is uniform in every dimension, tree depth, schedule and field
of normalized norm at most H. Only monotone schedules are required. -/
 theorem actual_expected_center_uniform_small_mesh (hp : 3≤p) {H η : ℝ}
     (hH : 0≤H) (hη : 0<η) :
     ∃δ>0,∀(N K D : ℕ)(hN : 0<N),0<K→K<N→
       ∀V Q : ℕ→ℝ,(∀j,0≤V j ∧ V j≤1)→(∀j,V (j+1)≤V j)→
         (∀j,0≤Q j ∧ Q j≤1)→(∀j,Q (j+1)≤Q j)→
         (∀j<D,Q j-Q (j+1)≤δ)→
       ∀h : Vector N,‖h‖≤Real.sqrt N*H→
       center (p:=p) (K:=K) hN V Q D h≤algorithmicField p H+η+(D:ℝ)*Real.sqrt ((p:ℝ)/K) := by
   obtain ⟨δ,hδ,hbound⟩ := fieldBranchingSum_uniform_small_mesh_of_leaf_le_one hp hH hη
   refine ⟨δ,hδ,?_⟩
   intro N K D hN hK hKN V Q hV hVm hQ hQm hmesh h hnorm
   have hf : fieldSize N h≤H := by
     have hn : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
     rw [fieldSize]
     exact (div_le_iff₀ hn).mpr (hnorm.trans_eq (mul_comm _ _))
   have he := expected_center_le_ascending_sum hN (by omega : 2≤p) hK hKN V Q hV hVm hQ hQm D h hf
   have hb := hbound D (ascending D Q) (ascending D V)
     (ascending_monotone D Q hQm) (by simpa only [ascending,Nat.sub_zero] using (hQ D).1)
     (by simpa only [ascending,Nat.sub_self] using (hQ 0).2)
     (ascending_monotone D V hVm) (fun i _ => hV (D-i)) (ascending_mesh D Q hmesh)
   exact he.trans (add_le_add hb le_rfl)

end SphericalAging.HamiltonianTreeFieldALGUpper
