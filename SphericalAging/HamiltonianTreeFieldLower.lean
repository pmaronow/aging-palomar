module

public import SphericalAging.HamiltonianTreeEnergyBand
public import SphericalAging.HamiltonianTreeExternalField
public import SphericalAging.FieldAlignedSphereBase

public section

/-! The matching external-field lower estimate for a genuinely constructed
greedy Hamiltonian tree with its root aligned to the actual field. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeFieldLower
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping
open HamiltonianTreeEnergy HamiltonianTreeLocalEvents HamiltonianTreeEnergyBand HamiltonianTreeExternalField
open RegularTreeCentroidGeometry RegularTreeExternalFieldBound FieldAlignedSphereBase
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

theorem actual_field_centroid_deviation (hN : 0<N) (hK : 0<K)
    (Q : ℕ→ℝ) (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (d : ℕ) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c) (h : Vector N) :
    |leafMean d (RegularTreeEnergyTelescoping.map (fun x => ⟪h,x⟫_ℝ) d c)/(N:ℝ)-
      ⟪h,root d c⟫_ℝ/(N:ℝ)|≤fieldSize N h*Real.sqrt ((d:ℝ)/(K:ℝ)) := by
  have hdim : 0<(N:ℝ) := Nat.cast_pos.mpr hN
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hdim
  have hqm : Monotone (fun l => Q (d-l)) := by
    intro i j hij
    exact (antitone_nat_of_succ_le hQm) (Nat.sub_le_sub_left hij d)
  have hcent := actual_source_HS_2_9 hN hK (fun l => Q (d-l)) hqm d
    (by simpa using (hQ d).1) (by simpa using (hQ 0).2) c
    (descending_geometry_is_forkTree Q d c hc)
  rw [leafMean_inner_eq hK,←sub_div,←inner_sub_right,abs_div,abs_of_pos hdim]
  calc
    _≤(‖h‖*‖leafCentroid d c-root d c‖)/(N:ℝ) :=
      div_le_div_of_nonneg_right (abs_real_inner_le_norm _ _) hdim.le
    _=fieldSize N h*(‖leafCentroid d c-root d c‖/Real.sqrt N) := by
      rw [field_norm hN h]
      field_simp [hdim.ne',hs.ne']
      ring_nf
      rw [Real.sq_sqrt hdim.le]
      ring
    _≤_ := mul_le_mul_of_nonneg_left hcent (fieldSize_nonneg h)

theorem actual_zeroRoot_total_leaf_energy_lower (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (hroot : V d=0) (h : Vector N)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    ∃c : TreeData (Vector N) K d,TreeForkGeometry Q d c ∧
      ‖root d c‖^2=(N:ℝ)*Q d ∧
      (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j)+
          fieldSize N h*Real.sqrt (Q d)-(d:ℝ)*ε-fieldSize N h*Real.sqrt ((d:ℝ)/(K:ℝ))≤
        leafMean d (energyTree V d c s z)+
          leafMean d (RegularTreeEnergyTelescoping.map (fun x => ⟪h,x⟫_ℝ) d c)/(N:ℝ) := by
  have hN : 0<N := by omega
  obtain ⟨c,hcx,hc,he⟩ := actual_zeroRoot_leaf_energy_lower hp hK hKN V Q hV hVm hQ hQm ε d hroot
    (alignedBase N hN (Q d) h) (alignedBase_norm hN _ (hQ _).1 h) s z hz
  have hf := actual_field_centroid_deviation hN hK Q hQ hQm d c hc h
  rw [hcx,alignedBase_pairing hN _ (hQ _).1 h] at hf
  refine ⟨c,hc,?_,?_⟩
  · rw [hcx]
    exact alignedBase_norm hN _ (hQ _).1 h
  · have hl := (neg_le_abs _).trans hf
    linarith

end SphericalAging.HamiltonianTreeFieldLower
