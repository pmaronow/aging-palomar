module

public import SphericalAging.HamiltonianTreeEnergyProbability
public import SphericalAging.RegularTreeExternalFieldBound

public section

/-! The literal deterministic external field contribution to the actual
tree energy estimate. Spatial certificates are constructed from the same
descending-level orthogonal forks as the partial-variance Hamiltonian tree. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeExternalField
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping
open HamiltonianTreeEnergy HamiltonianTreeLocalEvents HamiltonianTreeEnergyProbability
open RegularTreeCentroidGeometry RegularTreeExternalFieldBound
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

theorem descending_geometry_is_forkTree (Q : ℕ→ℝ) (d : ℕ) (c : TreeData (Vector N) K d)
    (hc : TreeForkGeometry Q d c) : ForkTree (fun l => Q (d-l)) d c := by
  induction d with
  | zero => trivial
  | succ d ih =>
    obtain ⟨hc0,hci⟩ := hc
    refine ⟨?_,?_⟩
    · simpa only [Nat.sub_zero,Nat.add_sub_cancel_right] using hc0
    · intro i
      have hh := ih _ (hci i)
      simpa only [Nat.add_sub_add_right] using hh

theorem descending_geometry_field_bound (hN : 0<N) (hK : 0<K)
    (Q : ℕ→ℝ) (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (d : ℕ) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c)
    (hroot : ‖root d c‖^2=(N:ℝ)*Q d) (h : Vector N) (H : ℝ)
    (hH : 0≤H) (hbound : ‖h‖≤Real.sqrt N*H) :
    leafMean d (RegularTreeEnergyTelescoping.map (fun x => ⟪h,x⟫_ℝ) d c)/(N:ℝ)≤
      H*Real.sqrt (Q d)+H*Real.sqrt ((d:ℝ)/(K:ℝ)) := by
  have hqm : Monotone (fun l => Q (d-l)) := by
    intro i j hij
    exact (antitone_nat_of_succ_le hQm) (Nat.sub_le_sub_left hij d)
  have hh := actual_external_field_bound hN hK (fun l => Q (d-l)) hqm d
    (by simpa using (hQ d).1) (by simpa using (hQ 0).2) c
    (descending_geometry_is_forkTree Q d c hc) (by simpa using hroot) h H hH hbound
  simpa only [Nat.sub_zero] using hh

theorem actual_zeroRoot_total_leaf_energy_upper (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (hQ : ∀j,0≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j) (ε : ℝ)
    (d : ℕ) (hrootV : V d=0) (c : TreeData (Vector N) K d) (hc : TreeForkGeometry Q d c)
    (hroot : ‖root d c‖^2=(N:ℝ)*Q d) (h : Vector N) (H : ℝ)
    (hH : 0≤H) (hbound : ‖h‖≤Real.sqrt N*H)
    (s : TensorSpace N p) (z : TreeSample (TensorSpace N p) K d)
    (hz : (s,z)∈treeEvent V Q ε d) :
    leafMean d (energyTree V d c s z)+
        leafMean d (RegularTreeEnergyTelescoping.map (fun x => ⟪h,x⟫_ℝ) d c)/(N:ℝ)≤
      (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) (by omega) V Q j)+
        (d:ℝ)*ε+H*Real.sqrt (Q d)+H*Real.sqrt ((d:ℝ)/(K:ℝ)) := by
  have he := actual_zeroRoot_leaf_energy_upper hp hK hKN V Q hV hVm hQ hQm ε d hrootV c hc s z hz
  have hf := descending_geometry_field_bound (by omega) hK Q hQ hQm d c hc hroot h H hH hbound
  exact (add_le_add he hf).trans_eq (by ring)

end SphericalAging.HamiltonianTreeExternalField
