module

public import SphericalAging.HamiltonianTreeFieldLower

public section

/-! Genuine two-sided finite-tree energy estimate including the literal
external field, under the constructed Gaussian branching law. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.HamiltonianTreeFieldBand
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping BranchingTreeLocalEvents
open HamiltonianTreeEnergy HamiltonianTreeLocalEvents HamiltonianTreeEnergyProbability
open HamiltonianTreeExternalField FieldAlignedSphereBase HamiltonianTreeFieldLower
open scoped BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def center (hN : 0<N) (V Q : ℕ→ℝ) (d : ℕ) (h : Vector N) : ℝ :=
  (∑j∈Finset.range d,expectedEdge (N:=N) (p:=p) (K:=K) hN V Q j)+fieldSize N h*Real.sqrt (Q d)

@[expose] def error (N K d : ℕ) (ε : ℝ) (h : Vector N) : ℝ :=
  (d:ℝ)*ε+fieldSize N h*Real.sqrt ((d:ℝ)/(K:ℝ))

@[expose] def totalLeafEnergy (V : ℕ→ℝ) (d : ℕ) (h : Vector N) (c : TreeData (Vector N) K d)
    (z : TensorSpace N p×TreeSample (TensorSpace N p) K d) : ℝ :=
  leafMean d (energyTree V d c z.1 z.2)+
    leafMean d (RegularTreeEnergyTelescoping.map (fun x => ⟪h,x⟫_ℝ) d c)/(N:ℝ)

theorem actual_finite_tree_field_band (hp : 1≤p) (hK : 0<K) (hKN : K<N)
    (V Q : ℕ→ℝ) (hV : ∀j,0≤V j ∧ V j≤1) (hVm : ∀j,V (j+1)≤V j)
    (δ : ℝ) (hδ : 0<δ) (hQ : ∀j,δ≤Q j ∧ Q j≤1) (hQm : ∀j,Q (j+1)≤Q j)
    (ε : ℝ) (hε : 0<ε) (d : ℕ) (hroot : V d=0) (h : Vector N) :
    ∃E : Set (TensorSpace N p×TreeSample (TensorSpace N p) K d),MeasurableSet E ∧
      1-failureBudget K (fun _ => localFailure N p K δ ε) d≤
        ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real E ∧
      ∀z∈E,
        (∀c : TreeData (Vector N) K d,TreeForkGeometry Q d c→‖root d c‖^2=(N:ℝ)*Q d→
          totalLeafEnergy V d h c z≤center (p:=p) (K:=K) (by omega) V Q d h+error N K d ε h) ∧
        (∃c : TreeData (Vector N) K d,TreeForkGeometry Q d c ∧ ‖root d c‖^2=(N:ℝ)*Q d ∧
          center (p:=p) (K:=K) (by omega) V Q d h-error N K d ε h≤totalLeafEnergy V d h c z) := by
  have hN : 0<N := by omega
  have hQ0 : ∀j,0≤Q j ∧ Q j≤1 := fun j => ⟨hδ.le.trans (hQ j).1,(hQ j).2⟩
  refine ⟨treeEvent V Q ε d,treeEvent_measurable hp hK hKN V Q hV hVm hQ0 hQm ε d,
    actual_simultaneous_tree_success_probability hp hK hKN V Q hV hVm δ hδ hQ hQm ε hε d,?_⟩
  intro z hz
  constructor
  · intro c hc hx
    have hh := actual_zeroRoot_total_leaf_energy_upper hp hK hKN V Q hV hVm hQ0 hQm ε d hroot
      c hc hx h (fieldSize N h) (fieldSize_nonneg h) (field_norm hN h).le z.1 z.2 hz
    exact hh.trans_eq (by unfold center error;ring)
  · obtain ⟨c,hc,hx,hh⟩ := actual_zeroRoot_total_leaf_energy_lower hp hK hKN V Q hV hVm hQ0 hQm ε d hroot h z.1 z.2 hz
    refine ⟨c,hc,hx,?_⟩
    exact (show center (p:=p) (K:=K) hN V Q d h-error N K d ε h=_ from by
      unfold center error;ring).trans_le hh

end SphericalAging.HamiltonianTreeFieldBand
