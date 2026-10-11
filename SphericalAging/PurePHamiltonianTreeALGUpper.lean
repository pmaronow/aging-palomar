module

public import SphericalAging.HamiltonianTreeFieldALGUpper
public import SphericalAging.PurePHamiltonianTreeProposition33

public section

/-! An actual common high-probability pure-p tree-energy ALG ceiling.
The finite expected-edge and spatial concentration estimates are combined
with the genuine arbitrary-mesh variational bound, retaining all errors. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PurePHamiltonianTreeALGUpper
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping HamiltonianTreeLocalEvents BranchingTreeLocalEvents
open HamiltonianTreeEnergy HamiltonianTreeFieldBand HamiltonianTreeFieldALGUpper PurePHamiltonianTreeProposition33
open ExternalFieldElementaryPenalty
open scoped BigOperators
variable {p : ℕ}

 theorem actual_tree_field_alg_ceiling (hp : 3≤p) {H η : ℝ} (hH : 0≤H) (hη : 0<η) :
     ∃δ>0,∀(D : ℕ)(γ ε : ℝ),0<γ→0<ε→
       ∃K0 : ℕ,0<K0 ∧ ∀K≥K0,∃N0 : ℕ,∃hN0 : K<N0,∀(N : ℕ)(hNN : N0≤N),
         ∀V Q : ℕ→ℝ,(∀j,0≤V j ∧ V j≤1)→(∀j,V (j+1)≤V j)→
           (∀j,γ≤Q j ∧ Q j≤1)→(∀j,Q (j+1)≤Q j)→V D=0→
           (∀j<D,Q j-Q (j+1)≤δ)→
         ∀h : Vector N,‖h‖≤Real.sqrt N*H→
         ∃E : Set (TensorSpace N p×TreeSample (TensorSpace N p) K D),MeasurableSet E ∧
           1-Real.exp (-(N:ℝ)/2)≤
             ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)).real E ∧
           ∀z∈E,∀c : TreeData (Vector N) K D,TreeForkGeometry Q D c→‖root D c‖^2=(N:ℝ)*Q D→
             totalLeafEnergy V D h c z≤algorithmicField p H+η+(D:ℝ)*Real.sqrt ((p:ℝ)/K)+2*(D:ℝ)*ε := by
   obtain ⟨δ,hδ,hcenter⟩ := actual_expected_center_uniform_small_mesh hp hH hη
   refine ⟨δ,hδ,?_⟩
   intro D γ ε hγ hε
   obtain ⟨K0,hK0,hband⟩ := actual_source_HS_3_3_pureP (p:=p) (by omega) D γ ε H hγ hε hH
   refine ⟨K0,hK0,?_⟩
   intro K hK
   obtain ⟨N0,hN0,hbandN⟩ := hband K hK
   refine ⟨N0,hN0,?_⟩
   intro N hNN V Q hV hVm hQ hQm hroot hmesh h hnorm
   have hN : 0<N := by omega
   have hKpos : 0<K := by omega
   have hKN : K<N := hN0.trans_le hNN
   have hQ0 : ∀j,0≤Q j ∧ Q j≤1 := fun j => ⟨hγ.le.trans (hQ j).1,(hQ j).2⟩
   have hc := hcenter N K D hN hKpos hKN V Q hV hVm hQ0 hQm hmesh h hnorm
   obtain ⟨E,hEm,hEp,hE⟩ := hbandN N hNN V Q hV hVm hQ hQm hroot h hnorm
   refine ⟨E,hEm,hEp,?_⟩
   intro z hz c hcf hcn
   have he := (hE z hz).1 c hcf hcn
   exact he.trans (add_le_add hc le_rfl)

end SphericalAging.PurePHamiltonianTreeALGUpper
