module

public import SphericalAging.HamiltonianTreeFieldBand
public import SphericalAging.GaussianForkBranchingRate
public import SphericalAging.TreeFieldErrorThreshold

public section

/-! Huang--Sellke Proposition 3.3 for the actual ordered pure-p Gaussian
model. The branching and dimension thresholds, common event, probability
bound, energy ceiling and matching spatial configuration are all derived.
The finite ceiling is the literal expected fork-supremum sum; no ALG
variational identification or algorithmic threshold is asserted here. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PurePHamiltonianTreeProposition33
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping BranchingTreeLocalEvents
open HamiltonianTreeEnergy HamiltonianTreeLocalEvents HamiltonianTreeFieldBand
open FieldAlignedSphereBase GaussianForkBranchingRate TreeFieldErrorThreshold
open scoped BigOperators InnerProductSpace
variable {p : ℕ}

theorem actual_source_HS_3_3_pureP (hp : 1≤p) (D : ℕ) (δ ε H : ℝ)
    (hδ : 0<δ) (hε : 0<ε) (hH : 0≤H) :
    ∃K0 : ℕ,0<K0 ∧ ∀K≥K0,∃N0 : ℕ,∃hN0 : K<N0,∀(N : ℕ)(hNN : N0≤N),
      ∀V Q : ℕ→ℝ,(∀j,0≤V j ∧ V j≤1)→(∀j,V (j+1)≤V j)→
        (∀j,δ≤Q j ∧ Q j≤1)→(∀j,Q (j+1)≤Q j)→V D=0→
      ∀h : Vector N,‖h‖≤Real.sqrt N*H→
      ∃E : Set (TensorSpace N p×TreeSample (TensorSpace N p) K D),MeasurableSet E ∧
        1-Real.exp (-(N:ℝ)/2)≤
          ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)).real E ∧
        ∀z∈E,
          (∀c : TreeData (Vector N) K D,TreeForkGeometry Q D c→‖root D c‖^2=(N:ℝ)*Q D→
            totalLeafEnergy V D h c z≤center (N:=N) (p:=p) (K:=K)
              ((Nat.zero_le K).trans_lt (hN0.trans_le hNN)) V Q D h+2*(D:ℝ)*ε) ∧
          (∃c : TreeData (Vector N) K D,TreeForkGeometry Q D c ∧ ‖root D c‖^2=(N:ℝ)*Q D ∧
            center (N:=N) (p:=p) (K:=K)
              ((Nat.zero_le K).trans_lt (hN0.trans_le hNN)) V Q D h-2*(D:ℝ)*ε≤totalLeafEnergy V D h c z) := by
  obtain ⟨K1,hK1,hbranch⟩ := exists_branching_threshold hp δ ε hδ hε
  obtain ⟨K2,hK2,hfield⟩ := exists_field_branching_threshold D H ε hH hε
  refine ⟨max K1 K2,by omega,?_⟩
  intro K hK
  have hKpos : 0<K := by omega
  have hrate := hbranch K (by omega)
  have hfieldK := hfield K (by omega)
  obtain ⟨N1,hprob⟩ := actual_tree_failure_eventually_exp hp δ ε hδ hε hrate D
  refine ⟨max N1 (K+1),by omega,?_⟩
  intro N hN V Q hV hVm hQ hQm hroot h hnorm
  have hKN : K<N := by omega
  have hNpos : 0<N := by omega
  have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hNpos)
  have hsize : fieldSize N h≤H := by
    unfold fieldSize
    apply (div_le_iff₀ hs).2
    exact hnorm.trans_eq (mul_comm _ _)
  have herr : error N K D ε h≤2*(D:ℝ)*ε := by
    have hh := (mul_le_mul_of_nonneg_right hsize (Real.sqrt_nonneg ((D:ℝ)/(K:ℝ)))).trans hfieldK
    unfold error
    linarith
  obtain ⟨E,hEm,hEp,hE⟩ := actual_finite_tree_field_band hp hKpos hKN V Q hV hVm δ hδ hQ hQm ε hε D hroot h
  refine ⟨E,hEm,(sub_le_sub_left (hprob N (by omega)) 1).trans hEp,?_⟩
  intro z hz
  obtain ⟨hupper,hlower⟩ := hE z hz
  constructor
  · intro c hc hx
    exact (hupper c hc hx).trans (add_le_add le_rfl herr)
  · obtain ⟨c,hc,hx,hh⟩ := hlower
    exact ⟨c,hc,hx,(sub_le_sub_left herr _).trans hh⟩

end SphericalAging.PurePHamiltonianTreeProposition33
