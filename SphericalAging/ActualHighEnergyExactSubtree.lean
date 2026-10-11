module

public import SphericalAging.ActualAlgorithmTreePrunedSuccess

public section

/-! The actual algorithm success, global overlap and landscape events produce
a genuine exact small-branching fork tree under the static selected original
Gaussian noises, with the explicitly derived energy perturbation cost. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualHighEnergyExactSubtree
open Set FiniteModel AdaptiveGradientDisclosure GaussianLandscape
open ActualAlgorithmTree ActualAlgorithmTreeEnergy ActualTreeEnergyPerturbation
open ActualAlgorithmTreePrunedSuccess GaussianTreeStaticPruneLaw GlobalAlgorithmTreeExactification
open RegularTreeHighEnergyPruning RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open RegularTreeCentroidGeometry FiniteTreeSeparation TreeExactificationError
open FiniteTreeCommonOrthogonalDirection HamiltonianTreeEnergy HamiltonianTreeFieldBand
open IndependentBranchingSuccess IndependentBranchingSuccessEvent GaussianBranchingSuccess PartialVarianceBranchingCoefficients
variable {N p K k : ℕ}

@[expose] def reversedSeparated (δ : ℝ) (q : ℕ→ℝ) (D j : ℕ) : ℝ := separatedOverlap δ (q (D-j))

theorem reversedSeparated_mem (δ : ℝ) (hδ : δ∈Icc (0:ℝ) 1) (q : ℕ→ℝ)
    (hq : ∀l,q l∈Icc (0:ℝ) 1) (D j : ℕ) :
    δ≤reversedSeparated δ q D j ∧ reversedSeparated δ q D j≤1 := by
  have hn := mul_nonneg (sub_nonneg.mpr hδ.2) (hq (D-j)).1
  have hh := mul_le_mul_of_nonneg_left (hq (D-j)).2 (sub_nonneg.mpr hδ.2)
  unfold reversedSeparated separatedOverlap
  constructor <;> linarith

theorem reversedSeparated_descending (δ : ℝ) (hδ : δ≤1) (q : ℕ→ℝ) (hq : Monotone q)
    (D : ℕ) : ∀j,reversedSeparated δ q D (j+1)≤reversedSeparated δ q D j := by
  intro j
  exact add_le_add_left (mul_le_mul_of_nonneg_left
    (hq (Nat.sub_le_sub_left (Nat.le_succ j) D)) (sub_nonneg.mpr hδ)) δ

theorem reversedSeparated_mesh (δ : ℝ) (hδ : δ∈Icc (0:ℝ) 1)
    (q : ℕ→ℝ) (hq : Monotone q) (D : ℕ) (s : ℝ) (hs : 0≤s)
    (hmesh : ∀l,q (l+1)-q l≤s) :
    ∀j<D,reversedSeparated δ q D j-reversedSeparated δ q D (j+1)≤s := by
  intro j hj
  have he : D-(j+1)+1=D-j := by omega
  have hgap := hmesh (D-(j+1))
  rw [he] at hgap
  have hnon : 0≤q (D-j)-q (D-(j+1)) := sub_nonneg.mpr (hq (by omega))
  have hmul : (1-δ)*(q (D-j)-q (D-(j+1)))≤s :=
    (mul_le_mul_of_nonneg_left hgap (sub_nonneg.mpr hδ.2)).trans
      (mul_le_of_le_one_left hs (by linarith [hδ.1] : 1-δ≤1))
  convert hmul using 1
  unfold reversedSeparated separatedOverlap
  ring

theorem actual_high_energy_exact_subtree (hN : 0<N) (hK : 0<K) (hk : 0<k) (hkn : k<N)
    (D : ℕ) (hDim : nodeCount k D<N) (σ : Selection K k D)
    (q : ℕ→ℝ) (hq : Monotone q) (hr : ∀l,q l∈Icc (0:ℝ) 1)
    (ε δ : ℝ) (hε : 0≤ε) (hδ : δ∈Ioc (0:ℝ) 1)
    (hsmall : SmallConditions k D δ ((1-δ)*(ε+2/(K:ℝ))))
    (V : ℕ→ℝ) (hV0 : V 0=1) (A : TensorSpace N p→Vector N)
    (h : Vector N) (C H E : ℝ) (hH : 0≤H) (hh : ‖h‖≤Real.sqrt N*H)
    (z : TensorSpace N p×TreeSample (TensorSpace N p) K D)
    (hglobal : GlobalOverlapTree q ε D
      (outputTree A (update (parentCoefficient V) (freshCoefficient V)) D z.1 z.2))
    (hsuccess : z∈event K (update (parentCoefficient V) (freshCoefficient V)) (fieldSuccess A h E) D)
    (hland : LeafLandscapeBound V C D z.1 z.2) :
    ∃w : TreeData (Vector N) k D,
      TreeForkGeometry (reversedSeparated δ q D) D w ∧
      ‖root D w‖^2=(N:ℝ)*reversedSeparated δ q D D ∧
      E-((p:ℝ)*C+H)*(2*Real.sqrt δ+correctionError k ((1-δ)*(ε+2/(K:ℝ))) D)≤
        totalLeafEnergy V D h w (samplePrune D σ z) := by
  let c := outputTree A (update (parentCoefficient V) (freshCoefficient V)) D z.1 z.2
  obtain ⟨w,hw,hn,hball,hd⟩ := actual_global_to_exact_fixed_subtree hN hK hkn D hDim σ
    q hq hr ε δ hε hδ hsmall c hglobal
  have hrev : ∀l,l≤D→separatedOverlap δ (q l)=reversedSeparated δ q D (D-l) := by
    intro l hl
    rw [reversedSeparated,Nat.sub_sub_self hl]
  have hgeom := forkTree_of_reverse (fun l => separatedOverlap δ (q l)) (reversedSeparated δ q D) D w hrev hw
  have hcball := allLeaves_prune (fun x => ‖x‖≤Real.sqrt N) D σ c (global_allLeaves_ball q ε D c hglobal)
  have hdist := leafDistance_of_addresses _ D (prune D σ c) w (fun a => by
    rw [norm_sub_rev]
    exact hd a)
  have hcost := actual_total_energy_perturbation hN hk V h C H _ hH hh D (prune D σ c) w
    hcball hball hdist z.1 (pruneSample D σ z.2) (actual_pruned_landscape V C D σ z.1 z.2 hland)
  have henergy := actual_pruned_success_energy hk V hV0 A h E D σ z.1 z.2 hsuccess
  refine ⟨w,hgeom,?_,?_⟩
  · simpa only [reversedSeparated,Nat.sub_self] using hn
  · change E-((p:ℝ)*C+H)*(2*Real.sqrt δ+correctionError k ((1-δ)*(ε+2/(K:ℝ))) D)≤_
    change E≤totalLeafEnergy V D h (prune D σ c) (samplePrune D σ z) at henergy
    change totalLeafEnergy V D h (prune D σ c) (samplePrune D σ z)≤
      totalLeafEnergy V D h w (samplePrune D σ z)+_ at hcost
    linarith

end SphericalAging.ActualHighEnergyExactSubtree
