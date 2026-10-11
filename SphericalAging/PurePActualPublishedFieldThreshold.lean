module

public import SphericalAging.ActualAlgorithmTreeThresholdContradiction
public import SphericalAging.PurePHamiltonianTreeALGCeiling
public import SphericalAging.TwoBranchingExactificationParameters
public import SphericalAging.ActualFieldThresholdParameterChoices
public import SphericalAging.AlgorithmTreeOverlapExponentialBudget
public import SphericalAging.TwoRateExponentialTail

public section

/-! The published general-p external-field algorithmic threshold is derived
from the literal original Gaussian model. All finite mesh, branching,
separation, correction and dimension parameters are chosen uniformly before
the algorithm; no preceding threshold or overlap conclusion is assumed. -/
noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PurePActualPublishedFieldThreshold
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure GaussianLandscape
open ExternalFieldUniformCost ExternalFieldElementaryPenalty BallFieldAlgorithmTreeSuccess
open BallFieldAlgorithmCalibratedTree ActualAlgorithmTreeThresholdContradiction
open ActualHighEnergyExactSubtree PurePHamiltonianTreeALGCeiling
open TwoBranchingExactificationParameters ActualFieldThresholdParameterChoices
open AlgorithmTreeOverlapExponentialBudget ProbabilityPowerExponentialTail ProbabilityPowerEventTail TwoRateExponentialTail
open FiniteTreeCommonOrthogonalDirection TreeExactificationError HamiltonianTreeFieldBand
open scoped NNReal InnerProductSpace
variable {p : ℕ}

@[expose] def promote {N : ℕ} {L : ℝ≥0} (A : BallFieldAlgorithm N p L) : BallFieldAlgorithm N p (L+1) where
  output := A.output
  measurable_output := A.measurable_output
  lipschitz_output := A.lipschitz_output.weaken (by exact le_add_of_nonneg_right (by positivity))
  ball_output := A.ball_output
  direction := A.direction
  norm_direction := A.norm_direction

/-- The full source 10.1 threshold, with uniform constants for every genuine
Euclidean Lipschitz ball algorithm and every actual external-field direction. -/
theorem actual_published_field_threshold (hp : 3≤p) (L : ℝ≥0) : PublishedFieldThreshold p L := by
  intro κ hκ η hη
  let LP : ℝ≥0 := L+1
  have hLP : 0<(LP:ℝ) := by dsimp [LP];positivity
  let B : ℝ := (p:ℝ)*(landscapeThreshold p+4)+κ
  have hB : 0≤B := by
    dsimp [B]
    have hC := landscapeThreshold_pos p
    positivity
  obtain ⟨δ,hδ,ζ,hζ,herror⟩ := exists_small_energy_parameters hB hη
  obtain ⟨meshδ,hmeshδ,hTree⟩ := actual_tree_field_alg_uniform hp hκ (by positivity : 0<η/2)
  obtain ⟨D,hD,hDmesh⟩ := exists_mesh_depth hmeshδ
  obtain ⟨k,hk,hkTree⟩ := hTree D δ hδ.1
  obtain ⟨NAlg,hNAlg,hAlg⟩ := hkTree k (le_refl k)
  obtain ⟨K,hkK,_hKmin,hε,heη,hsmall,hcorr⟩ := exists_exactification_parameters k D 0 hk hδ hζ
  have hK : 0<K := hk.trans_le hkK
  let ε := tolerance K
  have hsmall' : SmallConditions k D δ ((1-δ)*(ε+2/(K:ℝ))) := by
    rw [←heη]
    exact hsmall
  have hcorr' : correctionError k ((1-δ)*(ε+2/(K:ℝ))) D≤ζ := by
    rw [←heη]
    exact hcorr
  have hcost : correctionCost p k D K κ δ ε<η/2 := by
    unfold correctionCost
    exact (mul_le_mul_of_nonneg_left (add_le_add_right hcorr' (2*Real.sqrt δ)) hB).trans_lt herror
  let C1 := overlapPrefactor K D
  let C2 : ℝ := ((K^D:ℕ):ℝ)+1
  let c1 := overlapRate LP ε
  let c := min c1 (1/2)
  have hC1 : 0≤C1 := overlapPrefactor_nonneg K D
  have hC2 : 0≤C2 := by dsimp [C2];positivity
  have hC : 0<C1+C2 := by dsimp [C2];linarith [overlapPrefactor_nonneg K D,show (0:ℝ)≤((K^D:ℕ):ℝ) from Nat.cast_nonneg _]
  have hc1 : 0<c1 := overlapRate_pos hLP hε
  have hc : 0<c := lt_min hc1 (by norm_num)
  have hm : 0<K^D := pow_pos hK D
  let N0 := max NAlg (max (nodeCount k D+1) (max 2 (absorptionCutoff (C1+C2) c)))
  refine ⟨rate c (K^D),rate_pos hc hm,N0,?_⟩
  intro N hNN _hN1 A
  have hNNAlg : NAlg≤N := (le_max_left _ _).trans hNN
  have hN2 : 2≤N := by
    have hh := (le_max_right NAlg _).trans hNN
    have hh' := (le_max_right (nodeCount k D+1) _).trans hh
    exact (le_max_left _ _).trans hh'
  have hN : 0<N := by omega
  have hkn : k<N := hNAlg.trans_le hNNAlg
  have hDim : nodeCount k D<N := by
    have hh := (le_max_left (nodeCount k D+1) _).trans ((le_max_right NAlg _).trans hNN)
    omega
  have hcut : absorptionCutoff (C1+C2) c≤N :=
    (le_max_right _ _).trans ((le_max_right (nodeCount k D+1) _).trans ((le_max_right NAlg _).trans hNN))
  let A' : BallFieldAlgorithm N p LP := promote A
  let q := overlapMesh A' D
  let V := variance hN A' D
  let Q := reversedSeparated δ q D
  obtain ⟨hq,hr,hmesh,hV0,hVD,hV,hVm,_hOm,_hOp,_hOb⟩ :=
    actual_calibrated_global_tree (K:=K) hN A' D hD ε hε.le
  have hδc : δ∈Icc (0:ℝ) 1 := ⟨hδ.1.le,hδ.2.le⟩
  have hQ : ∀j,δ≤Q j ∧ Q j≤1 := reversedSeparated_mem δ hδc q hr D
  have hQm : ∀j,Q (j+1)≤Q j := reversedSeparated_descending δ hδ.2.le q hq D
  have hQmesh : ∀j<D,Q j-Q (j+1)≤ meshδ := by
    intro j hj
    exact (reversedSeparated_mesh δ hδc q hq D (1/(D:ℝ)) (by positivity) hmesh j hj).trans hDmesh
  have hfield : ‖κ • A'.direction‖≤Real.sqrt N*κ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκ,A'.norm_direction,mul_comm]
  obtain ⟨G,hG,hGp,hGb⟩ := hAlg N hNNAlg V Q hV hVm hQ hQm hVD hQmesh (κ • A'.direction) hfield
  have hEU : algorithmicField p κ+η/2+correctionCost p k D K κ δ ε<algorithmicField p κ+η := by
    linarith
  have hpow := actual_field_success_power_bound hN2 (by omega : 0<p) hK hk hkn D hD hDim
    (firstSelection hkK D) A' κ δ ε (algorithmicField p κ+η) (algorithmicField p κ+η/2)
    hκ ⟨hδ.1,hδ.2.le⟩ hε.le hsmall' hEU G hG hGp hGb
  rw [unionBudget_eq_exponential hN hLP K D ε] at hpow
  have hrest : ((K^D:ℕ):ℝ)*Real.exp (-(N:ℝ))+Real.exp (-(N:ℝ)/2)≤C2*Real.exp (-(1/2)*(N:ℝ)) := by
    have hw := exponential_tail_weaken (Nat.cast_nonneg (K^D)) (by norm_num : (1/2:ℝ)≤1) (Nat.cast_nonneg N)
    simp only [neg_one_mul] at hw
    calc
      _≤((K^D:ℕ):ℝ)*Real.exp (-(1/2)*(N:ℝ))+Real.exp (-(1/2)*(N:ℝ)) := by
        convert add_le_add_left hw (Real.exp (-(N:ℝ)/2)) using 1 <;> congr 2 <;> ring
      _=C2*Real.exp (-(1/2)*(N:ℝ)) := by dsimp [C2];ring
  have hpow2 : ((disorderLaw N p).real (success A' κ (algorithmicField p κ+η)))^(K^D)≤
      C1*Real.exp (-c1*(N:ℝ))+C2*Real.exp (-(1/2)*(N:ℝ)) := by
    calc
      _≤overlapPrefactor K D*Real.exp (-overlapRate LP ε*(N:ℝ))+
          (((K^D:ℕ):ℝ)*Real.exp (-(N:ℝ))+Real.exp (-(N:ℝ)/2)) := by
        simpa only [add_assoc] using hpow
      _≤_ := add_le_add_right hrest _
  have hh := exponential_bound_of_two_power_budgets hm hC1 hC2 hC hc1 (by norm_num : (0:ℝ)<1/2) hcut hpow2
  exact hh

end SphericalAging.PurePActualPublishedFieldThreshold
