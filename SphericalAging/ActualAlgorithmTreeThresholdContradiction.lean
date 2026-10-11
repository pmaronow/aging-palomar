module

public import SphericalAging.BallFieldAlgorithmCalibratedTree
public import SphericalAging.ActualHighEnergyExactSubtree

public section

/-! A literal finite-tree contradiction bounds the actual original field
success probability by the three derived failure budgets. -/
noncomputable section
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAlgorithmTreeThresholdContradiction
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure GaussianLandscape
open ExternalFieldUniformCost BallFieldAlgorithmTreeSuccess BallFieldAlgorithmCalibratedTree
open ActualAlgorithmTreeGlobalEvent ActualAlgorithmTree ActualAlgorithmTreeEnergy
open ActualHighEnergyExactSubtree ActualTreeEnergyPerturbation ActualTreeLandscapeEvent
open IndependentBranchingSuccess IndependentBranchingSuccessEvent GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open GaussianTreeStaticPruneLaw RegularTreeHighEnergyPruning RegularTreeEnergyTelescoping
open TreeExactificationError FiniteTreeCommonOrthogonalDirection HamiltonianTreeEnergy HamiltonianTreeFieldBand
open scoped NNReal InnerProductSpace
variable {N p K k : ℕ} {L : ℝ≥0}

@[expose] def firstSelection (hkK : k≤K) : (D : ℕ)→Selection K k D
  | 0 => PUnit.unit
  | D+1 => (Fin.castLEEmb hkK,fun _ => firstSelection hkK D)

@[expose] def correctionCost (p k D K : ℕ) (κ δ ε : ℝ) : ℝ :=
  ((p:ℝ)*(landscapeThreshold p+4)+κ)*
    (2*Real.sqrt δ+correctionError k ((1-δ)*(ε+2/(K:ℝ))) D)

theorem actual_field_success_power_bound (hN2 : 2≤N) (hp : 0<p) (hK : 0<K) (hk : 0<k)
    (hkn : k<N) (D : ℕ) (hD : 0<D) (hDim : nodeCount k D<N) (σ : Selection K k D)
    (A : BallFieldAlgorithm N p L) (κ δ ε E U : ℝ) (hκ : 0≤κ) (hδ : δ∈Ioc (0:ℝ) 1)
    (hε : 0≤ε) (hsmall : SmallConditions k D δ ((1-δ)*(ε+2/(K:ℝ))))
    (hEU : U+correctionCost p k D K κ δ ε<E)
    (G : Set (TensorSpace N p×TreeSample (TensorSpace N p) k D)) (hG : MeasurableSet G)
    (hGp : 1-Real.exp (-(N:ℝ)/2)≤
      ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) k D)).real G)
    (hGb : ∀z∈G,∀c : TreeData (Vector N) k D,
      TreeForkGeometry (reversedSeparated δ (overlapMesh A D) D) D c→
        ‖root D c‖^2=(N:ℝ)*reversedSeparated δ (overlapMesh A D) D D→
          totalLeafEnergy (variance (by omega : 0<N) A D) D (κ • A.direction) c z≤U) :
    ((disorderLaw N p).real (success A κ E))^(K^D)≤
      unionBudget K D (2*Real.exp (-ε^2/(2*(AlgorithmicOverlapConcentration.overlapConstant N L:ℝ))))+
        ((K^D:ℕ):ℝ)*Real.exp (-(N:ℝ))+Real.exp (-(N:ℝ)/2) := by
  have hN : 0<N := by omega
  let V := variance hN A D
  let q := overlapMesh A D
  let μ := (stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)
  let S := event K (update (parentCoefficient V) (freshCoefficient V))
    (fieldSuccess (output A) (κ • A.direction) E) D
  obtain ⟨hq,hr,hmesh,hV0,hVD,hV,hVm,hOm,hOp,hOb⟩ :=
    actual_calibrated_global_tree (K:=K) hN A D hD ε hε
  have hsuccess := actual_original_disorder_tree_success (K:=K) hK V (fun j => (hV j).1) hVm hV0 A κ E D
  dsimp only at hsuccess
  let O := goodEvent (K:=K) (output A) V D ε
  obtain ⟨Z,hZm,hZp,hZb⟩ := actual_leaf_landscape_event (K:=K) hN2 hp V
    (fun j => (hV j).1) hVm hV0 D
  let G' := samplePrune D σ ⁻¹' G
  have hMP := samplePrune_measurePreserving (stdGaussian (TensorSpace N p))
    (stdGaussian (TensorSpace N p)) D σ
  have hG'm : MeasurableSet G' := hG.preimage hMP.measurable
  have hG'p : 1-Real.exp (-(N:ℝ)/2)≤μ.real G' := by
    rw [show μ.real G'=((stdGaussian (TensorSpace N p)).prod
      (treeLaw (stdGaussian (TensorSpace N p)) k D)).real G from hMP.hasLaw.measureReal_eq hG]
    exact hGp
  have hfield : ‖κ • A.direction‖≤Real.sqrt N*κ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hκ,A.norm_direction,mul_comm]
  have hcover : S⊆Oᶜ∪Zᶜ∪G'ᶜ := by
    intro z hz
    by_contra hbad
    have ho : z∈O := by
      by_contra hnot
      exact hbad (Or.inl (Or.inl hnot))
    have hzland : z∈Z := by
      by_contra hnot
      exact hbad (Or.inl (Or.inr hnot))
    have hg' : z∈G' := by
      by_contra hnot
      exact hbad (Or.inr hnot)
    obtain ⟨w,hw,hn,hwe⟩ := actual_high_energy_exact_subtree hN hK hk hkn D hDim σ q hq hr
      ε δ hε hδ hsmall V hV0 (output A) (κ • A.direction) (landscapeThreshold p+4) κ E hκ hfield z
      (hOb z ho) hz (hZb z hzland)
    have hupper := hGb (samplePrune D σ z) hg' w hw hn
    have hcost : E-correctionCost p k D K κ δ ε≤totalLeafEnergy V D (κ • A.direction) w (samplePrune D σ z) := hwe
    linarith
  have hoBad : μ.real Oᶜ≤unionBudget K D
      (2*Real.exp (-ε^2/(2*(AlgorithmicOverlapConcentration.overlapConstant N L:ℝ)))) := by
    rw [measureReal_compl hOm,probReal_univ]
    linarith
  have hzBad : μ.real Zᶜ≤((K^D:ℕ):ℝ)*Real.exp (-(N:ℝ)) := by
    rw [measureReal_compl hZm,probReal_univ]
    linarith
  have hgBad : μ.real G'ᶜ≤Real.exp (-(N:ℝ)/2) := by
    rw [measureReal_compl hG'm,probReal_univ]
    linarith
  calc
    _≤μ.real S := hsuccess.2.1
    _≤μ.real (Oᶜ∪Zᶜ∪G'ᶜ) := measureReal_mono hcover
    _≤μ.real Oᶜ+μ.real Zᶜ+μ.real G'ᶜ :=
      (measureReal_union_le _ _).trans (add_le_add_left (measureReal_union_le _ _) _)
    _≤_ := add_le_add (add_le_add hoBad hzBad) hgBad

end SphericalAging.ActualAlgorithmTreeThresholdContradiction
