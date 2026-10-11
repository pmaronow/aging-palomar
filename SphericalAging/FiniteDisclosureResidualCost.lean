module

public import SphericalAging.ResidualCostIntegrability
public import SphericalAging.ResidualOriginalEnergy
public import SphericalAging.FiniteDisclosureIntegrableAverage
public import SphericalAging.FiniteDisclosureSeedHistory

public section

/-! Actual conditional residual-model cost at every leaf of a finite
Gaussian disclosure tree. Fresh and dependent ranks are both included. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureResidualCost
open Set Filter MeasureTheory ProbabilityTheory FiniteModel GaussianLandscape AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureDisclosed FiniteDisclosureSeedHistory CanonicalVectorSpan TensorOrthogonalAction TensorResidualRotation
open ResidualTensorAlgorithm ResidualTensorEnergy ResidualGaussianMeanCost ResidualCostIntegrability ResidualOriginalEnergy
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

@[expose]  def value (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S→Frame N)→(S→TensorSpace N p)→
    (S→TensorSpace N p→Vector N)→(Past N p n r S→Vector N)→Leaves N p n r S→ℝ
  | 0,r,_,_,_,F,D,A,u,z =>
      Hamiltonian N p (action (F z.1) (D z.1+z.2.val)).ofLp
        (physicalProjection (space N r) (F z.1) (A z.1 (action (F z.1) (D z.1+z.2.val))))/(N:ℝ)+
      betaD p*|⟪u z.1,A z.1 (action (F z.1) (D z.1+z.2.val))⟫_ℝ/Real.sqrt (N:ℝ)|^p
  | n+1,r,S,_,P,F,D,A,u,z =>
      Sum.elim (value N p n (r+1) (S×Block N p r) P.2.1
        (freshFrame P.1.val F) (freshDisclosed P.1.val D) (fun s => A s.1) (u∘Sum.inl))
        (value N p n r S P.2.2 F D A (u∘Sum.inr)) z

 theorem average_bound {N p k : ℕ} {L : ℝ≥0} (hN : 0<N) (hk : k<N) (hp : 3≤p)
    {ε : ℝ} (hε : 0≤ε)
    (hb : ∀m,N-k≤m→1≤m→∀B : BallFieldAlgorithm m p L,meanCost B≤thresholdEnergy p+ε)
    (n r : ℕ) (S : Type) [MeasurableSpace S] (P : Plan N p n r S)
    (F : S→Frame N) (D : S→TensorSpace N p) (hD : ∀s,D s∈(Residual N p r)ᗮ)
    (A : S→TensorSpace N p→Vector N) (u : Past N p n r S→Vector N)
    (s : Past N p n r S)
    (hA : LipschitzWith L (A (seed N p n r S s)))
    (hball : ∀J,‖A (seed N p n r S s) J‖≤Real.sqrt N)
    (hRank : Module.finrank ℝ (physicalSpace N p n r S P F s)≤k)
    (hu : u s∈(physicalSpace N p n r S P F s)ᗮ)
    (hun : u s=0 ∨ ‖u s‖=1) :
    average N p n r S (value N p n r S P F D A u) s≤
      thresholdEnergy p+ε+betaD p*(k:ℝ)/(N:ℝ) := by
  induction n generalizing r S with
  | zero =>
    let W := space N r
    let m := Module.finrank ℝ Wᗮ
    let b := ResidualTensorModel.vectorBasis W
    have hdim := W.finrank_add_finrank_orthogonal
    have hr : Module.finrank ℝ W≤k := by
      simpa only [physicalSpace,rotatedSpace,LinearEquiv.finrank_map_eq] using hRank
    have hEq : Module.finrank ℝ W+m=N := by simpa only [m,finrank_euclideanSpace,Fintype.card_fin] using hdim
    have hm : 0<m := by omega
    have hmN : m≤N := by omega
    have hNk : N≤m+k := by omega
    have hmLower : N-k≤m := by omega
    let v : Wᗮ := ⟨(F s).symm (u s),orthogonal_inverse (F s) W hu⟩
    have hv : v=0 ∨ ‖v‖=1 := by
      rcases hun with hu0 | hu1
      · left
        apply Subtype.ext
        change (F s).symm (u s)=0
        rw [hu0,map_zero]
      · right;change ‖(F s).symm (u s)‖=1;rw [(F s).symm.norm_map,hu1]
    have hh := (zero_or_unit_mean_bound hN hm hmN hNk hp hε
      (hb m hmLower (by omega)) W b (F s) (action (F s) (D s)) (A s) hA hball v hv).2
    change (∫R : Residual N p r,value N p 0 r S P F D A u (s,R) ∂stdGaussian (Residual N p r))≤_
    convert hh using 1
    congr 1
    funext R
    simp only [value,residualValue,map_add,←map_add]
    rw [original_energy_eq_residual W (F s) (D s) (hD s) R]
    simp only [map_add]
    have hvF : F s v=u s := (F s).apply_symm_apply _
    rw [hvF]
  | succ n ih =>
    cases s with
    | inl s =>
      exact ih (r+1) (S×Block N p r) P.2.1
        (freshFrame P.1.val F) (freshDisclosed P.1.val D)
        (freshDisclosed_mem P.1.val D hD) (fun s => A s.1)
        (u∘Sum.inl) s hA hball hRank hu hun
    | inr s =>
      exact ih r S P.2.2 F D hD A (u∘Sum.inr) s hA hball hRank hu hun

end SphericalAging.FiniteDisclosureResidualCost
