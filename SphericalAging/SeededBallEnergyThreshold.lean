module

public import SphericalAging.ExternalFieldCostLimsup
public import SphericalAging.RandomVectorBounds
public import SphericalAging.HardSphereDynamics

public section

/-! The preceding published field threshold bounds the mean energy of
actual independently seeded, ball-valued Lipschitz algorithms. The field
direction is constructed, and its nonnegative penalty is removed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000
namespace SphericalAging.SeededBallEnergyThreshold
open MeasureTheory ProbabilityTheory Set Filter FiniteModel HardSphereDynamics
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar ExternalFieldProbabilityTransfer ExternalFieldUniformCost
open ExternalFieldSeededCost ExternalFieldCostLimsup ForkNormalizedEnergy
open scoped NNReal ENNReal Topology

@[expose] def canonicalDirection {N : ℕ} (hN : 0<N) : Vector N :=
  Real.sqrt N • basisVector ⟨0,hN⟩

theorem canonicalDirection_norm {N : ℕ} (hN : 0<N) :
    ‖canonicalDirection hN‖=Real.sqrt N := by
  simp only [canonicalDirection,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),basisVector,EuclideanSpace.norm_single,norm_one,mul_one]

theorem seeded_energy_eventually {p : ℕ} (hp : 3≤p) {Lip : ℝ≥0}
    (H : PublishedFieldThreshold p Lip) (dim : ℕ→ℕ) (hDim : ∀j,1≤dim j)
    (hTop : Tendsto dim atTop atTop)
    {Ξ : ℕ→Type} [∀j,MeasurableSpace (Ξ j)]
    (σ : ∀j,Measure (Ξ j)) [∀j,IsProbabilityMeasure (σ j)]
    (A : ∀j,Ξ j×Disorder (dim j) p→Vector (dim j))
    (hA : ∀j,Measurable (A j))
    (hgood : ∀j,∀ᵐξ ∂σ j,LipschitzWith Lip
      (fun J : EuclideanSpace ℝ (TensorIndex (dim j) p) => A j (ξ,J.ofLp)) ∧
        ∀J,‖A j (ξ,J)‖≤Real.sqrt (dim j)) :
    ∀ε>0,∀ᶠj in atTop,expectedEnergy (μ:=(σ j).prod (disorderLaw (dim j) p)) Prod.snd (A j)
      ≤thresholdEnergy p+ε := by
  let w := fun j (_ : Ξ j) => canonicalDirection (by have hd:=hDim j;omega : 0<dim j)
  have hw (j : ℕ) : Measurable (w j) := measurable_const
  have hg (j : ℕ) : ∀ᵐξ ∂σ j,LipschitzWith Lip
      (fun J : EuclideanSpace ℝ (TensorIndex (dim j) p) => A j (ξ,J.ofLp)) ∧
        (∀J,‖A j (ξ,J)‖≤Real.sqrt (dim j)) ∧ ‖w j ξ‖=Real.sqrt (dim j) := by
    filter_upwards [hgood j] with ξ hξ
    exact ⟨hξ.1,hξ.2,canonicalDirection_norm _⟩
  intro ε hε
  filter_upwards [seeded_cost_eventually hp H dim hDim hTop σ w A hw hA hg ε hε] with j hj
  have hs := seededCost_integral_split (hDim j) hp (σ j) (hw j) (hA j)
    ((hg j).mono (fun _ h => h.2))
  have hn : 0≤betaD p*(∫z,seededOverlapPower (p:=p) (w j) (A j) z
      ∂(σ j).prod (disorderLaw (dim j) p)) :=
    mul_nonneg (betaD_positive hp).le (integral_nonneg (fun _ => pow_nonneg (abs_nonneg _) _))
  rw [hs] at hj
  unfold expectedEnergy
  rw [integral_div] at hj
  linarith

end SphericalAging.SeededBallEnergyThreshold
