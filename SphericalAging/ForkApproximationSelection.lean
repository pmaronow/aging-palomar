module

public import SphericalAging.PhysicalForkStanding
public import SphericalAging.FiniteForkProjectionLimits

public section

/-! Genuine selection of the preceding finite-fork coefficient-Lipschitz
algorithms, with actual ball support and L² distance derived on the full
independent seed/disorder law. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ForkApproximationSelection
open MeasureTheory ProbabilityTheory Filter FiniteModel CKSpecification
  WienerForkTransfer ForkSeedCoordinates FiniteForkMoments PhysicalForkWaitingTransfer
  ForkNormalizedEnergy RandomGaussianPairing RandomVectorBounds ForkParameterBounds ForkEnergyComparison
open scoped NNReal Topology

structure Algorithm (dim : ℕ→ℕ) (p K : ℕ) (Q ε : ℝ)
    (Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)) where
  Lip : ℝ≥0
  output : ∀n,Seed (dim n) K×Disorder (dim n) p→Vector (dim n)
  measurable : ∀n,Measurable (output n)
  good : ∀n,∀ᵐξ ∂ForkSeedCoordinates.law (dim n) K,
    LipschitzWith Lip (fun J : EuclideanSpace ℝ (TensorIndex (dim n) p) => output n (ξ,J.ofLp)) ∧
      ∀J,‖output n (ξ,J)‖≤Real.sqrt (dim n)
  error : limsup (fun n => (∫z,‖output n z-projected Q (seededMean (Y n)) z‖^2
    ∂measure (dim n) p K)/(dim n:ℝ)) atTop≤ε^2

theorem exists_algorithm {dim : ℕ→ℕ} {p K : ℕ} {β e : ℝ} {c r : ℝ→ℝ}
    (F : FiniteForkStanding.Forks dim p β e c r) (hK : 1≤K)
    (L T : ℝ≥0) (hT : 0<T) (ε : ℝ) (hε : 0<ε) :
    ∃A : Algorithm dim p K (forkNorm c K L) ε (F.branches K L T),True := by
  obtain ⟨Lip,A,hA,hgood,herror⟩ := F.approximation K hK L T hT ε hε
  exact ⟨⟨Lip,A,hA,hgood,herror⟩,trivial⟩

@[expose] def choose {dim : ℕ→ℕ} {p K : ℕ} {β e : ℝ} {c r : ℝ→ℝ}
    (F : FiniteForkStanding.Forks dim p β e c r) (hK : 1≤K)
    (L T : ℝ≥0) (hT : 0<T) (ε : ℝ) (hε : 0<ε) :
    Algorithm dim p K (forkNorm c K L) ε (F.branches K L T) :=
  Classical.choose (exists_algorithm F hK L T hT ε hε)

theorem output_ball {dim : ℕ→ℕ} {p K : ℕ} {Q ε : ℝ}
    {Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)}
    (A : Algorithm dim p K Q ε Y) (n : ℕ) :
    ∀ᵐz ∂measure (dim n) p K,‖A.output n z‖≤Real.sqrt (dim n) := by
  filter_upwards [(measurePreserving_fst (μ:=ForkSeedCoordinates.law (dim n) K)
    (ν:=disorderLaw (dim n) p)).quasiMeasurePreserving.ae (A.good n)] with z hz
  exact hz.2 z.2

theorem output_memLp {dim : ℕ→ℕ} {p K : ℕ} {Q ε : ℝ}
    {Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)}
    (A : Algorithm dim p K Q ε Y) (n : ℕ) : MemLp (A.output n) 2 (measure (dim n) p K) :=
  MemLp.of_bound (A.measurable n).aestronglyMeasurable _ (output_ball A n)

theorem distance_limsup_le {dim : ℕ→ℕ} (hDim : ∀n,0<dim n) {p K : ℕ}
    {Q ε β : ℝ} {t T : ℝ≥0}
    {Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)}
    (hY : ∀n,ForkJointLaw β t T (Y n)) (hε : 0≤ε)
    (A : Algorithm dim p K Q ε Y) :
    limsup (fun n => distanceRoot (measure (dim n) p K) (dim n)
      (A.output n) (projected Q (seededMean (Y n)))) atTop≤ε := by
  apply FiniteForkProjectionLimits.distance_limsup_of_second_moment (C:=2) hDim
    (fun n => measure (dim n) p K) (fun n => output_memLp A n)
    (fun n => projected_memLp (Q:=Q) (hDim n) (seededMean_memLp (hY n))) hε _ A.error
  intro n
  simpa only [one_mul,one_add_one_eq_two] using distanceRoot_le (hDim n) (output_memLp A n)
    (projected_memLp (Q:=Q) (hDim n) (seededMean_memLp (hY n)))
    (C:=1) (D:=1) (by norm_num) (by norm_num)
    (by simpa only [one_mul] using output_ball A n)
    (by simpa only [one_mul] using projected_bound Q (seededMean (Y n)))

end SphericalAging.ForkApproximationSelection
