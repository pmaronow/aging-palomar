module

public import SphericalAging.FiniteDisclosureCostLimit
public import SphericalAging.AdaptiveDisclosureDimension
public import SphericalAging.FiniteDisclosureQueryFactorization
public import SphericalAging.FiniteDisclosureSpaceMeasurable

public section

/-! Source10.7 Step4 for the literal recursively disclosed sigma algebras.
The finite program and its query factorization are constructed from the
original independent Gaussian tensor; no conditional cost bound is assumed. -/
noncomputable section
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.AdaptiveResidualSourceCost
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open AdaptiveTensorDisclosureSource AdaptiveDisclosureDimension
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosureAmbient FiniteDisclosureExactHistory
open FiniteDisclosureQueryFactorization FiniteDisclosureSpaceMeasurable
open ExternalFieldUniformCost ExternalFieldElementaryPenalty ExternalFieldSharpScalar
open scoped Topology InnerProductSpace NNReal

@[expose] def cost {N p : ℕ} {S : Type} (W0 : S→Submodule ℝ (Vector N))
    (u : ℕ→S×TensorSpace N p→Vector N) (j : ℕ)
    (A : S→TensorSpace N p→Vector N) (z : S×TensorSpace N p) : ℝ :=
  Hamiltonian N p z.2.ofLp ((Space W0 u j z)ᗮ.starProjection (A z.1 z.2))/(N:ℝ)+
    betaD p*|⟪u j z,A z.1 z.2⟫_ℝ/Real.sqrt (N:ℝ)|^p

theorem query_measurable {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ) :
    Measurable (u j) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix S W0 hW0 u hu j
  have hh : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] (u j) := by
    rw [hHistory]
    exact hu j
  obtain ⟨q,hq,he⟩ := exists_past_vector_query P (u j) hh
  rw [he]
  exact hq.comp (actualHistory_measurable P)

theorem projection_measurable {N p : ℕ} (S : Type) [MeasurableSpace S]
    (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ)
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A)) :
    Measurable (fun z : S×TensorSpace N p => (Space W0 u j z).starProjection (A z.1 z.2)) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix S W0 hW0 u hu j
  have ha : Measurable (fun z : S×TensorSpace N p => (actualHistory P z,A z.1 z.2)) :=
    (actualHistory_measurable P).prodMk hA
  have hc := (physicalSpace_projection_measurable N p (N+j) 0 S P (initialFrame N S) measurable_snd).comp ha
  change Measurable (fun z : S×TensorSpace N p => (actualSpace P z).starProjection (A z.1 z.2)) at hc
  simpa only [hSpace] using hc

theorem cost_integrable {N p : ℕ} (S : Type) [MeasurableSpace S]
    (hN : 0<N) (hp : 3≤p) (W0 : S→Submodule ℝ (Vector N))
    (hW0 : Measurable (fun z : S×Vector N => (W0 z.1).starProjection z.2))
    (u : ℕ→S×TensorSpace N p→Vector N)
    (hu : ∀j,Measurable[MeasurableSpace.comap (History W0 u j) inferInstance] (u j)) (j : ℕ)
    (μ : Measure S) [IsProbabilityMeasure μ]
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (hball : ∀ᵐs ∂μ,∀J,‖A s J‖≤Real.sqrt N)
    (hun : ∀z,u j z=0 ∨ ‖u j z‖=1) :
    Integrable (cost W0 u j A) (μ.prod (stdGaussian (TensorSpace N p))) := by
  obtain ⟨P,hSpace,hHistory⟩ := exists_actual_prefix S W0 hW0 u hu j
  have hh : Measurable[MeasurableSpace.comap (literalHistory P) inferInstance] (u j) := by
    rw [hHistory]
    exact hu j
  obtain ⟨q,hq,he⟩ := exists_past_vector_query P (u j) hh
  have hqe z : q (actualHistory P z)=u j z := by rw [he];rfl
  have hc : FiniteDisclosureAmbientCost.cost P A q=cost W0 u j A := by
    funext z
    simp only [FiniteDisclosureAmbientCost.cost,cost,hSpace,hqe]
  rw [←hc]
  exact FiniteDisclosureAmbientCost.cost_integrable hN hp P μ A hA hball q hq
    (fun z => by rw [hqe];exact hun z)

theorem actual_source_cost_eventually {p k0 : ℕ} (hp : 3≤p) {L : ℝ≥0}
    (H : PublishedFieldThreshold p L) (dim : ℕ→ℕ)
    (hDim : ∀n,0<dim n) (hTop : Tendsto dim atTop atTop)
    {S : ℕ→Type} [∀n,MeasurableSpace (S n)]
    (μ : ∀n,Measure (S n)) [∀n,IsProbabilityMeasure (μ n)]
    (W0 : ∀n,S n→Submodule ℝ (Vector (dim n)))
    (hW0 : ∀n,Measurable (fun z : S n×Vector (dim n) => (W0 n z.1).starProjection z.2))
    (hRank0 : ∀n s,Module.finrank ℝ (W0 n s)≤k0)
    (u : ∀n,ℕ→S n×TensorSpace (dim n) p→Vector (dim n))
    (hu : ∀n j,Measurable[MeasurableSpace.comap (History (W0 n) (u n) j) inferInstance] (u n j))
    (A : ∀n,S n→TensorSpace (dim n) p→Vector (dim n))
    (hA : ∀n,Measurable (Function.uncurry (A n)))
    (hgood : ∀n,∀ᵐs ∂μ n,LipschitzWith L (A n s) ∧ ∀J,‖A n s J‖≤Real.sqrt (dim n))
    (j : ℕ) (horth : ∀n z,u n j z∈(Space (W0 n) (u n) j z)ᗮ)
    (hun : ∀n z,u n j z=0 ∨ ‖u n j z‖=1) :
    ∀ε>0,∀ᶠn in atTop,
      (∫z,cost (W0 n) (u n) j (A n) z ∂(μ n).prod (stdGaussian (TensorSpace (dim n) p)))≤thresholdEnergy p+ε := by
  classical
  let P n := Classical.choose (exists_actual_prefix (S n) (W0 n) (hW0 n) (u n) (hu n) j)
  have hSpace n : ∀z,actualSpace (P n) z=Space (W0 n) (u n) j z :=
    (Classical.choose_spec (exists_actual_prefix (S n) (W0 n) (hW0 n) (u n) (hu n) j)).1
  have hHistory n := (Classical.choose_spec (exists_actual_prefix (S n) (W0 n) (hW0 n) (u n) (hu n) j)).2
  have hh n : Measurable[MeasurableSpace.comap (literalHistory (P n)) inferInstance] (u n j) := by
    rw [hHistory n]
    exact hu n j
  let q n := Classical.choose (exists_past_vector_query (P n) (u n j) (hh n))
  have hqm n : Measurable (q n) :=
    (Classical.choose_spec (exists_past_vector_query (P n) (u n j) (hh n))).1
  have hqe n z : q n (actualHistory (P n) z)=u n j z := by
    have he := (Classical.choose_spec (exists_past_vector_query (P n) (u n j) (hh n))).2
    rw [he];rfl
  have hc n : FiniteDisclosureAmbientCost.cost (P n) (A n) (q n)=cost (W0 n) (u n) j (A n) := by
    funext z
    simp only [FiniteDisclosureAmbientCost.cost,cost,hSpace n,hqe n]
  have hcost := FiniteDisclosureCostLimit.actual_cost_eventually (k:=k0+j) hp H dim
    (fun n => dim n+j) hDim hTop μ P A hA hgood q hqm
    (fun n z => by rw [hSpace n];exact source_rank_le (W0 n) (u n) (hRank0 n) j z)
    (fun n z => by rw [hSpace n,hqe n];exact horth n z)
    (fun n z => by rw [hqe n];exact hun n z)
  simpa only [hc] using hcost

end SphericalAging.AdaptiveResidualSourceCost
