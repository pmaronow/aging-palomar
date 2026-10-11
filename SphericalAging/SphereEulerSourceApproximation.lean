module

public import SphericalAging.SphereEulerSourceEstimate

public section

/-! The actual fixed-time Euler/query-span construction. The output and
every query are explicit functions of the prescribed seed and the finite
observed gradient sequence. The mean-square estimate is proved under the
literal Gaussian/surface/Wiener law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal
namespace SphericalAging.SphereEulerSourceApproximation
open FiniteModel HardSphereDynamics SphereEulerModelApproximation
open SphereEulerSourceEstimate SphereEulerMeshRate SphereEulerPredictable
open SphereEulerDimensionRate AdditiveSphereGaussianApproximation
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] abbrev Seed (N : ℕ) := State N×VectorBrownian.Space N

@[expose] def initialSpan (T : ℝ≥0) (M : ℕ) (z : Seed N) : Submodule ℝ (State N) :=
  Submodule.span ℝ (SphereEulerSeedSpan.seedGenerators z.1
    (fun j => increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j z.2) M : Set (State N))

theorem querySpan_zero_eq_seedSpan (β T : ℝ≥0) (M : ℕ) (q : Sample N p) :
    querySpan β T M 0 q=initialSpan T M (q.1.2,q.2) := by
  classical
  simp only [querySpan,SphereEulerSeedSpan.space,SphereEulerSeedSpan.generators,
    Finset.range_zero,Finset.image_empty,Finset.union_empty,initialSpan]

@[expose] def query (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) : State N :=
  SphereEulerQuerySpan.query β (mesh T M) q.1.1 q.1.2
    (fun j => increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j q.2) k

@[expose] def gradient (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) : State N :=
  hamiltonianGradient q.1.1 (query β T M k q)

theorem query_mem (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) (hk : k≤M) :
    query β T M k q∈querySpan β T M k q := SphereEulerSeedSpan.query_mem _ _ _ _ _ _ hk

theorem querySpan_succ_eq (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) :
    querySpan β T M (k+1) q=querySpan β T M k q⊔Submodule.span ℝ ({gradient β T M k q} : Set (State N)) :=
  SphereEulerSeedSpan.space_succ_eq _ _ _ _ _ _ _

theorem gradient_eq_disclosed (hp : 2≤p) (β T : ℝ≥0) (M k : ℕ) (q : Sample N p) (hk : k≤M) :
    gradient β T M k q=hamiltonianGradient
      (AdaptiveGradientDisclosure.disclosedDisorder (querySpan β T M k q) q.1.1) (query β T M k q) :=
  AdaptiveGradientDisclosure.gradient_eq_disclosed hp _ q.1.1 (query_mem β T M k q hk)

theorem seed_increment_measurable (T : ℝ≥0) (M j : ℕ) :
    Measurable (fun z : Seed N => increment (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j z.2) :=
  (((increment_stronglyMeasurable (NullAugmentation.driver (VectorBrownian.driver N)) (mesh T M) j).mono
    ((NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N)).le _)).measurable).comp measurable_snd

/-- A single constant works for every dimension and every fixed query count.
The actual adaptive residual-law identification is handled by the tensor
history construction; every analytic Euler estimate here is unconditional. -/
theorem actual_fixed_time_euler_query_span (p : ℕ) (hp : 2≤p) (β T : ℝ≥0) :
    ∃ C : ℝ≥0,∀ M : ℕ,1≤M →
      (∀ N,Measurable (output (N:=N) (p:=p) β T M)) ∧
      (∀ N (q : Sample N p),‖output β T M q‖≤Real.sqrt N) ∧
      (∀ N (q : Sample N p),Monotone (fun k => querySpan β T M k q)) ∧
      (∀ N (q : Sample N p),querySpan β T M 0 q=initialSpan T M (q.1.2,q.2)) ∧
      (∀ N (q : Sample N p),Module.finrank ℝ (querySpan β T M 0 q)≤M+1) ∧
      (∀ N (q : Sample N p) k,k≤M → query β T M k q∈querySpan β T M k q) ∧
      (∀ N (q : Sample N p) k,querySpan β T M (k+1) q=
        querySpan β T M k q⊔Submodule.span ℝ ({gradient β T M k q} : Set (State N))) ∧
      (∀ N (q : Sample N p),output β T M q∈querySpan β T M M q) ∧
      (∀ N (q : Sample N p),Module.finrank ℝ (querySpan β T M M q)≤2*M+1) ∧
      limsup (fun N : ℕ => normalizedError N p β T M) atTop≤(C:ℝ)*(T:ℝ)/(M:ℝ) := by
  refine ⟨globalRate p β (landscapeCutoff p) T,?_⟩
  intro M hM
  exact ⟨fun N => output_measurable β T M,fun N q => output_norm_le β T M q,
    fun N q => querySpan_mono β T M q,fun N q => querySpan_zero_eq_seedSpan β T M q,
    fun N q => initial_querySpan_finrank_le β T M q,
    fun N q k hk => query_mem β T M k q hk,fun N q k => querySpan_succ_eq β T M k q,
    fun N q => output_mem_querySpan β T M q,fun N q => terminal_querySpan_finrank_le β T M q,
    actual_dimension_limsup_le p hp β T (by omega)⟩

end SphericalAging.SphereEulerSourceApproximation
