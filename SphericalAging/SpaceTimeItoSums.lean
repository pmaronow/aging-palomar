module

public import SphericalAging.SpaceTimeTaylorPartition
public import SphericalAging.SpaceTimeDerivativeRiemann

public section

/-! Spatial partition limits for an actual time-dependent C² test function. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SpaceTimeItoSums
open HardSphereDynamics LocalSDE MultivariateTaylor
open VectorItoFormula WeightedVectorQuadratic LocalWeightedQuadratic SDEWeightedCovariation
open AnnealedSDECore
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*}

@[expose] def linearApprox (f : ℝ≥0 → State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range n,fderiv ℝ (f (uniformPartitionTime t n l)) (X (uniformPartitionTime t n l) ω)
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)

@[expose] def quadraticApprox (f : ℝ≥0 → State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ l ∈ Finset.range n,(1/2 : ℝ)*Hessian (f (uniformPartitionTime t n l)) (X (uniformPartitionTime t n l) ω)
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)
    (X (uniformPartitionTime t n (l+1)) ω-X (uniformPartitionTime t n l) ω)

/-- Exact partition telescoping separates the time and spatial increments. -/
lemma partition_identity (f : ℝ → State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (T : ℝ≥0) (n : ℕ) (hn : 0<n) (ω : Ω) :
    f T (X T ω)-f 0 (X 0 ω)=
      SpaceTimeDerivativeRiemann.timeApprox f (fun s => X (Real.toNNReal s) ω) T n+
      linearApprox (fun s => f s) X T n ω+
      quadraticApprox (fun s => f s) X T n ω+
      SpaceTimeTaylorPartition.remainderApprox (fun s => f s) X T n ω := by
  have hsum : ∑ l ∈ Finset.range n,(f (uniformPartitionTime T n (l+1))
      (X (uniformPartitionTime T n (l+1)) ω)-f (uniformPartitionTime T n l)
      (X (uniformPartitionTime T n l) ω))=f T (X T ω)-f 0 (X 0 ω) := by
    rw [Finset.sum_range_sub (fun l => f (uniformPartitionTime T n l) (X (uniformPartitionTime T n l) ω)) n]
    have hn0 : (n : ℝ≥0)≠0 := by exact_mod_cast Nat.ne_of_gt hn
    simp [uniformPartitionTime,hn0]
  rw [← hsum]
  unfold SpaceTimeDerivativeRiemann.timeApprox linearApprox quadraticApprox
    SpaceTimeTaylorPartition.remainderApprox remainder
  simp only [Real.toNNReal_coe]
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun l _ => by ring)

lemma quadraticApprox_coordinates (f : ℝ≥0 → State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (t : ℝ≥0) (n : ℕ) (ω : Ω) : quadraticApprox f X t n ω=(1/2 : ℝ)*
      ∑ i : Fin N,∑ k : Fin N,weightedCovariationSum
        (fun s ω => Hessian (f s) (X s ω) (basisVector i) (basisVector k))
        (fun s ω => X s ω i) (fun s ω => X s ω k) t n ω := by
  let q (i k : Fin N) (l : ℕ) : ℝ := (1/2 : ℝ)*
    Hessian (f (uniformPartitionTime t n l)) (X (uniformPartitionTime t n l) ω) (basisVector i) (basisVector k)*
    (X (uniformPartitionTime t n (l+1)) ω i-X (uniformPartitionTime t n l) ω i)*
    (X (uniformPartitionTime t n (l+1)) ω k-X (uniformPartitionTime t n l) ω k)
  calc
    _ = ∑ l ∈ Finset.range n,∑ i : Fin N,∑ k : Fin N,q i k l := by
      unfold quadraticApprox
      apply Finset.sum_congr rfl
      intro l _
      rw [SphereGenerator.bilinear_coordinates]
      simp only [Finset.mul_sum,PiLp.sub_apply]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      dsimp only [q]
      ring
    _ = ∑ i : Fin N,∑ k : Fin N,∑ l ∈ Finset.range n,q i k l := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := by
      unfold weightedCovariationSum
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [q]
      ring

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The second-order partition sums converge to the genuine physical
matrix covariance contracted with the Hessian of the C² observable. -/
theorem strong_quadratic_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D b sigma Z0 X T)
    (hsigma : ∀ ω i j,Continuous (sigma ω i j)) (t : ℝ≥0) (ht : t≤T)
    {f : ℝ≥0 → State N → ℝ}
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s)))) :
    TendstoInMeasure P (fun n => quadraticApprox f X t (n+1)) atTop
      (fun ω => (1/2 : ℝ)*∑ i : Fin N,∑ k : Fin N,∫ s in Ioc (0 : ℝ≥0) t,
        Hessian (f s) (X s ω) (basisVector i) (basisVector k)*
          (∑ j : Fin N,sigma ω i j (X s ω)*sigma ω k j (X s ω)) ∂nonnegativeLebesgueMeasure) := by
  have hhc (i k : Fin N) : Continuous (fun q : ℝ≥0 × State N =>
      Hessian (f q.1) q.2 (basisVector i) (basisVector k)) :=
    (hH.clm_apply continuous_const).clm_apply continuous_const
  have h (i k : Fin N) := strong_coordinate_weightedCovariation_tendsto D T hX hsigma t ht i k
    (fun s ω => Hessian (f s) (X s ω) (basisVector i) (basisVector k))
    (fun s => (hhc i k).comp_aestronglyMeasurable
      (aestronglyMeasurable_const.prodMk (((hX.2.1 s).mono (F.le s)).aestronglyMeasurable)))
    (hX.2.2.1.mono (fun _ h => (hhc i k).comp (continuous_id.prodMk h)))
  have hsum := tendstoInMeasure_finsetSum Finset.univ _ _ (fun i _ =>
    tendstoInMeasure_finsetSum Finset.univ _ _ (fun k _ => h i k))
  apply (hsum.const_mul_real_noMeas (1/2 : ℝ)).congr_left
  intro n
  exact .of_forall (fun ω => (quadraticApprox_coordinates f X t (n+1) ω).symm)

end SphericalAging.SpaceTimeItoSums
