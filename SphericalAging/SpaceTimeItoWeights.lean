module

public import SphericalAging.SpaceTimeItoSums
public import SphericalAging.MultivariateItoWeights

public section

/-! Bounded predictable derivative weights with a genuine physical time parameter. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.SpaceTimeItoWeights
open HardSphereDynamics LocalSDE MultivariateTaylor SpaceTimeItoSums
open WeightedItoSums
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ}

@[expose] def derivativeWeight (f : ℝ≥0 → State N → ℝ) (T : ℝ≥0)
    (R : ℝ) (hR : 0<R) (i : Fin N) (s : ℝ≥0) (x : State N) : ℝ :=
  coefficientBump (N := N) R hR x*fderiv ℝ (f (min s T)) x (basisVector i)

lemma derivativeWeight_continuous {f : ℝ≥0 → State N → ℝ}
    (hD : Continuous (Function.uncurry (fun s => fderiv ℝ (f s))))
    (T : ℝ≥0) (R : ℝ) (hR : 0<R) (i : Fin N) :
    Continuous (Function.uncurry (derivativeWeight f T R hR i)) := by
  exact ((coefficientBump (N := N) R hR).continuous.comp continuous_snd).mul
    ((hD.clm_apply continuous_const).comp ((continuous_fst.min continuous_const).prodMk continuous_snd))

lemma derivativeWeight_bounded {f : ℝ≥0 → State N → ℝ}
    (hD : Continuous (Function.uncurry (fun s => fderiv ℝ (f s))))
    (T : ℝ≥0) (R : ℝ) (hR : 0<R) (i : Fin N) :
    ∃ K : ℝ≥0,∀ s x,‖derivativeWeight f T R hR i s x‖≤K := by
  have hc : Continuous (fun q : ℝ≥0 × State N => fderiv ℝ (f q.1) q.2 (basisVector i)) :=
    hD.clm_apply continuous_const
  obtain ⟨K,hK⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).prod
    (isCompact_closedBall (0 : State N) (2*R))).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨Real.toNNReal (max K 0),?_⟩
  intro s x
  by_cases hx : ‖x‖≤2*R
  · have hb : ‖coefficientBump (N := N) R hR x‖≤1 := by
      rw [Real.norm_of_nonneg (ContDiffBump.nonneg _)]
      exact ContDiffBump.le_one _
    have hd : ‖fderiv ℝ (f (min s T)) x (basisVector i)‖≤K :=
      hK (min s T,x) ⟨⟨bot_le,min_le_right _ _⟩,by simpa only [Metric.mem_closedBall,dist_zero_right] using hx⟩
    exact (norm_mul_le _ _).trans ((mul_le_of_le_one_left (norm_nonneg _) hb).trans
      (hd.trans ((le_max_left K 0).trans (Real.le_coe_toNNReal _))))
  · have hb : coefficientBump (N := N) R hR x=0 :=
      (coefficientBump (N := N) R hR).zero_of_le_dist (by
        simpa only [coefficientBump,dist_zero_right] using (not_le.mp hx).le)
    simp only [derivativeWeight,hb,zero_mul,norm_zero]
    exact NNReal.coe_nonneg _

lemma derivativeWeight_eq (f : ℝ≥0 → State N → ℝ) (T : ℝ≥0) (R : ℝ) (hR : 0<R)
    (i : Fin N) (s : ℝ≥0) (hs : s≤T) (x : State N) (hx : ‖x‖≤R) :
    derivativeWeight f T R hR i s x=fderiv ℝ (f s) x (basisVector i) := by
  simp only [derivativeWeight,min_eq_left hs]
  exact MultivariateItoWeights.derivativeWeight_eq (f s) R hR i x hx

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

lemma weight_stronglyAdapted {f : ℝ≥0 → State N → ℝ}
    (hD : Continuous (Function.uncurry (fun s => fderiv ℝ (f s))))
    (T : ℝ≥0) (R : ℝ) (hR : 0<R) (i : Fin N) {X : ℝ≥0 → Ω → State N}
    (hXa : StronglyAdapted F X) :
    StronglyAdapted F (fun s ω => derivativeWeight f T R hR i s (X s ω)) := by
  intro s
  exact (derivativeWeight_continuous hD T R hR i).comp_stronglyMeasurable
    (stronglyMeasurable_const.prodMk (hXa s))

lemma weight_continuous {f : ℝ≥0 → State N → ℝ}
    (hD : Continuous (Function.uncurry (fun s => fderiv ℝ (f s))))
    (T : ℝ≥0) (R : ℝ) (hR : 0<R) (i : Fin N) {X : ℝ≥0 → Ω → State N}
    (hXc : ∀ᵐ ω ∂P,Continuous (fun s => X s ω)) :
    ∀ᵐ ω ∂P,Continuous (fun s => derivativeWeight f T R hR i s (X s ω)) :=
  hXc.mono (fun _ hc => (derivativeWeight_continuous hD T R hR i).comp (continuous_id.prodMk hc))

lemma linearApprox_eq_weightedLeftSum (f : ℝ≥0 → State N → ℝ) (R : ℝ) (hR : 0<R)
    (X : ℝ≥0 → Ω → State N) (hXb : ∀ᵐ ω ∂P,∀ s,‖X s ω‖≤R)
    (T : ℝ≥0) (n : ℕ) (hn : 0<n) :
    linearApprox f X T n =ᵐ[P] fun ω => ∑ i : Fin N,weightedLeftSum
      (fun s ω => derivativeWeight f T R hR i s (X s ω)) (fun s ω => X s ω i) T n ω := by
  filter_upwards [hXb] with ω hω
  unfold linearApprox weightedLeftSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  rw [← state_sum_basis (X (uniformPartitionTime T n (l+1)) ω-X (uniformPartitionTime T n l) ω)]
  simp only [map_sum,map_smul,smul_eq_mul,PiLp.sub_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [derivativeWeight_eq f T R hR i _
    (uniformPartitionTime_mem_Icc_of_le T hn (Nat.le_of_lt (Finset.mem_range.mp hl))).2 _ (hω _)]
  ring

end SphericalAging.SpaceTimeItoWeights
