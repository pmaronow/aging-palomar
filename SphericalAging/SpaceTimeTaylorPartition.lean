module

public import SphericalAging.MultivariateItoSums

public section

/-! Genuine C² spatial Taylor control with a varying physical time
parameter. Uniformity follows from the actual continuous spatial Hessian on
compact time/state sets; no mixed or second time derivative is required. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.SpaceTimeTaylorPartition
open HardSphereDynamics LocalSDE MultivariateTaylor MultivariateTaylorPartition
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*}

/-- Actual compact time/state continuity of the spatial Hessian makes the
spatial Taylor remainder uniform in physical time. -/
theorem uniform_remainder_time_closedBall
    (f : ℝ≥0 → State N → ℝ) (hf : ∀ s,ContDiff ℝ 2 (f s))
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s)))) (T : ℝ≥0) (R : ℝ) :
    ∀ ε : ℝ,0<ε → ∃ δ : ℝ,0<δ ∧
      ∀ s∈Icc 0 T,∀ x∈Metric.closedBall (0 : State N) R,
        ∀ y∈Metric.closedBall (0 : State N) R,
        ‖y-x‖<δ → ‖remainder (f s) x y‖≤ε*‖y-x‖^2 := by
  have huc := ((isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).prod
    (isCompact_closedBall (0 : State N) R)).uniformContinuousOn_of_continuous
    hH.continuousOn
  intro ε hε
  obtain ⟨δ,hδ,hm⟩ := (Metric.uniformContinuousOn_iff
    (α := ℝ≥0 × State N) (β := State N →L[ℝ] State N →L[ℝ] ℝ)).mp huc (2*ε) (by positivity)
  refine ⟨δ,hδ,?_⟩
  intro s hs x hx y hy hxy
  obtain ⟨r,hr,he⟩ := line_taylor (hf s) x y
  have hz : x+r • (y-x)∈Metric.closedBall (0 : State N) R :=
    (convex_closedBall (0 : State N) R).add_smul_sub_mem hx hy ⟨hr.1.le,hr.2.le⟩
  have hdist : dist (s,x+r • (y-x)) (s,x)<δ := by
    simp only [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg)]
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_of_nonneg hr.1.le]
    exact (mul_le_of_le_one_left (norm_nonneg _) hr.2.le).trans_lt hxy
  have hHlt : ‖Hessian (f s) (x+r • (y-x))-Hessian (f s) x‖<2*ε := by
    have hh := hm (s,x+r • (y-x)) ⟨hs,hz⟩ (s,x) ⟨hs,hx⟩ hdist
    change dist (Hessian (f s) (x+r • (y-x))) (Hessian (f s) x)<2*ε at hh
    have heq (u v : State N →L[ℝ] State N →L[ℝ] ℝ) : dist u v=‖u-v‖ := dist_eq_norm u v
    rw [heq] at hh
    exact hh
  unfold remainder
  rw [he]
  rw [show (1/2 : ℝ)*Hessian (f s) (x+r • (y-x)) (y-x) (y-x)-
      (1/2 : ℝ)*Hessian (f s) x (y-x) (y-x)=
      (1/2 : ℝ)*(Hessian (f s) (x+r • (y-x))-Hessian (f s) x) (y-x) (y-x) by
        simp only [ContinuousLinearMap.sub_apply];ring]
  calc
    _=(1/2 : ℝ)*‖(Hessian (f s) (x+r • (y-x))-Hessian (f s) x) (y-x) (y-x)‖ := by
      rw [norm_mul,Real.norm_of_nonneg (by norm_num)]
    _≤(1/2 : ℝ)*((2*ε)*‖y-x‖*‖y-x‖) := by
      gcongr
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right hHlt.le (norm_nonneg _))) (norm_nonneg _))
    _=_ := by ring

@[expose] def remainderApprox (f : ℝ≥0 → State N → ℝ) (X : ℝ≥0 → Ω → State N)
    (T : ℝ≥0) (n : ℕ) (ω : Ω) : ℝ :=
  ∑ i∈Finset.range n,remainder (f (uniformPartitionTime T n i))
    (X (uniformPartitionTime T n i) ω) (X (uniformPartitionTime T n (i+1)) ω)

lemma remainder_eventually_bound (f : ℝ≥0 → State N → ℝ)
    (hf : ∀ s,ContDiff ℝ 2 (f s))
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s))))
    (g : ℝ≥0 → State N) (T : ℝ≥0) (hg : ContinuousOn g (Icc 0 T)) :
    ∀ ε : ℝ,0<ε → ∀ᶠ n in atTop,∀ i∈Finset.range (n+1),
      ‖remainder (f (uniformPartitionTime T (n+1) i)) (g (uniformPartitionTime T (n+1) i))
        (g (uniformPartitionTime T (n+1) (i+1)))‖≤
          ε*‖g (uniformPartitionTime T (n+1) (i+1))-g (uniformPartitionTime T (n+1) i)‖^2 := by
  obtain ⟨R,hR⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  intro ε hε
  obtain ⟨δ,hδ,hδbound⟩ := uniform_remainder_time_closedBall f hf hH T R ε hε
  filter_upwards [state_increments_tendsto g T hg δ hδ] with n hn
  intro i hi
  have hip : i+1≤n+1 := Finset.mem_range.mp hi
  apply hδbound _
    (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) ((Nat.le_add_right i 1).trans hip)) _ _ _ _ (hn i hi)
  · simpa only [Metric.mem_closedBall,dist_zero_right] using
      hR _ (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) ((Nat.le_add_right i 1).trans hip))
  · simpa only [Metric.mem_closedBall,dist_zero_right] using
      hR _ (uniformPartitionTime_mem_Icc_of_le T (Nat.zero_lt_succ n) hip)

lemma remainder_subseq_tendsto_zero (f : ℝ≥0 → State N → ℝ)
    (hf : ∀ s,ContDiff ℝ 2 (f s))
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s))))
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) (ω : Ω) (k : ℕ → ℕ)
    (hk : Tendsto k atTop atTop) (q : ℝ)
    (hpath : ContinuousOn (fun s => X s ω) (Icc 0 T))
    (hq : Tendsto (fun n => normQuadraticApprox X T (k n+1) ω) atTop (𝓝 q)) :
    Tendsto (fun n => remainderApprox f X T (k n+1) ω) atTop (𝓝 0) := by
  let C : ℝ := |q|+1
  have hC : 0<C := by dsimp only [C];positivity
  have hqbound : ∀ᶠ n in atTop,normQuadraticApprox X T (k n+1) ω≤C := by
    filter_upwards [hq.eventually (Metric.ball_mem_nhds q zero_lt_one)] with n hn
    simp only [Metric.mem_ball,Real.dist_eq] at hn
    dsimp only [C]
    linarith [(abs_lt.mp hn).2,le_abs_self q]
  rw [Metric.tendsto_atTop]
  intro ε hε
  let δ : ℝ := ε/(2*C)
  have hδ : 0<δ := div_pos hε (mul_pos (by norm_num) hC)
  obtain ⟨m,hm⟩ := eventually_atTop.mp (hqbound.and
    (hk.eventually (remainder_eventually_bound f hf hH (fun s => X s ω) T hpath δ hδ)))
  refine ⟨m,fun n hn => ?_⟩
  obtain ⟨hq',hr⟩ := hm n hn
  rw [dist_eq_norm,sub_zero]
  calc
    ‖remainderApprox f X T (k n+1) ω‖≤∑ i∈Finset.range (k n+1),
      ‖remainder (f (uniformPartitionTime T (k n+1) i)) (X (uniformPartitionTime T (k n+1) i) ω)
        (X (uniformPartitionTime T (k n+1) (i+1)) ω)‖ := norm_sum_le _ _
    _≤∑ i∈Finset.range (k n+1),δ*‖X (uniformPartitionTime T (k n+1) (i+1)) ω-
        X (uniformPartitionTime T (k n+1) i) ω‖^2 := Finset.sum_le_sum hr
    _=δ*normQuadraticApprox X T (k n+1) ω := by rw [← Finset.mul_sum];rfl
    _≤δ*C := mul_le_mul_of_nonneg_left hq' hδ.le
    _<ε := by dsimp only [δ];field_simp;linarith

variable [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- Actual quadratic variation and continuous paths close the spatial
Taylor remainder even when the test varies with physical time. -/
theorem remainder_tendstoInMeasure (f : ℝ≥0 → State N → ℝ)
    (hf : ∀ s,ContDiff ℝ 2 (f s))
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s))))
    (X : ℝ≥0 → Ω → State N) (T : ℝ≥0) (q : Ω → ℝ)
    (hXm : ∀ s,AEStronglyMeasurable (X s) P)
    (hXc : ∀ᵐ ω ∂P,ContinuousOn (fun s => X s ω) (Icc 0 T))
    (hQ : TendstoInMeasure P (fun n => normQuadraticApprox X T (n+1)) atTop q) :
    TendstoInMeasure P (fun n => remainderApprox f X T (n+1)) atTop (fun _ => 0) := by
  have hm : ∀ n,AEStronglyMeasurable (remainderApprox f X T (n+1)) P := by
    intro n
    have hsum := Finset.aestronglyMeasurable_sum (Finset.range (n+1)) (fun i _ =>
      (MultivariateTaylorPartition.remainder_continuous (hf (uniformPartitionTime T (n+1) i))).comp_aestronglyMeasurable
        ((hXm (uniformPartitionTime T (n+1) i)).prodMk (hXm (uniformPartitionTime T (n+1) (i+1)))))
    apply hsum.congr
    exact .of_forall (fun ω => by simp only [Finset.sum_apply];rfl)
  rw [exists_seq_tendstoInMeasure_atTop_iff hm]
  intro ns hns
  obtain ⟨ms,hms,hq⟩ := (hQ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms,hms,?_⟩
  filter_upwards [hXc,hq] with ω hc hqω
  exact remainder_subseq_tendsto_zero f hf hH X T ω (ns ∘ ms)
    (hns.tendsto_atTop.comp hms.tendsto_atTop) (q ω) hc hqω

/-- For a genuine strong SDE the required quadratic variation is derived
from its actual integral equation, not supplied as a Taylor conclusion. -/
theorem strong_remainder_tendsto (D : BrownianDriver N P F)
    {b : Ω → Fin N → State N → ℝ} {sigma : Ω → Fin N → Fin N → State N → ℝ}
    {Z0 : Ω → State N} {X : ℝ≥0 → Ω → State N} (T : ℝ≥0)
    (hX : AnnealedSDECore.IsRandomStrongSolutionOn D b sigma Z0 X T)
    (f : ℝ≥0 → State N → ℝ) (hf : ∀ s,ContDiff ℝ 2 (f s))
    (hH : Continuous (Function.uncurry (fun s => Hessian (f s)))) :
    TendstoInMeasure P (fun n => remainderApprox f X T (n+1)) atTop (fun _ => 0) :=
  remainder_tendstoInMeasure f hf hH X T _
    (fun s => (((hX.2.1 s).mono (F.le s)).aestronglyMeasurable))
    (hX.2.2.1.mono (fun _ h => h.continuousOn))
    (MultivariateItoSums.strong_normQuadratic_tendsto D T hX T le_rfl)

end SphericalAging.SpaceTimeTaylorPartition
