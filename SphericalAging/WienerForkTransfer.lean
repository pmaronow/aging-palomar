module

public import SphericalAging.ActualWeightedWiener

public section

/-! Literal finite branch means on independent trunk/future Wiener products.
Only the preceding endpoint/past joint law is assumed; weighted pairing
transfer is proved by genuine Wiener L² density. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped ENNReal NNReal Topology BigOperators InnerProductSpace RealInnerProductSpace
namespace SphericalAging.WienerForkTransfer
open FiniteModel HardSphereDynamics AnnealedHamiltonianEnergyStein
open WienerVectorGaussian WienerTrunkWeight WienerPairingFunctional WeightedWienerExtension
open ActualWeightedWiener

@[expose] abbrev FutureSpace (N K : ℕ) := Fin K→VectorBrownian.Space N
@[expose] def futureLaw (N K : ℕ) : Measure (FutureSpace N K) :=
  Measure.pi (fun _ => VectorBrownian.law N)
instance futureLaw_probability (N K : ℕ) : IsProbabilityMeasure (futureLaw N K) := by
  unfold futureLaw
  infer_instance
@[expose] abbrev Background (N p K : ℕ) := AnnealedCutoffProcess.Parameter N p×FutureSpace N K
@[expose] def seedLaw (N p K : ℕ) : Measure (Background N p K) :=
  (AnnealedModelLaw.parameterLaw N p).prod (futureLaw N K)
instance seedLaw_probability (N p K : ℕ) : IsProbabilityMeasure (seedLaw N p K) := by
  unfold seedLaw
  infer_instance
@[expose] abbrev ForkSpace (N p K : ℕ) := Background N p K×VectorBrownian.Space N
@[expose] def forkLaw (N p K : ℕ) : Measure (ForkSpace N p K) :=
  (seedLaw N p K).prod (VectorBrownian.law N)
instance forkLaw_probability (N p K : ℕ) : IsProbabilityMeasure (forkLaw N p K) := by
  unfold forkLaw
  infer_instance

@[expose] abbrev History (N : ℕ) (T : ℝ≥0) := Iic T→Vector N
@[expose] def trunkHistory {N : ℕ} (T : ℝ≥0) (ω : VectorBrownian.Space N) : History N T :=
  fun u => WithLp.toLp 2 (fun i => ω i u)
theorem trunkHistory_measurable (N : ℕ) (T : ℝ≥0) : Measurable (trunkHistory (N:=N) T) := by
  apply measurable_pi_iff.mpr
  intro u
  exact (by fun_prop : Measurable (WithLp.toLp 2 : (Fin N→ℝ)→Vector N)).comp
    (VectorBrownian.process_measurable N u)

@[expose] def originalJoint (N p : ℕ) (β : ℝ) (t T : ℝ≥0)
    (ω : AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N) : Vector N×History N T :=
  (modelProcess N p β t ω,trunkHistory T ω.2)
theorem originalJoint_aemeasurable (N p : ℕ) (β : ℝ) (t T : ℝ≥0) :
    AEMeasurable (originalJoint N p β t T) (AnnealedModelLaw.law N p) :=
  (model_memLp N p β t).aestronglyMeasurable.aemeasurable.prodMk
    ((trunkHistory_measurable N T).comp measurable_snd).aemeasurable

/-- The exact relevant marginal of the preceding physical fork standing law:
each endpoint and the entire trunk past have the original annealed law. -/
@[expose] def ForkJointLaw {N p K : ℕ} (β : ℝ) (t T : ℝ≥0)
    (Y : Fin K→ForkSpace N p K→Vector N) : Prop :=
  ∀ b,HasLaw (fun ω => (Y b ω,trunkHistory T ω.2))
    ((AnnealedModelLaw.law N p).map (originalJoint N p β t T)) (forkLaw N p K)

theorem branch_memLp {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) (b : Fin K) :
    MemLp (Y b) 2 (forkLaw N p K) := by
  have hm : MemLp (Prod.fst : Vector N×History N T→Vector N) 2
      ((AnnealedModelLaw.law N p).map (originalJoint N p β t T)) :=
    (memLp_map_measure_iff measurable_fst.aestronglyMeasurable
      (originalJoint_aemeasurable N p β t T)).mpr (model_memLp N p β t)
  exact (hY b).memLp_comp hm

theorem model_norm_sq (N p : ℕ) (β : ℝ) (t : ℝ≥0) :
    ∀ᵐ ω ∂AnnealedModelLaw.law N p,‖modelProcess N p β t ω‖^2=(N:ℝ) := by
  by_cases hN : 0<N
  · filter_upwards [(ActualModelRestart.modelProcess_physical (p:=p) hN β).2] with ω hω
    exact (real_inner_self_eq_norm_sq _).symm.trans (hω t)
  · have hz : N=0 := by omega
    subst N
    exact Eventually.of_forall (fun ω => by
      have he : modelProcess 0 p β t ω=0 := Subsingleton.elim _ _
      simp [he])

theorem branch_norm_sq {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) (b : Fin K) :
    ∀ᵐ ω ∂forkLaw N p K,‖Y b ω‖^2=(N:ℝ) := by
  have hm : Measurable (fun z : Vector N×History N T => ‖z.1‖^2=(N:ℝ)) :=
    measurable_fst.norm.pow_const 2 |>.eq measurable_const
  apply (hY b).ae_iff hm |>.mpr
  exact (ae_map_iff (originalJoint_aemeasurable N p β t T)
    (measurableSet_setOfPred.mpr hm)).mpr (model_norm_sq N p β t)

@[expose] def branchLp {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) (b : Fin K) :
    Lp (Vector N) 2 (forkLaw N p K) := (branch_memLp hY b).toLp (Y b)

@[expose] def mean {N p K : ℕ} (Y : Fin K→ForkSpace N p K→Vector N) (ω : ForkSpace N p K) : Vector N :=
  (K:ℝ)⁻¹ • ∑ b : Fin K,Y b ω

@[expose] def meanLp {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) :
    Lp (Vector N) 2 (forkLaw N p K) := (K:ℝ)⁻¹ • ∑ b : Fin K,branchLp Y hY b

theorem meanLp_coe {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) :
    (meanLp Y hY : ForkSpace N p K→Vector N)=ᵐ[forkLaw N p K] mean Y := by
  have hi : ∀ b : Fin K,(branchLp Y hY b : ForkSpace N p K→Vector N)=ᵐ[forkLaw N p K] Y b :=
    fun b => (branch_memLp hY b).coeFn_toLp
  filter_upwards [Lp.coeFn_smul (K:ℝ)⁻¹ (∑ b : Fin K,branchLp Y hY b),
    Lp.coeFn_finsetSum Finset.univ (fun b : Fin K => branchLp Y hY b),
    ae_all_iff.mpr hi] with ω h1 h2 h3
  change ((K:ℝ)⁻¹ • ∑ b : Fin K,branchLp Y hY b) ω=(K:ℝ)⁻¹ • ∑ b : Fin K,Y b ω
  rw [h1]
  simp only [Pi.smul_apply,h2,Finset.sum_apply,h3]

theorem mean_norm_bound {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (hK : 0<K) {Y : Fin K→ForkSpace N p K→Vector N} (hY : ForkJointLaw β t T Y) :
    ∀ᵐ ω ∂forkLaw N p K,‖mean Y ω‖≤Real.sqrt N := by
  have hKpos : (0:ℝ)<K := by exact_mod_cast hK
  filter_upwards [ae_all_iff.mpr (fun b => branch_norm_sq hY b)] with ω hω
  have hn (b : Fin K) : ‖Y b ω‖=Real.sqrt N :=
    (Real.sqrt_sq (norm_nonneg _)).symm.trans (congrArg Real.sqrt (hω b))
  calc
    ‖mean Y ω‖ = (K:ℝ)⁻¹ * ‖∑ b : Fin K,Y b ω‖ := by
      simp [mean,norm_smul,Real.norm_eq_abs,abs_of_nonneg hKpos.le]
    _ ≤ (K:ℝ)⁻¹ * ∑ b : Fin K,‖Y b ω‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hKpos.le)
    _ = _ := by simp [hn];field_simp

theorem meanLp_norm_sq_le {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (hK : 0<K) (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) :
    ‖meanLp Y hY‖^2≤(N:ℝ) := by
  apply norm_sq_le_of_sphere_bound (seedLaw N p K)
  filter_upwards [meanLp_coe Y hY,mean_norm_bound hK hY] with ω h1 h2
  rw [h1]
  exact (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mpr h2 |>.trans_eq
    (Real.sq_sqrt (Nat.cast_nonneg N))

theorem branch_prefix_transfer {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y)
    (b : Fin K) {u : ℝ≥0} (hu : u≤T) :
    pairingFunctional (seedLaw N p K) (branchLp Y hY b) (intervalIndicator u)=
      actualPrefixPairing N p β t u := by
  let test : Vector N×History N T→ℝ := fun z => ⟪z.1,z.2 ⟨u,hu⟩⟫_ℝ
  have hc : Continuous (fun z : Vector N×Vector N => ⟪z.1,z.2⟫_ℝ) :=
    continuous_fst.inner continuous_snd
  have hm : Measurable test := hc.measurable.comp
    (measurable_fst.prodMk ((measurable_pi_apply (⟨u,hu⟩ : Iic T)).comp measurable_snd))
  have he := (hY b).integral_comp hm.aestronglyMeasurable
  have ho := (hasLaw_map (originalJoint_aemeasurable N p β t T)).integral_comp
    hm.aestronglyMeasurable
  have hij : (∫ ω,⟪Y b ω,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ ∂forkLaw N p K)=
      ∫ ω,⟪modelProcess N p β t ω,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ
        ∂AnnealedModelLaw.law N p := by
    simpa only [test,Function.comp_apply,originalJoint,trunkHistory] using he.trans ho.symm
  rw [pairingFunctional_prefix]
  unfold actualPrefixPairing
  congr 1
  calc
    _ = ∫ ω,⟪Y b ω,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ ∂forkLaw N p K := by
      apply integral_congr_ae
      filter_upwards [(branch_memLp hY b).coeFn_toLp] with ω hω
      exact congrArg (fun x => ⟪x,WithLp.toLp 2 (fun i => ω.2 i u)⟫_ℝ) hω
    _ = _ := hij

@[expose] def meanFunctional {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) : TimeL2→L[ℝ]ℝ :=
  pairingFunctional (seedLaw N p K) (meanLp Y hY)

theorem meanFunctional_prefix {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (hK : 0<K) (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y)
    {u : ℝ≥0} (hu : u≤T) :
    meanFunctional Y hY (intervalIndicator u)=actualPrefixPairing N p β t u := by
  have hKne : (K:ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt hK
  have he : meanFunctional Y hY (intervalIndicator u)=(K:ℝ)⁻¹ *
      ∑ b : Fin K,pairingFunctional (seedLaw N p K) (branchLp Y hY b) (intervalIndicator u) := by
    simp only [meanFunctional,pairingFunctional,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply,innerSL_apply_apply,meanLp,real_inner_smul_left,
      sum_inner,smul_eq_mul]
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [he]
  simp_rw [branch_prefix_transfer Y hY _ hu]
  simp [hKne]

@[expose] def meanPairing {N p K : ℕ} (Y : Fin K→ForkSpace N p K→Vector N) (k : TimeL2) : ℝ :=
  (N:ℝ)⁻¹ * ∫ ω,⟪mean Y ω,vectorIntegral k ω.2⟫_ℝ ∂forkLaw N p K

theorem meanFunctional_apply {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) (k : TimeL2) :
    meanFunctional Y hY k=meanPairing Y k := by
  rw [meanFunctional,pairingFunctional_apply]
  unfold meanPairing
  congr 1
  apply integral_congr_ae
  filter_upwards [meanLp_coe Y hY] with ω hω
  exact congrArg (fun x => ⟪x,vectorIntegral k ω.2⟫_ℝ) hω

theorem meanFunctional_norm_le {N p K : ℕ} {β : ℝ} {t T : ℝ≥0}
    (hK : 0<K) (Y : Fin K→ForkSpace N p K→Vector N) (hY : ForkJointLaw β t T Y) :
    ‖meanFunctional Y hY‖≤1 :=
  pairingFunctional_norm_le (seedLaw N p K) _ (meanLp_norm_sq_le hK Y hY)

theorem weighted_fork_from_prefix {ι : Type} {l : Filter ι} (dims : ι→ℕ)
    (p K : ℕ) (hK : 0<K) (β : ℝ) (t T : ℝ≥0)
    (Y : ∀ i,Fin K→ForkSpace (dims i) p K→Vector (dims i))
    (hY : ∀ i,ForkJointLaw β t T (Y i))
    {r k : ℝ→ℝ} (hr : ContinuousOn r (Icc 0 (T:ℝ)))
    (hk : ContinuousOn k (Icc 0 (T:ℝ)))
    (hprefix : ∀ u : ℝ≥0,u≤T→Tendsto (fun i => actualPrefixPairing (dims i) p β t u) l
      (𝓝 (Real.sqrt 2 * ∫v in (0:ℝ)..(u:ℝ),r v))) :
    Tendsto (fun i => meanPairing (Y i) (weight k T hk)) l
      (𝓝 (Real.sqrt 2 * ∫u in (0:ℝ)..(T:ℝ),k u*r u)) := by
  have hh := weighted_from_unweighted (fun i => meanFunctional (Y i) (hY i))
    (fun i => meanFunctional_norm_le hK (Y i) (hY i)) hr hk (by
      intro u hu
      simpa only [meanFunctional_prefix hK _ _ hu] using hprefix u hu)
  simpa only [meanFunctional_apply] using hh

theorem gaussian_trunk_independent_disorder {N p K : ℕ} {k : ℝ→ℝ} {T : ℝ≥0}
    (hk : ContinuousOn k (Icc 0 (T:ℝ))) (hunit : (∫u in (0:ℝ)..(T:ℝ),k u^2)=1) :
    HasLaw (fun ω : ForkSpace N p K => vectorIntegral (weight k T hk) ω.2)
      (stdGaussian (Vector N)) (forkLaw N p K) ∧
    IndepFun (fun ω : ForkSpace N p K => vectorIntegral (weight k T hk) ω.2)
      (fun ω => ω.1.1.1) (forkLaw N p K) := by
  obtain ⟨hlaw,hi⟩ := source_gaussian_trunk (seedLaw N p K) hk hunit
  refine ⟨hlaw,?_⟩
  exact hi.comp measurable_id (measurable_fst.comp measurable_fst)

end SphericalAging.WienerForkTransfer
