module

public import SphericalAging.PhysicalForkPastLaw
public import SphericalAging.ActualOverlapConcentration
public import SphericalAging.FiniteScalarAverageMoments
public import SphericalAging.BallResponseEnergyContraction

public section

/-! Common-past fork overlaps concentrate about their genuine canonical
mean. A finite average preserves the actual O(1/N) second-moment bound;
no CK mean identification or memory-decay estimate is needed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.PhysicalForkPastConcentration
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel
  HardSphereDynamics WienerForkTransfer PhysicalForkConstruction PhysicalForkPastLaw
  PhysicalForkWaitingTransfer AnnealedHamiltonianEnergyStein ActualModelOverlapVariance
  ActualOverlapConcentration ActualCompactJointOverlapVariance FiniteScalarAverageMoments
open scoped NNReal ENNReal BigOperators InnerProductSpace
variable {N p K : ℕ}

@[expose] def branchWaitingOverlap (β : ℝ≥0) (t trunk s : ℝ≥0) (b : Fin K)
    (z : ForkSpace N p K) : ℝ :=
  FiniteCorrelationIto.overlap (branch β t trunk b z) (waiting β s z)

@[expose] def meanWaitingOverlap (β : ℝ≥0) (t trunk s : ℝ≥0) (z : ForkSpace N p K) : ℝ :=
  FiniteCorrelationIto.overlap (mean (branch β t trunk) z) (waiting β s z)

@[expose] def canonicalMean (N p : ℕ) (β : ℝ≥0) (s t : ℝ≥0) : ℝ :=
  ∫z,actualOverlap (p:=p) β (N+1) (modelRadius_pos N) s t z ∂AnnealedModelLaw.law N p

theorem meanWaitingOverlap_eq_average (β : ℝ≥0) (t trunk s : ℝ≥0) (z : ForkSpace N p K) :
    meanWaitingOverlap β t trunk s z=(K:ℝ)⁻¹*∑b,branchWaitingOverlap β t trunk s b z := by
  simp only [meanWaitingOverlap,branchWaitingOverlap,FiniteCorrelationIto.overlap,
    mean,real_inner_smul_left,sum_inner]
  rw [←Finset.sum_div]
  ring

theorem branch_waiting_secondMoment_eq_model (β : ℝ≥0) (t trunk s : ℝ≥0)
    (hs : s≤trunk) (b : Fin K) (c : ℝ) :
    (∫z,(branchWaitingOverlap β t trunk s b z-c)^2 ∂forkLaw N p K)=
    ∫z,(actualOverlap (p:=p) β (N+1) (modelRadius_pos N) s t z-c)^2
      ∂AnnealedModelLaw.law N p := by
  let test := fun z : State N×State N => (FiniteCorrelationIto.overlap z.1 z.2-c)^2
  have ht : StronglyMeasurable test := by
    unfold test FiniteCorrelationIto.overlap
    fun_prop
  have hb := (physical_past_law (N:=N) (p:=p) (K:=K) (β:ℝ) t trunk s hs b).integral_comp
    ht.aestronglyMeasurable
  have ho := (hasLaw_map (originalPair_aemeasurable N p β t s)).integral_comp ht.aestronglyMeasurable
  calc
    _=∫z,test (originalPair N p β t s z) ∂AnnealedModelLaw.law N p := hb.trans ho.symm
    _=_ := by
      congr 1
      funext z
      simp only [test,originalPair,actualOverlap,modelProcess,process,FiniteCorrelationIto.overlap]
      rw [real_inner_comm]

theorem branch_waiting_overlap_memLp (hN : 0<N) (β : ℝ≥0) (t trunk s : ℝ≥0) (b : Fin K) :
    MemLp (branchWaitingOverlap β t trunk s b) 2 (forkLaw N p K) := by
  have ha := ((branch_memLp (fork_joint_law (N:=N) (p:=p) β t trunk) b).aestronglyMeasurable.inner
    (waiting_memLp N p K β s).aestronglyMeasurable).mul_const (N:ℝ)⁻¹
  apply MemLp.of_bound (by
    unfold branchWaitingOverlap
    simpa only [FiniteCorrelationIto.overlap,div_eq_mul_inv] using ha) 1
  have hW := (originalTrunk_measurePreserving N p K).quasiMeasurePreserving.ae
    (FiniteStateOrthogonalityTheorem.actual_model_waiting_state_ball hN β s)
  filter_upwards [branch_norm_sq (fork_joint_law (N:=N) (p:=p) β t trunk) b,hW] with z hy hw
  have hyb : ‖branch β t trunk b z‖≤Real.sqrt (N:ℝ) :=
    (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
      (by rw [hy,Real.sq_sqrt (Nat.cast_nonneg N)])
  change ‖FiniteCorrelationIto.overlap (branch β t trunk b z) (waiting β s z)‖≤1
  rw [Real.norm_eq_abs]
  exact BallResponseEnergyContraction.overlap_abs_le_one_ball hN hyb hw

theorem branch_waiting_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p)
    (β : ℝ≥0) (t trunk s : ℝ≥0) (hs : s≤trunk) (hst : s≤t) (b : Fin K) :
    (∫z,(branchWaitingOverlap β t trunk s b z-canonicalMean N p β s t)^2 ∂forkLaw N p K)≤
      jointVarianceCeiling p β (t+1)/(N:ℝ) := by
  rw [branch_waiting_secondMoment_eq_model β t trunk s hs b]
  exact actual_overlap_centered_secondMoment_le hN hp β (N+1) (modelRadius_pos N)
    (modelRadius_sq N) s t (t+1) hst (le_add_right le_rfl) (by positivity)

theorem mean_waiting_centered_secondMoment_le (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk s : ℝ≥0) (hs : s≤trunk) (hst : s≤t) :
    (∫z,(meanWaitingOverlap β t trunk s z-canonicalMean N p β s t)^2 ∂forkLaw N p K)≤
      jointVarianceCeiling p β (t+1)/(N:ℝ) := by
  simp_rw [meanWaitingOverlap_eq_average]
  exact (average_centered_secondMoment_le hK (branchWaitingOverlap β t trunk s)
    (canonicalMean N p β s t) (jointVarianceCeiling p β (t+1)/(N:ℝ))
    (branch_waiting_overlap_memLp (by omega : 0<N) β t trunk s)
    (branch_waiting_centered_secondMoment_le hN hp β t trunk s hs hst)).2

theorem branch_mean_waiting_secondMoment_le (hN : 3≤N) (hp : 2≤p) (hK : 0<K)
    (β : ℝ≥0) (t trunk s : ℝ≥0) (hs : s≤trunk) (hst : s≤t) (b : Fin K) :
    (∫z,(branchWaitingOverlap β t trunk s b z-meanWaitingOverlap β t trunk s z)^2
      ∂forkLaw N p K)≤4*jointVarianceCeiling p β (t+1)/(N:ℝ) := by
  let c := canonicalMean N p β s t
  have hba := branch_waiting_overlap_memLp (p:=p) (by omega : 0<N) β t trunk s b
  have hma : MemLp (meanWaitingOverlap (N:=N) (p:=p) (K:=K) β t trunk s) 2 (forkLaw N p K) := by
    have hm : MemLp (fun z : ForkSpace N p K => (K:ℝ)⁻¹*∑i : Fin K,
        branchWaitingOverlap β t trunk s i z) 2 (forkLaw N p K) :=
      (memLp_finsetSum Finset.univ (fun i _ =>
        branch_waiting_overlap_memLp (p:=p) (by omega : 0<N) β t trunk s i)).const_mul (K:ℝ)⁻¹
    convert hm using 1
    funext z
    exact meanWaitingOverlap_eq_average β t trunk s z
  have hbi : Integrable (fun z => (branchWaitingOverlap β t trunk s b z-c)^2) (forkLaw N p K) :=
    (hba.sub (memLp_const c)).integrable_sq
  have hmi : Integrable (fun z => (meanWaitingOverlap β t trunk s z-c)^2) (forkLaw N p K) :=
    (hma.sub (memLp_const c)).integrable_sq
  calc
    _≤∫z,2*(branchWaitingOverlap β t trunk s b z-c)^2+2*(meanWaitingOverlap β t trunk s z-c)^2
        ∂forkLaw N p K :=
      integral_mono_ae ((hba.sub hma).integrable_sq)
        ((hbi.const_mul 2).add (hmi.const_mul 2))
        (.of_forall fun z => by
          dsimp only [Pi.sub_apply]
          have hsq := sq_nonneg (branchWaitingOverlap β t trunk s b z+meanWaitingOverlap β t trunk s z-2*c)
          nlinarith)
    _=2*(∫z,(branchWaitingOverlap β t trunk s b z-c)^2 ∂forkLaw N p K)+
        2*(∫z,(meanWaitingOverlap β t trunk s z-c)^2 ∂forkLaw N p K) := by
      rw [integral_add (hbi.const_mul 2) (hmi.const_mul 2),integral_const_mul,integral_const_mul]
    _≤_ := by
      have hb := branch_waiting_centered_secondMoment_le hN hp β t trunk s hs hst b
      have hm := mean_waiting_centered_secondMoment_le hN hp hK β t trunk s hs hst
      exact (add_le_add (mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤2))
        (mul_le_mul_of_nonneg_left hm (by norm_num : (0:ℝ)≤2))).trans_eq (by ring)

end SphericalAging.PhysicalForkPastConcentration
