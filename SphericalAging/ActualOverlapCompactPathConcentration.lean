module

public import SphericalAging.ActualOverlapCompactSup
public import SphericalAging.CountableMeshConcentration
public import SphericalAging.ActualOverlapConcentration
public import SphericalAging.TwoScaleConcentrationLimit

public section

/-! Literal compact-time centered correlation concentration. Finite mesh
variances and genuine actual dyadic path tightness imply expected sup²→0. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ActualOverlapCompactPathConcentration
open HardSphereDynamics ActualModelOverlapVariance ActualOverlapTimeModulus ActualOverlapConcentration
open ActualOverlapDyadicApproximation ActualStateDyadicTightness DyadicContinuousChaining
open DyadicSquareSupremum CompactKernelMemoryLimit CountableCenteredSup CountableMeshConcentration
open ActualCompactJointOverlapVariance ActualOverlapVarianceLimit TwoScaleConcentrationLimit
variable {N p : ℕ}
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

@[expose] abbrev MeshIndex (m : ℕ) := Fin (2^m+1)×Fin (2^m+1)

@[expose] def meshOverlap (β R : ℝ≥0) (hR : 0 < (R:ℝ)) (T : ℝ≥0) (m : ℕ) (k : MeshIndex m) :
    AnnealedCutoffProcess.Parameter N p×VectorBrownian.Space N→ℝ :=
  actualOverlap β R hR (uniformPartitionTime T (2^m) k.1.val) (uniformPartitionTime T (2^m) k.2.val)

@[expose] def gridToMesh (T : ℝ≥0) (m : ℕ) (i : GridIndex) : MeshIndex m :=
  (⟨dyadicApproxIndex (gridPair T i).1 T m,Nat.lt_succ_of_le (dyadicApproxIndex_le_pow (gridPair_mem_square T i).1 m)⟩,
   ⟨dyadicApproxIndex (gridPair T i).2 T m,Nat.lt_succ_of_le (dyadicApproxIndex_le_pow (gridPair_mem_square T i).2 m)⟩)

@[expose] def meshRemainderCeiling (p : ℕ) (β T : ℝ≥0) (m : ℕ) : ℝ :=
  2*(4*gridErrorCeiling m+2*tailProbabilityCeiling p β T m)^2+4*tailProbabilityCeiling p β T m

theorem tailProbabilityCeiling_nonneg (p : ℕ) (β T : ℝ≥0) (m : ℕ) :
    0 ≤ tailProbabilityCeiling p β T m := by
  have hc := ActualNormalizedStateFourthIncrement.fourthCoefficient_nonneg p β T
  unfold tailProbabilityCeiling
  norm_num [dyadicRatio]
  positivity

theorem stateBadTail_real_le (hN : 1 ≤ N) (hp : 0 < p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    (AnnealedModelLaw.law N p).real (stateBadTail (p:=p) β R hR T m) ≤ tailProbabilityCeiling p β T m := by
  have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (stateBadTail_measure_le hN hp β R hR hNR T m)
  simpa only [measureReal_def,ENNReal.toReal_ofReal (tailProbabilityCeiling_nonneg p β T m)] using hh

theorem actual_overlap_centered_secondMoment_le_square (hN : 3 ≤ N) (hp : 2 ≤ p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2)
    (s t T : ℝ≥0) (hs : s ≤ T) (ht : t ≤ T) :
    (∫ω,(actualOverlap (p:=p) β R hR s t ω-
      ∫z,actualOverlap β R hR s t z ∂AnnealedModelLaw.law N p)^2 ∂AnnealedModelLaw.law N p) ≤
        jointVarianceCeiling p β (T+1)/(N:ℝ) := by
  rcases le_total s t with hst|hts
  · exact actual_overlap_centered_secondMoment_le hN hp β R hR hNR s t (T+1) hst
      (ht.trans (le_add_right le_rfl)) (by positivity)
  · rw [actualOverlap_symm β R hR s t]
    exact actual_overlap_centered_secondMoment_le hN hp β R hR hNR t s (T+1) hts
      (hs.trans (le_add_right le_rfl)) (by positivity)

theorem overlapCenteredSup_secondMoment_le_mesh (hN : 3 ≤ N) (hp : 2 ≤ p) (β R : ℝ≥0)
    (hR : 0 < (R:ℝ)) (hNR : (N:ℝ) < (R:ℝ)^2) (T : ℝ≥0) (m : ℕ) :
    (∫ω,(overlapCenteredSup N p β R hR T ω)^2 ∂AnnealedModelLaw.law N p) ≤
      (2*((2^m+1:ℕ):ℝ)^2*jointVarianceCeiling p β (T+1))/(N:ℝ)+meshRemainderCeiling p β T m := by
  have hn : 1 ≤ N := by omega
  have hp0 : 0 < p := by omega
  let P := AnnealedModelLaw.law N p
  let b := P.real (stateBadTail (p:=p) β R hR T m)
  have he : 0 ≤ 2*gridErrorCeiling m := by norm_num [gridErrorCeiling,dyadicRatio]; positivity
  have hg := centeredSup_integral_square_le
    (gridOverlap (p:=p) β R hR T) (meshOverlap (p:=p) β R hR T m) (gridToMesh T m)
    (fun i => actualOverlap_memLp_two hn β R hR hNR _ _)
    (fun k => actualOverlap_memLp_two hn β R hR hNR _ _)
    ((actualOverlap_uniform_bound hn β R hR hNR).mono (fun ω hω i => hω _ _))
    ((actualOverlap_uniform_bound hn β R hR hNR).mono (fun ω hω k => hω _ _))
    (stateBadTail_measurableSet β R hR T m) he
    ((actualOverlap_grid_approximation_on_good hn β R hR hNR T m).mono (fun ω hω hgood i =>
      hω hgood (gridPair T i).1 (gridPair T i).2 (gridPair_mem_square T i).1 (gridPair_mem_square T i).2))
  have hEq : (∫ω,(overlapCenteredSup N p β R hR T ω)^2 ∂P)=
      ∫ω,(centeredSup (gridOverlap (p:=p) β R hR T) P ω)^2 ∂P := by
    apply integral_congr_ae
    filter_upwards [overlapCenteredSup_ae_countable hn hp0 β R hR hNR T] with ω hω
    exact congrArg (fun x : ℝ => x^2) hω
  rw [hEq]
  have hmesh : (∑k : MeshIndex m,∫ω,(meshOverlap (p:=p) β R hR T m k ω-
      ∫z,meshOverlap β R hR T m k z ∂P)^2 ∂P) ≤
      ((2^m+1:ℕ):ℝ)^2*jointVarianceCeiling p β (T+1)/(N:ℝ) := by
    calc
      _ ≤ ∑k : MeshIndex m,jointVarianceCeiling p β (T+1)/(N:ℝ) := by
        apply Finset.sum_le_sum
        intro k _
        exact actual_overlap_centered_secondMoment_le_square hN hp β R hR hNR _ _ T
          (uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^m) (Nat.le_of_lt_succ k.1.isLt)).2
          (uniformPartitionTime_mem_Icc_of_le T (by positivity : 0<2^m) (Nat.le_of_lt_succ k.2.isLt)).2
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,
          nsmul_eq_mul,Nat.cast_mul]; ring
  have hb := stateBadTail_real_le hn hp0 β R hR hNR T m
  have hsq : (4*gridErrorCeiling m+2*b)^2 ≤
      (4*gridErrorCeiling m+2*tailProbabilityCeiling p β T m)^2 := by
    apply pow_le_pow_left₀ (by dsimp [b]; have hb0 := measureReal_nonneg (μ:=P) (s:=stateBadTail (p:=p) β R hR T m); nlinarith [he])
    dsimp only [b,P]
    linarith
  dsimp only [meshRemainderCeiling]
  have hg' := hg.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left hmesh (by norm_num)) le_rfl) le_rfl)
  have hbase : (∫ω,(centeredSup (gridOverlap (p:=p) β R hR T) P ω)^2 ∂P) ≤
      2*(((2^m+1:ℕ):ℝ)^2*jointVarianceCeiling p β (T+1)/(N:ℝ))+
        2*(4*gridErrorCeiling m+2*b)^2+4*b := by
    convert hg' using 1 <;> dsimp only [b,P] <;> ring
  calc
    _ ≤ 2*(((2^m+1:ℕ):ℝ)^2*jointVarianceCeiling p β (T+1)/(N:ℝ))+
        2*(4*gridErrorCeiling m+2*b)^2+4*b := hbase
    _ ≤ 2*(((2^m+1:ℕ):ℝ)^2*jointVarianceCeiling p β (T+1)/(N:ℝ))+
        2*(4*gridErrorCeiling m+2*tailProbabilityCeiling p β T m)^2+
          4*tailProbabilityCeiling p β T m := by
      exact add_le_add (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsq (by norm_num)))
        (mul_le_mul_of_nonneg_left hb (by norm_num))
    _ = _ := by ring

theorem meshRemainderCeiling_tendsto_zero (p : ℕ) (β T : ℝ≥0) :
    Tendsto (meshRemainderCeiling p β T) atTop (𝓝 0) := by
  unfold meshRemainderCeiling
  simpa only [mul_zero,zero_add,zero_pow (by norm_num : (2:ℕ)≠0)] using
    ((((gridErrorCeiling_tendsto_zero.const_mul 4).add
      ((tailProbabilityCeiling_tendsto_zero p β T).const_mul 2)).pow 2).const_mul 2).add
        ((tailProbabilityCeiling_tendsto_zero p β T).const_mul 4)

theorem actual_overlap_centered_compact_secondMoment_tendsto_zero {p : ℕ} (dim : ℕ→ℕ)
    (hdim : Tendsto dim atTop atTop) (hp : 2 ≤ p) (β T : ℝ≥0) :
    Tendsto (fun n => ∫ω,(overlapCenteredSup (dim n) p β (modelRadius (dim n))
      (modelRadius_pos (dim n)) T ω)^2 ∂AnnealedModelLaw.law (dim n) p) atTop (𝓝 0) := by
  apply tendsto_zero_of_mesh_bounds (dim:=dim) (A:=fun m =>
    2*((2^m+1:ℕ):ℝ)^2*jointVarianceCeiling p β (T+1))
    hdim (fun n => integral_nonneg (fun _ => sq_nonneg _)) (meshRemainderCeiling_tendsto_zero p β T)
  intro m
  filter_upwards [hdim.eventually (eventually_ge_atTop 3)] with n hn
  exact overlapCenteredSup_secondMoment_le_mesh hn hp β _ _ (modelRadius_sphere_bound (dim n)) T m

end SphericalAging.ActualOverlapCompactPathConcentration
