module

public import SphericalAging.ActualGammaPredictorLocalIncrement
public import SphericalAging.ActualGammaPredictorInitialValue
public import SphericalAging.FiniteMartingaleMeshVariance

public section

/-! Genuine earlier-Wiener variance of the actual backward Γ predictor.
The finite predictable-noise estimate is sharpened by vanishing meshes;
no target variance, asymptotic CK row, or independence of past observables
is assumed. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ActualGammaEarlierWienerVariance
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereGammaVariance ActualSphereMarkovRestart
open ActualGammaPredictorMartingale ActualGammaPredictorInitialValue
open ActualGammaPredictorCompactTaylor ActualGammaPredictorLocalIncrement
open FiniteMartingaleMeshVariance
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

section Actual
variable (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (x : State N)
    (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀ U,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) (fun _ => x) X U)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀u,OnSphere (X u ω))
    (T t s : ℝ≥0) (ht : t≤T) (hst : s≤t) (hT : 0<T)

include hN hp hNR hX hSphere ht hst hT in
theorem earlier_predictor_variance_le :
    variance (backwardProcess β R hR J X T t s s) (VectorBrownian.law N)≤
      rowCeiling β J T s*(s : ℝ) := by
  have hn : 0<N := by omega
  have hM := backwardProcess_martingale hn β R hR hNR J X hX hSphere T t s ht hst hT
  have hM2 := backwardProcess_memLp_two hn β R hR hNR J X hX hSphere T t s ht hst
  obtain ⟨C,hC,hBound⟩ := exists_actual_spatialBound β R hR J T t s hT
  have hA := rowCeiling_nonneg β J T s
  have hV := variance_le_of_arbitrarily_small_loss hM hM2 s (rowCeiling β J T s) hA ?_
  · rw [backwardProcess_variance_zero β R hR J x X hX T t s,sub_zero] at hV
    exact hV
  intro η hη
  refine ⟨(1+1/η)*errorCeiling β J T C,mul_nonneg (by positivity) (errorCeiling_nonneg β J T C),?_⟩
  apply Filter.Eventually.of_forall
  intro n i hi
  let r := uniformPartitionTime s (n+1) i
  let h := s/((n+1 : ℕ) : ℝ≥0)
  have hq : uniformPartitionTime s (n+1) (i+1)=r+h := by
    dsimp only [r,h,uniformPartitionTime]
    simp only [Nat.cast_add,Nat.cast_one]
    ring
  have hqs : r+h≤s := by
    rw [←hq]
    exact (uniformPartitionTime_mem_Icc_of_le s (by omega : 0<n+1) (by omega : i+1≤n+1)).2
  have hrs : r≤s := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤h from bot_le)).trans hqs
  have hrT : r≤T := hrs.trans (hst.trans ht)
  have hhT : h≤T := by
    have hh : h≤s := by
      dsimp only [h]
      exact div_le_self (show (0 : ℝ≥0)≤s from bot_le) (by exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n)))
    exact hh.trans (hst.trans ht)
  have hstep := predictor_increment_secondMoment hN hp β R hR hNR J X hX hSphere
    T t s T r h ht hst hT hqs hrT hhT C hC (hBound (r+h) ⟨bot_le,hqs⟩) η hη
  change (∫ ω,(backwardProcess β R hR J X T t s (uniformPartitionTime s (n+1) (i+1)) ω-
    backwardProcess β R hR J X T t s r ω)^2 ∂VectorBrownian.law N)≤_
  rw [hq]
  simp only [backwardProcess,min_eq_left hqs,min_eq_left hrs]
  simpa only [h,meshSize,NNReal.coe_div,NNReal.coe_natCast] using hstep

end Actual

/-- Every SDE and initial-value input is discharged for the actual
canonical joint process. -/
theorem joint_earlier_predictor_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (T t s : ℝ≥0) (ht : t≤T) (hst : s≤t) (hT : 0<T) :
    variance (backwardProcess β R hR J
      (jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x)) T t s s)
      (VectorBrownian.law N)≤rowCeiling β J T s*(s : ℝ) :=
  earlier_predictor_variance_le hN hp β R hR hNR J x _
    (fun U => jointProcess_physical (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR J x hx U)
    (jointProcess_onSphere (by omega : N≠0) (VectorBrownian.driver N) β R hR hNR J x hx)
    T t s ht hst hT

end SphericalAging.ActualGammaEarlierWienerVariance
