module

public import SphericalAging.ActualSphereCKBridges
public import SphericalAging.ActualMeanKernelDimensionTransfer

public section

/-! Remark 3.5: actual signed response primitives and their genuine total
variation bound give every continuous weighted compact-horizon passage.
No positivity of the finite response rows, primitive limit or response
convergence is supplied as an input. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal ENNReal
namespace SphericalAging.ActualContinuousWeightedResponseLimit
open CKSpecification CKPhysicalConsequences ActualResponseWindowLimit ActualSphereCKBridges
  ActualEnergyUniformBridge WeightedPrimitiveConvergence ActualMeanKernelDimensionTransfer
  AnnealedResponseMatrixContraction
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency true
variable {p : ℕ}

 theorem actual_signed_weighted_response_uniform_limit (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (d : CKData) (hd : CKEquations p β d) (T : ℝ≥0)
    (w : ℝ×ℝ→ℝ) (hw : Continuous w) :
    TendstoUniformlyOn (fun n t => ∫u in (0:ℝ)..t,w (t,u)*
      (dimensionResponseRow (by omega : 2≤p) β dim n t u-d.R t u))
        (fun _ => 0) atTop (Icc 0 (T:ℝ)) := by
  let dim₃ := floorDimension dim
  have hDim : ∀n,3≤dim₃ n := floorDimension_ge_three dim
  have hprim := canonical_ResponsePrimitiveBridge hp β hβ d hd dim₃ hDim (floorDimension_tendsto hdim)
  let A := Real.sqrt (1+annealedFourthConstant p β T)
  have hAi : 0≤A := Real.sqrt_nonneg _
  have hr (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (T:ℝ)) :
      IntervalIntegrable (dimensionResponseRow (by omega : 2≤p) β dim₃ n t) volume 0 t :=
    responseRow_integrable (by omega : 2≤p) β (dim₃ n-1) ht.1
  have hR (t : ℝ) (ht : t∈Icc 0 (T:ℝ)) : IntervalIntegrable (fun u => d.R t u) volume 0 t :=
    (hd.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨hu.1,hu.2⟩)).intervalIntegrable_of_Icc ht.1
  have hdiff (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (T:ℝ)) :
      IntervalIntegrable (fun u => dimensionResponseRow (by omega : 2≤p) β dim₃ n t u-d.R t u) volume 0 t :=
    (hr n t ht).sub (hR t ht)
  have hRb (t : ℝ) (ht : t∈Icc 0 (T:ℝ)) (u : ℝ) (hu : u∈Icc 0 t) : |d.R t u|≤1 := by
    have hphys := physical_bounds_of_equations hd
    rw [abs_of_nonneg (hphys.2 t u hu.1 hu.2)]
    exact (response_le_correlation hd hu.1 hu.2).trans (hphys.1 t u ht.1 hu.1).2
  have hvariation (n : ℕ) (t : ℝ) (ht : t∈Icc 0 (T:ℝ)) :
      (∫u in (0:ℝ)..t,|dimensionResponseRow (by omega : 2≤p) β dim₃ n t u-d.R t u|)≤(T:ℝ)*A+T := by
    calc
      _≤∫u in (0:ℝ)..t,|dimensionResponseRow (by omega : 2≤p) β dim₃ n t u|+1 := by
        apply intervalIntegral.integral_mono_on ht.1 (hdiff n t ht).abs ((hr n t ht).abs.add intervalIntegrable_const)
        intro u hu
        exact (abs_sub _ _).trans (add_le_add le_rfl (hRb t ht u hu))
      _=(∫u in (0:ℝ)..t,|dimensionResponseRow (by omega : 2≤p) β dim₃ n t u|)+t := by
        rw [intervalIntegral.integral_add (hr n t ht).abs intervalIntegrable_const]
        simp
      _≤_ := add_le_add (dimensionResponseRow_variation (by omega : 2≤p) β T dim₃ n ht) ht.2
  have hlim := weighted_integrals_tendstoUniformlyOn T.coe_nonneg (by positivity : 0≤(T:ℝ)*A+T)
    (fun n t u => dimensionResponseRow (by omega : 2≤p) β dim₃ n t u-d.R t u)
      w hw hdiff hvariation (hprim T)
  apply hlim.congr
  filter_upwards [floorDimension_eventually_eq hdim] with n hn
  intro t _
  simp only [dimensionResponseRow,dim₃,hn]

 theorem actual_signed_weighted_response_window_limit (hp : 3≤p) (β : ℝ≥0) (hβ : 0<β)
    (dim : ℕ→ℕ) (hdim : Tendsto dim atTop atTop)
    (d : CKData) (hd : CKEquations p β d) (T L : ℝ≥0)
    (w : ℝ→ℝ) (hw : Continuous w) :
    Tendsto (fun n => ∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),w (((T+L:ℝ≥0):ℝ)-u)*
      (dimensionResponseRow (by omega : 2≤p) β dim n (T+L) u-d.R (T+L) u)) atTop (𝓝 0) := by
  have hh := actual_continuous_weighted_window_limit (by omega : 2≤p) β (floorDimension dim) d hd
    (canonical_ResponsePrimitiveBridge hp β hβ d hd (floorDimension dim) (floorDimension_ge_three dim)
      (floorDimension_tendsto hdim)) T L w hw
  apply hh.congr'
  filter_upwards [floorDimension_eventually_eq hdim] with n hn
  simp only [dimensionResponseRow,hn]

end SphericalAging.ActualContinuousWeightedResponseLimit
