module

public import SphericalAging.LogBetaRenewalSeries
public import SphericalAging.BoundedDensityConvolution

public section

/-! Genuine convolution-law identities imply the exact pointwise finite
smoothing decomposition for every actual log-beta density power. -/
open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal ENNReal
namespace SphericalAging.LogBetaConvolutionShift
noncomputable section
set_option maxHeartbeats 1000000
open LogBetaRenewal LogBetaMoments LogBetaConvolutionPowers LogBetaSmoothedRenewal
  LogBetaRenewalSeries GammaEnvelopeDRI AbsorptionCutoff.Renewal

/-- The identity is proved pointwise from actual convolution measures and
continuous-density uniqueness, including the zeroth Dirac convolution law. -/
theorem powerDensity_average_identity {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (j : ℕ) (hj : 1<((j:ℝ)+1)*a) (n : ℕ) (y : ℝ) :
    powerDensity ρ a (n+j) y=
      ∫ s : ℝ,powerDensity ρ a j (y-s) ∂convPow (law ρ a) n := by
  letI := law_probability hρ ha
  let ν := convPow (law ρ a) n
  let H := powerDensity ρ a j
  let F := powerDensity ρ a (n+j)
  obtain ⟨hH,hDRI,B,hB,hBound⟩ := smoothing_properties hρ ha ha1 j hj
  have hHM : ∀x : ℝ,‖H x‖≤B := fun x => by
    rw [Real.norm_eq_abs,abs_of_nonneg (hBound x).1]
    exact (hBound x).2
  have hFshape : 1<(((n+j:ℕ):ℝ)+1)*a := by
    push_cast
    nlinarith only [hj,ha,show 0≤(n:ℝ) from Nat.cast_nonneg n]
  have hF := (powerDensity_properties hρ ha ha1 (n+j)).1
  have hFC : Continuous F := envelope_continuous _ _ _ _ (powerConstant_positive hρ ha (n+j)).le hFshape
    hF (powerDensity_properties hρ ha ha1 (n+j)).2.1
  have hAver : Continuous (BoundedDensityConvolution.average ν H) :=
    BoundedDensityConvolution.average_continuous ν hH hHM
  have hLaw : volume.withDensity (fun x => ENNReal.ofReal (F x))=
      volume.withDensity (fun x => ENNReal.ofReal (BoundedDensityConvolution.average ν H x)) := by
    calc
      _ = convPow (law ρ a) ((n+j)+1) := (convPow_law_eq_withDensity hρ ha ha1 (n+j)).symm
      _ = convPow (law ρ a) n ∗ convPow (law ρ a) (j+1) := by rw [←convPow_add,Nat.add_assoc]
      _ = ν ∗ volume.withDensity (fun x => ENNReal.ofReal (H x)) := by rw [convPow_law_eq_withDensity hρ ha ha1 j]
      _ = _ := BoundedDensityConvolution.conv_withDensity_bounded ν hH (fun x => (hBound x).1) hHM
  have hUnique := BoundedDensityConvolution.continuous_density_unique hFC hAver hF.nonnegative
    (BoundedDensityConvolution.average_nonnegative ν (fun x => (hBound x).1)) hLaw
  exact congrFun hUnique y

/-- The actual full renewal series is summable and equals its finite
initial part plus the actual smoothed renewal series. -/
theorem renewalDensity_decomposition {ρ a : ℝ} (hρ : 0<ρ) (ha : 0<a) (ha1 : a<1)
    (j : ℕ) (hj : 1<((j:ℝ)+1)*a) :
    (∀ y : ℝ,Summable (fun n : ℕ => powerDensity ρ a n y)) ∧
    ∀ y : ℝ,renewalDensity ρ a y=initialDensitySum ρ a j y+smoothedRenewal ρ a j y := by
  obtain ⟨hSum,_⟩ := smoothed_renewal_uniform_bound hρ ha ha1 j hj
  have hTail (y : ℝ) : Summable (fun n : ℕ => powerDensity ρ a (n+j) y) := by
    apply (hSum y).congr
    intro n
    exact (powerDensity_average_identity hρ ha ha1 j hj n y).symm
  have hFull (y : ℝ) : Summable (fun n : ℕ => powerDensity ρ a n y) :=
    (summable_nat_add_iff (f:=fun n : ℕ => powerDensity ρ a n y) j).mp (hTail y)
  refine ⟨hFull,?_⟩
  intro y
  have hTailEq : (∑' n : ℕ,powerDensity ρ a (n+j) y)=smoothedRenewal ρ a j y := by
    apply tsum_congr
    intro n
    exact powerDensity_average_identity hρ ha ha1 j hj n y
  have hSplit := (hFull y).sum_add_tsum_nat_add j
  rw [hTailEq] at hSplit
  exact hSplit.symm

end
end SphericalAging.LogBetaConvolutionShift
