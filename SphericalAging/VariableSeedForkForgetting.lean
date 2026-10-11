module

public import SphericalAging.ForkForgettingLimit
public import SphericalAging.ForkWaitingOverlapTransfer
public import SphericalAging.RandomVectorBounds
public import SphericalAging.VariableSeedOrthogonality

public section

/-! Genuine general-spin fork saturation and waiting-state transfer.
The inputs are preceding finite-fork errors, profile normalization,
adaptive span orthogonality and Euler approximation. Actual energies,
pairings, normalized/projected means and all boundedness are constructed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2500000
namespace SphericalAging.VariableSeedForkForgetting
open MeasureTheory ProbabilityTheory Filter Set FiniteModel
  ForkEnergyComparison RandomGaussianPairing ForkNormalizedEnergy RandomVectorBounds
  AlgorithmEnergyDeficit ForkForgettingLimit ForkWaitingOverlapTransfer
open scoped Topology ENNReal InnerProductSpace

theorem from_actual_fork_approximation {Θ : Type*} {l : Filter Θ}
    {p : ℕ} (hp : 0<p) (dim : ℕ→ℕ) (hDim : ∀n,0<dim n)
    {Ω : Θ→ℕ→Type} [∀θ n,MeasurableSpace (Ω θ n)]
    (μ : ∀θ n,Measure (Ω θ n)) [∀θ n,IsProbabilityMeasure (μ θ n)]
    (J : ∀θ n,Ω θ n→Disorder (dim n) p) (hJ : ∀θ n,HasLaw (J θ n) (disorderLaw (dim n) p) (μ θ n))
    (A M X : ∀θ n,Ω θ n→Vector (dim n))
    (Y : ℕ→∀θ n,Ω θ n→Vector (dim n))
    (hA : ∀θ n,AEStronglyMeasurable (A θ n) (μ θ n))
    (hM : ∀θ n,AEStronglyMeasurable (M θ n) (μ θ n))
    (hX : ∀θ n,AEStronglyMeasurable (X θ n) (μ θ n))
    (hY : ∀m θ n,AEStronglyMeasurable (Y m θ n) (μ θ n))
    (hAb : ∀θ n,∀ᵐω ∂μ θ n,‖A θ n ω‖≤Real.sqrt (dim n))
    (hMb : ∀θ n,∀ᵐω ∂μ θ n,‖M θ n ω‖≤Real.sqrt (dim n))
    (hXb : ∀θ n,∀ᵐω ∂μ θ n,‖X θ n ω‖≤Real.sqrt (dim n))
    (hYb : ∀m θ n,∀ᵐω ∂μ θ n,‖Y m θ n ω‖≤Real.sqrt (dim n))
    {Q c h γ ε κ : Θ→ℝ} {E ρ₀ D₀ C₀ C_Euler : ℝ}
    (hQ : ∀θ,0<Q θ ∧ Q θ≤1)
    (hρ : ∀θ,0≤(Q θ)^(-((p:ℝ)/2)) ∧ (Q θ)^(-((p:ℝ)/2))≤ρ₀)
    (hD : ∀θ,comparison p (Q θ)≤D₀)
    (hRadius : ∀θ,(Real.sqrt (Q θ))⁻¹≤C₀)
    (hγ : ∀θ,0≤γ θ) (hε : ∀θ,0≤ε θ) (hκ : ∀θ,0≤κ θ)
    (hc : ∀θ,0≤c θ) (hCEuler : 0≤C_Euler)
    (hMeanEnergy : ∀θ,limsup
      (fun n => |expectedEnergy (μ:=μ θ n) (J θ n) (M θ n)-h θ|) atTop≤γ θ)
    (hAlgorithmApprox : ∀θ,limsup
      (fun n => distanceRoot (μ θ n) (dim n) (A θ n) (projected (Q θ) (M θ n))) atTop≤ε θ)
    (hProjectionApprox : ∀θ,limsup
      (fun n => distanceRoot (μ θ n) (dim n) (projected (Q θ) (M θ n)) (normalized (Q θ) (M θ n))) atTop≤κ θ)
    (hSaturation : Tendsto (fun θ => (Q θ)^(-((p:ℝ)/2))*h θ) l (𝓝 E))
    (hγLimit : Tendsto γ l (𝓝 0)) (hεLimit : Tendsto ε l (𝓝 0)) (hκLimit : Tendsto κ l (𝓝 0))
    (hSpan : ∀m : ℕ,0<m→Tendsto
      (fun θ => deficit E (fun n => expectedEnergy (μ:=μ θ n) (J θ n) (A θ n))) l (𝓝 0)→
      Tendsto (fun θ => limsup
        (fun n => ∫ω,|inner ℝ (A θ n ω) (Y m θ n ω)/(dim n:ℝ)|^2 ∂μ θ n) atTop) l (𝓝 0))
    (hEuler : ∀m : ℕ,0<m→∀θ,limsup
      (fun n => ∫ω,‖X θ n ω-Y m θ n ω‖^2/(dim n:ℝ) ∂μ θ n) atTop≤C_Euler/(m:ℝ))
    (hPairBridge : ∀θ,Tendsto
      (fun n => pairing (μ:=μ θ n) (M θ n) (X θ n)) atTop (𝓝 (c θ))) :
    Tendsto (fun θ => deficit E
      (fun n => expectedEnergy (μ:=μ θ n) (J θ n) (A θ n))) l (𝓝 0) ∧
    Tendsto c l (𝓝 0) := by
  have hALp θ n : MemLp (A θ n) 2 (μ θ n) := MemLp.of_bound (hA θ n) _ (hAb θ n)
  have hMLp θ n : MemLp (M θ n) 2 (μ θ n) := MemLp.of_bound (hM θ n) _ (hMb θ n)
  have hXLp θ n : MemLp (X θ n) 2 (μ θ n) := MemLp.of_bound (hX θ n) _ (hXb θ n)
  let alg θ n := expectedEnergy (μ:=μ θ n) (J θ n) (A θ n)
  let mean θ n := expectedEnergy (μ:=μ θ n) (J θ n) (M θ n)
  let first θ n := distanceRoot (μ θ n) (dim n) (A θ n) (projected (Q θ) (M θ n))
  let second θ n := distanceRoot (μ θ n) (dim n) (projected (Q θ) (M θ n)) (normalized (Q θ) (M θ n))
  have hAlgBound θ : IsBoundedUnder (·≤·) atTop (alg θ) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (le_abs_self _).trans (energy_abs_le (hDim n) hp (hJ θ n) (hA θ n) (hAb θ n)))
  have hMeanBound θ : IsBoundedUnder (·≤·) atTop (fun n => |mean θ n-h θ|) := by
    have hb : ∀ᶠn in atTop,|mean θ n-h θ|≤GaussianLandscapeMoments.momentCeiling p 1+|h θ| :=
      Eventually.of_forall fun n => (abs_sub _ _).trans
        (add_le_add (energy_abs_le (hDim n) hp (hJ θ n) (hM θ n) (hMb θ n)) le_rfl)
    exact isBoundedUnder_of_eventually_le hb
  have hFirstBound θ : IsBoundedUnder (·≤·) atTop (first θ) := by
    have hb : ∀ᶠn in atTop,first θ n≤2 := Eventually.of_forall fun n => by
      exact (distanceRoot_le (hDim n) (hALp θ n) (projected_memLp (Q:=Q θ) (hDim n) (hMLp θ n))
        (C:=1) (D:=1) (by norm_num) (by norm_num)
        (by simpa only [one_mul] using hAb θ n) (by simpa only [one_mul] using projected_bound (Q θ) (M θ n))).trans_eq (by norm_num)
    exact isBoundedUnder_of_eventually_le hb
  have hSecondBound θ : IsBoundedUnder (·≤·) atTop (second θ) := by
    have hb : ∀ᶠn in atTop,second θ n≤1+(Real.sqrt (Q θ))⁻¹ :=
      Eventually.of_forall fun n => distanceRoot_le (hDim n)
        (projected_memLp (Q:=Q θ) (hDim n) (hMLp θ n)) (normalized_memLp (Q:=Q θ) (hMLp θ n))
        (C:=1) (D:=(Real.sqrt (Q θ))⁻¹) (by norm_num) (by positivity)
        (by simpa only [one_mul] using projected_bound (Q θ) (M θ n))
        (normalized_bound (hQ θ).1 (hMb θ n))
    exact isBoundedUnder_of_eventually_le hb
  have hTotalBound θ : IsBoundedUnder (·≤·) atTop
      (fun n => distanceRoot (μ θ n) (dim n) (A θ n) (normalized (Q θ) (M θ n))) := by
    have hb : ∀ᶠn in atTop,distanceRoot (μ θ n) (dim n) (A θ n) (normalized (Q θ) (M θ n))≤
        1+(Real.sqrt (Q θ))⁻¹ := Eventually.of_forall fun n =>
      distanceRoot_le (hDim n) (hALp θ n) (normalized_memLp (Q:=Q θ) (hMLp θ n))
        (C:=1) (D:=(Real.sqrt (Q θ))⁻¹) (by norm_num) (by positivity)
        (by simpa only [one_mul] using hAb θ n) (normalized_bound (hQ θ).1 (hMb θ n))
    exact isBoundedUnder_of_eventually_le hb
  have hDeficit := deficit_tendsto_of_normalized_energy hρ
    (fun θ => ⟨comparison_nonneg p (Q θ),hD θ⟩) hγ hε hκ
    (fun θ n => algorithm_energy_lower (hDim n) hp (hQ θ).1 (hQ θ).2 (hJ θ n)
      (hMLp θ n) (hALp θ n) (hMb θ n) (hAb θ n))
    hAlgBound hMeanBound hFirstBound hSecondBound hMeanEnergy hAlgorithmApprox hProjectionApprox
    hSaturation hγLimit hεLimit hκLimit
  refine ⟨hDeficit,?_⟩
  have hOrthogonal := VariableSeedOrthogonality.waiting_state_limit dim hDim μ A X Y hA hX hY
    hAb hXb hYb (fun m hm => hSpan m hm hDeficit) hCEuler hEuler
  have hDistLimit : Tendsto
      (fun θ => limsup (fun n => distanceRoot (μ θ n) (dim n) (A θ n) (normalized (Q θ) (M θ n))) atTop)
      l (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa only [zero_add] using hεLimit.add hκLimit)
    · intro θ
      exact le_limsup_of_frequently_le (Frequently.of_forall fun n => distanceRoot_nonneg _ _) (hTotalBound θ)
    · intro θ
      apply (limsup_le_iff (isCoboundedUnder_le_of_le atTop fun n => distanceRoot_nonneg _ _)
        (hTotalBound θ)).mpr
      intro z hz
      have he : 0<(z-(ε θ+κ θ))/3 := by linarith
      filter_upwards [eventually_lt_add_pos_of_limsup_le (hFirstBound θ) (hAlgorithmApprox θ) he,
        eventually_lt_add_pos_of_limsup_le (hSecondBound θ) (hProjectionApprox θ) he] with n h1 h2
      have ht := distanceRoot_triangle (hALp θ n) (projected_memLp (Q:=Q θ) (hDim n) (hMLp θ n))
        (normalized_memLp (Q:=Q θ) (hMLp θ n))
      linarith
  apply correlation_limit_from_fork (D:=1+C₀) hc hQ hPairBridge
    (fun θ n => (FiniteStateOrthogonalityBounds.overlap_square_integrable_bound (hDim n) (hA θ n) (hX θ n) (hAb θ n) (hXb θ n)).2)
    (fun θ n => ⟨distanceRoot_nonneg _ _,
      (distanceRoot_le (hDim n) (hALp θ n) (normalized_memLp (Q:=Q θ) (hMLp θ n))
        (C:=1) (D:=(Real.sqrt (Q θ))⁻¹) (by norm_num) (by positivity)
        (by simpa only [one_mul] using hAb θ n) (normalized_bound (hQ θ).1 (hMb θ n))).trans
          (by linarith [hRadius θ])⟩)
    (fun θ n => normalized_center_waiting_pairing_le (hDim n) (hALp θ n) (hMLp θ n) (hXLp θ n)
      (hAb θ n) (hXb θ n)) hOrthogonal hDistLimit

end SphericalAging.VariableSeedForkForgetting
