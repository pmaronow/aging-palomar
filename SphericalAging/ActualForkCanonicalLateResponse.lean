module

public import SphericalAging.ActualForkLateEnergyReplacement
public import SphericalAging.ActualResponseWindowLimit
public import SphericalAging.StationaryWeightedResponseWindow
public import SphericalAging.CurriedLimitTransfer

public section

/-! The literal canonical late response integral in the actual finite-fork
energy subtraction, and its fixed-time dimension limit from the preceding
signed response primitive bridge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualForkCanonicalLateResponse
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology FiniteModel
  HardSphereDynamics TwoTimeResponseTimeParameter ActualResponseKernel
  ActualEnergyUniformBridge ActualResponseWindowLimit WeightedPrimitiveConvergence
  AnnealedHamiltonianEnergyStein ActualForkLateEnergyReplacement ActualForkLateTraceReplacement
  StationaryWeightedResponseWindow CKSpecification ForkParameterBounds
  AnnealedTwoTimeResponseMoments ActualFiniteHorizonTraceReplacement
open scoped NNReal ENNReal
variable {N p K : ℕ}

@[expose] def canonicalLateResponse (hN : 0<N) (β T L : ℝ≥0) (c : ℝ→ℝ) : ℝ :=
  ∫s,lateDeterministicWeight p K c T L s*
    annealedResponse (p:=p) (Nat.ne_of_gt hN) β (N+1)
      (modelRadius_pos N) (modelRadius_sq N) (T+L) s ∂waitingMeasure (T+L)

theorem canonicalLateResponse_eq_window (hp : 2≤p) (β T L : ℝ≥0)
    (dim : ℕ→ℕ) (j : ℕ) (hDim : 1≤dim j) (c : ℝ→ℝ) :
    canonicalLateResponse (p:=p) (K:=K) (by omega : 0<dim j) β T L c=
      ∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),continuousForkWeight p K c L (((T+L:ℝ≥0):ℝ)-u)*
        dimensionResponseRow hp β dim j (T+L) u := by
  let f : ℝ→ℝ := fun u => if (T:ℝ)<u then
    continuousForkWeight p K c L (((T+L:ℝ≥0):ℝ)-u)*dimensionResponseRow hp β dim j (T+L) u else 0
  have he (s : WaitingTime (T+L)) : lateDeterministicWeight p K c T L s*
      annealedResponse (p:=p) (by omega : dim j≠0) β (dim j+1)
        (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) (T+L) s=f s := by
    by_cases hs : T<(s:ℝ≥0)
    · have hsr : (T:ℝ)<(s:ℝ) := hs
      have hτ : (((T+L:ℝ≥0):ℝ)-(s:ℝ))∈Icc (0:ℝ) L := by
        have hst : (s:ℝ)≤((T+L:ℝ≥0):ℝ) := s.property.2
        constructor
        · exact sub_nonneg.mpr hst
        · simp only [NNReal.coe_add];linarith
      rw [lateDeterministicWeight_eq_of_late p K c T L s hs,
        ←dimensionResponseRow_eq_actual hp β (T+L) dim j hDim s]
      dsimp only [f]
      rw [if_pos hsr,continuousForkWeight_on_window p K c L.coe_nonneg hτ]
      rfl
    · have hsr : ¬(T:ℝ)<(s:ℝ) := hs
      simp only [lateDeterministicWeight,if_neg hs,zero_mul,f,if_neg hsr]
  calc
    _ = ∫s : WaitingTime (T+L),f s ∂waitingMeasure (T+L) :=
      integral_congr_ae (.of_forall he)
    _ = ∫u in (0:ℝ)..((T+L:ℝ≥0):ℝ),f u := waiting_real_integral (T+L) f
    _ = _ := TriangleUniqueness.integral_strict_above T.coe_nonneg
      (show (T:ℝ)≤((T+L:ℝ≥0):ℝ) by simp only [NNReal.coe_add];linarith [L.coe_nonneg])

theorem canonicalLateResponse_dimension_limit (hp : 2≤p) (β T L : ℝ≥0)
    (dim : ℕ→ℕ) (hDim : ∀j,1≤dim j) (d : CKData) (h : CKEquations p β d)
    (hprimitive : ResponsePrimitiveBridge hp β dim d)
    {c r : ℝ→ℝ} {q : ℝ} (H : ProfileCenterEnergy.Profile c r q) :
    Tendsto (fun j => canonicalLateResponse (p:=p) (K:=K) (by have hd:=hDim j;omega : 0<dim j)
      β T L c) atTop (nhds (∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),
        continuousForkWeight p K c L (((T+L:ℝ≥0):ℝ)-u)*d.R (T+L) u)) := by
  let w := continuousForkWeight p K c L
  have hw : Continuous w := continuousForkWeight_continuous H p K L
  have hzero := actual_continuous_weighted_window_limit hp β dim d h hprimitive T L w hw
  have hTt : (T:ℝ)≤((T+L:ℝ≥0):ℝ) := by simp only [NNReal.coe_add];linarith [L.coe_nonneg]
  have hrows (j : ℕ) : IntervalIntegrable (fun u => dimensionResponseRow hp β dim j (T+L) u)
      volume (T:ℝ) ((T+L:ℝ≥0):ℝ) :=
    (responseRow_integrable hp β (dim j-1) (T+L).coe_nonneg).mono_set (by
      rw [uIcc_of_le (T+L).coe_nonneg,uIcc_of_le hTt]
      exact Icc_subset_Icc T.coe_nonneg le_rfl)
  have hR : IntervalIntegrable (fun u => d.R (T+L) u) volume (T:ℝ) ((T+L:ℝ≥0):ℝ) :=
    (h.response_continuous.comp (continuous_const.prodMk continuous_id).continuousOn
      (fun u hu => ⟨T.coe_nonneg.trans hu.1,hu.2⟩)).intervalIntegrable_of_Icc hTt
  have hweight : Continuous (fun u => w (((T+L:ℝ≥0):ℝ)-u)) := hw.comp (continuous_const.sub continuous_id)
  have hwa (j : ℕ) := (hrows j).continuousOn_mul hweight.continuousOn
  have hwb := hR.continuousOn_mul hweight.continuousOn
  have hid (j : ℕ) : (∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),w (((T+L:ℝ≥0):ℝ)-u)*
        (dimensionResponseRow hp β dim j (T+L) u-d.R (T+L) u))=
      (∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),w (((T+L:ℝ≥0):ℝ)-u)*dimensionResponseRow hp β dim j (T+L) u)-
        ∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),w (((T+L:ℝ≥0):ℝ)-u)*d.R (T+L) u := by
    simp_rw [mul_sub]
    exact intervalIntegral.integral_sub (hwa j) hwb
  simp_rw [hid] at hzero
  have hh := hzero.add_const (∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),w (((T+L:ℝ≥0):ℝ)-u)*d.R (T+L) u)
  simp only [sub_add_cancel,zero_add] at hh
  apply hh.congr'
  exact Eventually.of_forall fun j =>
    (canonicalLateResponse_eq_window (K:=K) hp β T L dim j (hDim j) c).symm

/-- The actual canonical integral has the prescribed dimension-first,
stationary-time-second limit. Only preceding signed primitive convergence
and the actual stationary CK cluster are used. -/
theorem canonicalLateResponse_ordered_limit (hp : 2≤p) (β : ℝ≥0)
    (dim : ℕ→ℕ) (hDim : ∀j,1≤dim j) {d : CKData} {h : CKEquations p β d}
    {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : StationaryClusterInputs.Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (hprimitive : ResponsePrimitiveBridge hp β dim d) (L : ℝ≥0) :
    Tendsto (fun z : ℕ×ℕ => canonicalLateResponse (p:=p) (K:=K)
      (by have hd:=hDim z.2;omega : 0<dim z.2) β (T z.1).toNNReal L c)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ))
      (nhds (∫τ in (0:ℝ)..L,r τ*(c τ^(p-1)-mixedOverlap c K L τ^(p-1)))) := by
  let w := continuousForkWeight p K c L
  have hw : Continuous w := continuousForkWeight_continuous H.profile p K L
  have houter := stationary_weighted_response_window H hT L.coe_nonneg w hw
  have houter' : Tendsto (fun n => ∫u in ((T n).toNNReal:ℝ)..(((T n).toNNReal+L:ℝ≥0):ℝ),
      w ((((T n).toNNReal+L:ℝ≥0):ℝ)-u)*d.R ((T n).toNNReal+L) u)
      atTop (nhds (∫τ in (0:ℝ)..L,w τ*r τ)) := by
    convert houter using 1
    funext n
    simp only [NNReal.coe_add,Real.coe_toNNReal _ (hT n)]
  have he : (∫τ in (0:ℝ)..L,w τ*r τ)=
      ∫τ in (0:ℝ)..L,r τ*(c τ^(p-1)-mixedOverlap c K L τ^(p-1)) := by
    apply intervalIntegral.integral_congr
    intro τ hτ
    rw [uIcc_of_le L.coe_nonneg] at hτ
    dsimp only [w]
    rw [continuousForkWeight_on_window p K c L.coe_nonneg hτ]
    ring
  rw [he] at houter'
  exact CurriedLimitTransfer.tendsto_curried_of_iterated_limits
    (Eventually.of_forall (fun n => canonicalLateResponse_dimension_limit (K:=K)
      hp β (T n).toNNReal L dim hDim d h hprimitive H.profile)) houter'

end SphericalAging.ActualForkCanonicalLateResponse
