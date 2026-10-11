module

public import SphericalAging.PhysicalForkOverlapLaw
public import SphericalAging.FiniteForkStanding
public import SphericalAging.FiniteForkProjectionLimits

public section

/-! Center concentration for the actual constructed physical fork.
The distinct-pair bounds are proved from actual independent-future
concentration; the diagonal terms vanish by the genuine branch law. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkCenterConcentration
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open PhysicalForkConstruction PhysicalForkOverlapLaw AnnealedHamiltonianEnergyStein
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints
open FiniteForkMoments ForkParameterBounds ForkNormalizedEnergy RandomGaussianPairing
  ForkEnergyComparison
open scoped NNReal ENNReal Topology InnerProductSpace

theorem actual_pair_error_tendsto {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (L : ℝ≥0) (b k : Fin K) (hbk : b≠k) :
    Tendsto (fun v : ℕ×ℕ =>
      ∫z : WienerForkTransfer.ForkSpace (dim v.2) p K,
        (⟪branch β ((T v.1).toNNReal+L) (T v.1).toNNReal b z,
          branch β ((T v.1).toNNReal+L) (T v.1).toNNReal k z⟫_ℝ/(dim v.2:ℝ)
            -c (2*(L:ℝ)))^2 ∂WienerForkTransfer.forkLaw (dim v.2) p K)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall (fun v => ha.trans_le (integral_nonneg (fun _ => sq_nonneg _)))
  · intro ε hε
    rw [eventually_curry_iff]
    have hh := physical_branch_ordered_uniform_L2 H hT dim hDim hTop E hLaw hbridge
      hi hn hL1 L.coe_nonneg hε K
    filter_upwards [hh] with n hnε
    filter_upwards [hnε] with j hjε
    have hL : (L:ℝ)∈Icc 0 (L:ℝ) := ⟨L.coe_nonneg,le_rfl⟩
    simpa only [Real.toNNReal_coe,←two_mul] using hjε L hL L hL b k hbk

/-- The genuine source10.4 physical center has its predicted squared
norm in the literal ordered dimension-before-stationary-time limit.
Neither a Gram error nor a center concentration conclusion is an input. -/
theorem actual_center_defect_tendsto {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun v : ℕ×ℕ =>
      ∫z : WienerForkTransfer.ForkSpace (dim v.2) p K,
        (‖WienerForkTransfer.mean
          (branch β ((T v.1).toNNReal+L) (T v.1).toNNReal) z‖^2/(dim v.2:ℝ)
          -(1/(K:ℝ)+(1-1/(K:ℝ))*c (2*(L:ℝ))))^2
            ∂WienerForkTransfer.forkLaw (dim v.2) p K)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
  apply FiniteForkCenterConcentration.actual_center_defect_tendsto
    (fun v : ℕ×ℕ => by have hd:=hDim v.2;omega) hK
    (fun v => fork_joint_law (N:=dim v.2) (p:=p) (K:=K)
      β ((T v.1).toNNReal+L) (T v.1).toNNReal)
  intro b k hbk
  exact actual_pair_error_tendsto H hT dim hDim hTop E hLaw hbridge hi hn hL1 L b k hbk

/-- A bounded nonnegative ordered error has the literal outer limit
of its inner limsup. Inner thresholds may depend on the outer parameter. -/
theorem ordered_limsup_tendsto {a : ℕ→ℕ→ℝ} {M : ℝ}
    (hn : ∀n j,0≤a n j) (hb : ∀n j,a n j≤M)
    (ht : Tendsto (fun z : ℕ×ℕ => a z.1 z.2)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0)) :
    Tendsto (fun n => limsup (a n) atTop) atTop (𝓝 0) := by
  have hlow n : 0≤limsup (a n) atTop := by
    apply le_limsup_of_le (isBoundedUnder_of_eventually_le (Eventually.of_forall (hb n)))
    intro b hb'
    obtain ⟨j,hj⟩ := hb'.exists
    exact (hn n j).trans hj
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : ∀ᶠn in atTop,∀ᶠj in atTop,a n j<ε/2 := by
    exact eventually_curry_iff.mp ((tendsto_order.mp ht).2 (ε/2) (by positivity))
  filter_upwards [he] with n hnε
  have hu := limsup_le_of_le (isCoboundedUnder_le_of_le atTop (hn n))
    (hnε.mono (fun _ h => h.le))
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hlow n)]
  linarith

/-- The exact source10.4 norm-error conclusion: dimension limsup first,
followed by the late stationary-cluster limit, for the actual branches. -/
theorem actual_normError_tendsto {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun n => FiniteForkStanding.normError (forkNorm c K L)
      (fun j => branch (N:=dim j) (p:=p) (K:=K) β
        ((T n).toNNReal+L) (T n).toNNReal)) atTop (𝓝 0) := by
  apply ordered_limsup_tendsto (M:=(1+|forkNorm c K L|)^2)
  · intro n j
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro n j
    rw [←defect_transfer]
    exact defect_bound (by have hd:=hDim j;omega) hK
      (fork_joint_law β ((T n).toNNReal+L) (T n).toNNReal) _
  · simpa only [forkNorm] using
      actual_center_defect_tendsto H hT dim hDim hTop E hLaw hbridge hi hn hL1 hK L

theorem forkNorm_pos_of_profile {c r : ℝ→ℝ} {q : ℝ}
    (H : ProfileCenterEnergy.Profile c r q) {K : ℕ} (hK : 0<K) (L : ℝ≥0) :
    0<forkNorm c K L := by
  have hKr : (0:ℝ)<K := Nat.cast_pos.mpr hK
  have hK1 : (1:ℝ)≤K := by exact_mod_cast (show 1≤K by omega)
  have hi : 1/(K:ℝ)≤1 := (div_le_one hKr).mpr hK1
  have hc := (H.bounds (2*(L:ℝ)) (by positivity)).1
  unfold forkNorm
  exact add_pos_of_pos_of_nonneg (div_pos zero_lt_one hKr)
    (mul_nonneg (sub_nonneg.mpr hi) hc)

/-- The actual ball projection of the normalized physical center differs
from that normalized center by a vanishing L² distance in the same
literal dimension-before-stationary-time filter. -/
theorem actual_projection_distance_tendsto {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun v : ℕ×ℕ => distanceRoot (measure (dim v.2) p K) (dim v.2)
      (projected (forkNorm c K L) (seededMean
        (branch β ((T v.1).toNNReal+L) (T v.1).toNNReal)))
      (normalized (forkNorm c K L) (seededMean
        (branch β ((T v.1).toNNReal+L) (T v.1).toNNReal))))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
  have hQ := forkNorm_pos_of_profile H.profile hK L
  have hd : Tendsto (fun v : ℕ×ℕ => normDefect (forkNorm c K L)
      (branch (N:=dim v.2) (p:=p) (K:=K) β ((T v.1).toNNReal+L) (T v.1).toNNReal))
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
    simp_rw [defect_transfer]
    simpa only [forkNorm] using
      actual_center_defect_tendsto H hT dim hDim hTop E hLaw hbridge hi hn hL1 hK L
  let a (v : ℕ×ℕ) := distanceRoot (measure (dim v.2) p K) (dim v.2)
    (projected (forkNorm c K L) (seededMean
      (branch β ((T v.1).toNNReal+L) (T v.1).toNNReal)))
    (normalized (forkNorm c K L) (seededMean
      (branch β ((T v.1).toNNReal+L) (T v.1).toNNReal)))
  have hbound (v : ℕ×ℕ) : a v^2≤normDefect (forkNorm c K L)
      (branch (N:=dim v.2) (p:=p) (K:=K) β ((T v.1).toNNReal+L) (T v.1).toNNReal)/
        (forkNorm c K L)^2 := by
    exact projection_second_moment_le (N:=dim v.2) (p:=p) (K:=K)
      (by have hD:=hDim v.2;omega) hK hQ
      (fork_joint_law (N:=dim v.2) (p:=p) (K:=K)
        β ((T v.1).toNNReal+L) (T v.1).toNNReal)
  have hs : Tendsto (fun v => a v^2)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) := by
    apply squeeze_zero (fun _ => sq_nonneg _) hbound
    simpa only [zero_div] using hd.div_const ((forkNorm c K L)^2)
  have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have he : (fun v => Real.sqrt (a v^2))=a := by
    funext v
    exact Real.sqrt_sq (distanceRoot_nonneg _ _)
  change Tendsto (fun v => Real.sqrt (a v^2))
    ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 (Real.sqrt 0)) at hh
  rw [he,Real.sqrt_zero] at hh
  exact hh

end SphericalAging.PhysicalForkCenterConcentration
