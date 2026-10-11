module

public import SphericalAging.FiniteForkMoments
public import SphericalAging.AsymptoticErrorTransfer

public section

/-! Genuine finite-fork concentration controls the actual ball projection
error, with the dimension limit taken before the time limit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace SphericalAging.FiniteForkProjectionLimits
open FiniteModel ForkSeedCoordinates WienerForkTransfer FiniteForkMoments
open ForkNormalizedEnergy ForkEnergyComparison RandomGaussianPairing RandomVectorBounds
open AsymptoticErrorTransfer

theorem distance_limsup_of_second_moment
    {dim : ℕ→ℕ} (hDim : ∀n,0<dim n)
    {Ω : ℕ→Type} [∀n,MeasurableSpace (Ω n)] (μ : ∀n,Measure (Ω n))
    [∀n,IsProbabilityMeasure (μ n)] {X Y : ∀n,Ω n→Vector (dim n)}
    (hX : ∀n,MemLp (X n) 2 (μ n)) (hY : ∀n,MemLp (Y n) 2 (μ n))
    {C ε : ℝ} (hε : 0≤ε) (hBound : ∀n,distanceRoot (μ n) (dim n) (X n) (Y n)≤C)
    (hm : limsup (fun n => (∫z,‖X n z-Y n z‖^2 ∂μ n)/(dim n:ℝ)) atTop≤ε^2) :
    limsup (fun n => distanceRoot (μ n) (dim n) (X n) (Y n)) atTop≤ε := by
  let a n := distanceRoot (μ n) (dim n) (X n) (Y n)
  have hC : 0≤C := (distanceRoot_nonneg (X 0) (Y 0)).trans (hBound 0)
  have hB : IsBoundedUnder (·≤·) atTop (fun n => a n^2) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      (sq_le_sq₀ (distanceRoot_nonneg (X n) (Y n)) hC).mpr (hBound n))
  have hM : limsup (fun n => a n^2) atTop≤ε^2 := by
    simpa only [a,distanceRoot_sq (hDim _) (hX _) (hY _)] using hm
  have hh := limsup_sqrt_le hε hB (fun n => sq_nonneg (a n)) hM
  have hs : (fun n => Real.sqrt (a n^2))=a := by
    funext n
    exact Real.sqrt_sq (distanceRoot_nonneg (X n) (Y n))
  rw [hs] at hh
  exact hh

theorem projection_limsup_le {dim : ℕ→ℕ} (hDim : ∀n,0<dim n)
    {p K : ℕ} (hK : 0<K) {β : ℝ} {t T : ℝ≥0} {Q ζ : ℝ} (hQ : 0<Q)
    {Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)}
    (hY : ∀n,ForkJointLaw β t T (Y n))
    (hDefect : limsup (fun n => normDefect Q (Y n)) atTop≤ζ) :
    limsup (fun n => distanceRoot (measure (dim n) p K) (dim n)
      (projected Q (seededMean (Y n))) (normalized Q (seededMean (Y n)))) atTop≤
        Real.sqrt ζ/Q := by
  let d n := normDefect Q (Y n)
  let b n := distanceRoot (measure (dim n) p K) (dim n)
    (projected Q (seededMean (Y n))) (normalized Q (seededMean (Y n)))
  let f : ℝ→ℝ := fun x => Real.sqrt x/Q
  have hDn : ∀n,0≤d n := fun n => defect_nonneg Q (Y n)
  have hDb : IsBoundedUnder (·≤·) atTop d :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      defect_bound (hDim n) hK (hY n) Q)
  have hfb : IsBoundedUnder (·≤·) atTop (f ∘ d) :=
    isBoundedUnder_of_eventually_le (Eventually.of_forall fun n =>
      div_le_div_of_nonneg_right (Real.sqrt_le_sqrt
        (defect_bound (hDim n) hK (hY n) Q)) hQ.le)
  have hmono : Monotone f := fun _ _ h => div_le_div_of_nonneg_right (Real.sqrt_le_sqrt h) hQ.le
  have hc : Continuous f := Real.continuous_sqrt.div_const Q
  have hmap := hmono.map_limsup_of_continuousAt d hc.continuousAt hDb
    (isCoboundedUnder_le_of_le atTop hDn)
  simp only [Function.comp_def] at hmap
  have hb : ∀n,b n≤f (d n) := by
    intro n
    have he := projection_second_moment_le (hDim n) hK hQ (hY n)
    have hh := Real.le_sqrt_of_sq_le he
    dsimp only [f,d,b]
    exact hh.trans_eq (by rw [Real.sqrt_div (defect_nonneg Q (Y n)),Real.sqrt_sq hQ.le])
  have hl := limsup_le_limsup (Eventually.of_forall hb)
    (isCoboundedUnder_le_of_le atTop (fun n => distanceRoot_nonneg _ _)) hfb
  rw [←hmap] at hl
  exact hl.trans (hmono hDefect)

end SphericalAging.FiniteForkProjectionLimits
