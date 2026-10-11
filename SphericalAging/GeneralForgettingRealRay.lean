module

public import SphericalAging.IteratedForkForgetting
public import SphericalAging.RemoteResponseScalarLimits

public section

/-! The arbitrary-diverging-sequence form of fixed-wait forgetting implies
the literal real-ray limit, without a uniform outer-parameter assertion. -/
noncomputable section
namespace SphericalAging.GeneralForgettingRealRay
open Filter
open scoped Topology

theorem real_ray_forgetting_of_sequences {f : ℝ→ℝ} (hpos : ∀t,0≤f t)
    (hseq : ∀t : ℕ→ℝ,(∀n,0<t n)→Tendsto t atTop atTop→
      Tendsto (fun n => f (t n)) atTop (𝓝 0)) :
    Tendsto f atTop (𝓝 0) := by
  have h := RemoteResponseScalarLimits.real_ray_limsup_of_sequences hpos
    (B:=0) (fun t hp ht => ⟨(hseq t hp ht).isBoundedUnder_le,
      (hseq t hp ht).limsup_eq.le⟩)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun t => ha.trans_le (hpos t)
  · intro b hb
    exact (limsup_le_iff (isCoboundedUnder_le_of_le atTop hpos) h.1).mp h.2 b hb

end SphericalAging.GeneralForgettingRealRay
