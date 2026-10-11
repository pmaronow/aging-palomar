module

public import SphericalAging.FiniteForkStanding
public import SphericalAging.PhysicalForkWaitingTransfer

public section

/-! Source10.4's common physical past, retaining the disorder-dependent
waiting state. This is stronger than endpoint/Brownian-history law alone. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkStanding
open MeasureTheory ProbabilityTheory Filter FiniteModel CKSpecification
  WienerForkTransfer ForkSeedCoordinates FiniteForkMoments PhysicalForkWaitingTransfer RandomGaussianPairing
open scoped NNReal Topology

structure Forks (dim : ℕ→ℕ) (p : ℕ) (β e : ℝ) (c r : ℝ→ℝ)
    extends FiniteForkStanding.Forks dim p β e c r where
  past_law : ∀K L T n,∀s : ℝ≥0,s≤T→PhysicalPastLaw β (T+L) s (branches K L T n)

theorem mean_waiting_CK_limit {dim : ℕ→ℕ} {p K : ℕ} {β e : ℝ}
    {c r : ℝ→ℝ} {d : CKData} (F : Forks dim p β e c r)
    (hK : 0<K) (L T s : ℝ≥0) (hs : s≤T)
    (hBridge : Tendsto (fun n => expectedOverlap (dim n) p β (T+L) s) atTop
      (𝓝 (d.C (T+L) s))) :
    Tendsto (fun n => pairing (μ:=measure (dim n) p K)
      (seededMean (F.branches K L T n)) (seededWaiting β s)) atTop
        (𝓝 (d.C (T+L) s)) := by
  apply hBridge.congr'
  exact Eventually.of_forall fun n =>
    (mean_waiting_pairing hK (F.branch_law K L T n) (F.past_law K L T n s hs)).symm

end SphericalAging.PhysicalForkStanding
