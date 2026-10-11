module

public import SphericalAging.ActualResponseDiagonalLimit

public section

/-! The canonical backward trace response is constant past its terminal
waiting time, by its literal zero-lag definition and genuine diagonal. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualResponseFutureWaitingSaturation
open ActualResponseJointKernel ActualResponsePrimitiveInterchange ActualResponseDiagonalLimit
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

 theorem responseMeanPair_future_diagonal (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (H s : ℝ≥0) (hHs : H≤s) :
    responseMeanPair (N := N) (p := p) β R hR H s=responseMeanPair (N := N) (p := p) β R hR s s := by
  unfold responseMeanPair backwardTraceField
  simp only [tsub_eq_zero_of_le hHs,tsub_self]

 theorem modelResponse_future_diagonal (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H s : ℝ≥0) (hHs : H≤s) :
    modelResponse (N := N) (p := p) β H s=((N : ℝ)-1)/(N : ℝ) := by
  rw [modelResponse,responseMeanPair_future_diagonal β (N+1)
    (AnnealedHamiltonianEnergyStein.modelRadius_pos N) H s hHs]
  exact modelResponse_diagonal hN hp β s

 theorem modelResponse_waiting_min (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (H s : ℝ≥0) :
    modelResponse (N := N) (p := p) β H s=modelResponse (N := N) (p := p) β H (min s H) := by
  rcases le_total s H with hs | hs
  · rw [min_eq_left hs]
  · rw [min_eq_right hs,modelResponse_future_diagonal hN hp β H s hs,
      modelResponse_diagonal hN hp β H]

end SphericalAging.ActualResponseFutureWaitingSaturation
