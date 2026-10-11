module

public import SphericalAging.ActualResponseCompactWaitingModulus
public import SphericalAging.ActualResponseCompactTerminalModulus
public import SphericalAging.ActualResponseFutureWaitingSaturation

public section

/-! The literal actual response means form a genuinely dimension-uniform
jointly equicontinuous family on all nonnegative terminal/waiting times.
True response SDE increments control both time coordinates, and the
actual zero-lag normalization supplies the noncausal extension. -/
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal
namespace SphericalAging.ActualResponseTimeEquicontinuity
open ActualResponsePrimitiveInterchange ActualResponseFutureWaitingSaturation
open ActualResponseCompactWaitingModulus ActualResponseCompactTerminalModulus
open ResponseIncrementCompactCeiling ResponseIncrementGaussianCeiling ResponseIncrementCeilingContinuity
open AnnealedHamiltonianEnergyStein
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def responseModulus (p : ℕ) (β : ℝ≥0) (z w : ℝ≥0×ℝ≥0) : ℝ :=
  compactTerminalModulus p β (max z.1 w.1) (max z.1 w.1-z.1)+
  compactWaitingModulus p β (max z.1 w.1)
    (max (min z.2 z.1) (min w.2 w.1)-min (min z.2 z.1) (min w.2 w.1))+
  compactTerminalModulus p β (max z.1 w.1) (max z.1 w.1-w.1)

lemma responseModulus_continuous (p : ℕ) (β : ℝ≥0) (z : ℝ≥0×ℝ≥0) :
    Continuous (responseModulus p β z) := by
  unfold responseModulus compactTerminalModulus compactWaitingModulus
  have hG := annealedIncrementCeiling_joint_continuous p β
  apply Continuous.add
  · apply Continuous.add
    · exact Real.continuous_sqrt.comp (hG.comp (show Continuous (fun w : ℝ≥0×ℝ≥0 =>
        (max z.1 w.1,max z.1 w.1-z.1)) by fun_prop))
    · exact Real.continuous_sqrt.comp (continuous_const.mul (hG.comp (show Continuous
        (fun w : ℝ≥0×ℝ≥0 => (max z.1 w.1,
          max (min z.2 z.1) (min w.2 w.1)-min (min z.2 z.1) (min w.2 w.1))) by fun_prop)))
  · exact Real.continuous_sqrt.comp (hG.comp (show Continuous (fun w : ℝ≥0×ℝ≥0 =>
      (max z.1 w.1,max z.1 w.1-w.1)) by fun_prop))

lemma responseModulus_self (p : ℕ) (β : ℝ≥0) (z : ℝ≥0×ℝ≥0) :
    responseModulus p β z z=0 := by
  simp [responseModulus,compactTerminalModulus,compactWaitingModulus,annealedIncrementCeiling_zero]

theorem modelResponse_joint_difference_le (hN : 3≤N) (hp : 2≤p) (β : ℝ≥0)
    (z w : ℝ≥0×ℝ≥0) :
    |modelResponse (N:=N) (p:=p) β z.1 z.2-modelResponse (N:=N) (p:=p) β w.1 w.2|≤
      responseModulus p β z w := by
  let H := max z.1 w.1
  let s := min z.2 z.1
  let r := min w.2 w.1
  have hs : s≤z.1 := min_le_right _ _
  have hr : r≤w.1 := min_le_right _ _
  have hzH : z.1≤H := le_max_left _ _
  have hwH : w.1≤H := le_max_right _ _
  have hz := responseMeanPair_terminal_compact_ordered hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N)
    H s z.1 H hs hzH le_rfl
  have hw := responseMeanPair_terminal_compact_ordered hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N)
    H r w.1 H hr hwH le_rfl
  have hwait := responseMeanPair_waiting_compact hN hp β (N+1) (modelRadius_pos N) (modelRadius_sq N)
    H H s r (hs.trans hzH) (hr.trans hwH) le_rfl
  change |modelResponse (N:=N) (p:=p) β H s-modelResponse (N:=N) (p:=p) β z.1 s|≤_ at hz
  change |modelResponse (N:=N) (p:=p) β H r-modelResponse (N:=N) (p:=p) β w.1 r|≤_ at hw
  change |modelResponse (N:=N) (p:=p) β H s-modelResponse (N:=N) (p:=p) β H r|≤_ at hwait
  rw [modelResponse_waiting_min hN hp β z.1 z.2,modelResponse_waiting_min hN hp β w.1 w.2]
  change |modelResponse (N:=N) (p:=p) β z.1 s-modelResponse (N:=N) (p:=p) β w.1 r|≤_
  calc
    _≤|modelResponse (N:=N) (p:=p) β z.1 s-modelResponse (N:=N) (p:=p) β H s|+
        |modelResponse (N:=N) (p:=p) β H s-modelResponse (N:=N) (p:=p) β w.1 r| := abs_sub_le _ _ _
    _≤|modelResponse (N:=N) (p:=p) β z.1 s-modelResponse (N:=N) (p:=p) β H s|+
        (|modelResponse (N:=N) (p:=p) β H s-modelResponse (N:=N) (p:=p) β H r|+|modelResponse (N:=N) (p:=p) β H r-modelResponse (N:=N) (p:=p) β w.1 r|) :=
      add_le_add le_rfl (abs_sub_le _ _ _)
    _≤compactTerminalModulus p β H (H-z.1)+
        (compactWaitingModulus p β H (max s r-min s r)+compactTerminalModulus p β H (H-w.1)) := by
      rw [abs_sub_comm] at hz
      exact add_le_add hz (add_le_add hwait hw)
    _=responseModulus p β z w := by unfold responseModulus;dsimp only [H,s,r];ring

/-- Genuine family equicontinuity, with no regularity or time-modulus
premise and no thermodynamic-limit equation supplied as an input. -/
theorem actual_modelResponse_equicontinuous {A : Type*} (dim : A→ℕ) (hD : ∀ a,3≤dim a)
    (hp : 2≤p) (β : ℝ≥0) :
    Equicontinuous (fun a => Function.uncurry (modelResponse (N:=dim a) (p:=p) β)) := by
  intro z
  apply Metric.equicontinuousAt_of_continuity_modulus (responseModulus p β z)
    (by simpa only [responseModulus_self] using (responseModulus_continuous p β z).tendsto z)
  exact Filter.Eventually.of_forall (fun w a => by
    rw [Real.dist_eq]
    exact modelResponse_joint_difference_le (hD a) hp β z w)

end SphericalAging.ActualResponseTimeEquicontinuity
