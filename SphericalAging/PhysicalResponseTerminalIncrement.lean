module

public import SphericalAging.RandomLinearVariationalIncrementEnergy
public import SphericalAging.TwoTimeResponseMoments
public import SphericalAging.TwoTimeResponseHorizon

public section

/-! Genuine quantitative terminal-time increments of the physical
projected response. The complete noise trace is at most eight uniformly
in dimension, and no cutoff derivative constant enters the ceiling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalResponseTerminalIncrement
open HardSphereDynamics PhysicalVariationalMoments TwoTimePhysicalResponse
open TwoTimeResponseMatrix TwoTimeResponseMoments RandomLinearVariationalSDE
open RandomLinearVariationalIncrementEnergy
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def incrementCeiling (p : ℕ) (β : ℝ≥0) (J : FiniteModel.Disorder N p)
    (H δ : ℝ≥0) : ℝ :=
  (2*(physicalDriftBound p β J:ℝ)^2*(δ:ℝ)^2+16*(δ:ℝ))*
    Real.exp ((2*(physicalDriftBound p β J:ℝ)+9)*(H:ℝ))

theorem incrementCeiling_nonneg (p : ℕ) (β : ℝ≥0) (J : FiniteModel.Disorder N p)
    (H δ : ℝ≥0) : 0 ≤ incrementCeiling p β J H δ := by unfold incrementCeiling;positivity

theorem physicalNoiseTraceBound_le_eight (hN : 0<N) : (physicalNoiseTraceBound N:ℝ)≤8 := by
  have hn : (0:ℝ)<N := by exact_mod_cast hN
  have hn1 : (1:ℝ)≤N := by exact_mod_cast hN
  change (8:ℝ)/(N:ℝ)≤8
  apply (div_le_iff₀ hn).mpr
  nlinarith

theorem scalar_increment_ceiling_bound (K S H δ : ℝ≥0) (hS : (S:ℝ)≤8)
    (E V : ℝ) (hE : 0≤E) (hV : 0≤V) (hEV : E≤V) :
    (2*(K:ℝ)^2*(δ:ℝ)^2+2*(S:ℝ)*(δ:ℝ))*
      (E*Real.exp (((2*K+1+S:ℝ≥0):ℝ)*(H:ℝ)))≤
    V*((2*(K:ℝ)^2*(δ:ℝ)^2+16*(δ:ℝ))*Real.exp ((2*(K:ℝ)+9)*(H:ℝ))) := by
  have he : Real.exp (((2*K+1+S:ℝ≥0):ℝ)*(H:ℝ))≤Real.exp ((2*(K:ℝ)+9)*(H:ℝ)) := by
    apply Real.exp_le_exp.mpr
    simp only [NNReal.coe_add,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_one]
    exact mul_le_mul_of_nonneg_right (by linarith) H.coe_nonneg
  have hp : 2*(K:ℝ)^2*(δ:ℝ)^2+2*(S:ℝ)*(δ:ℝ)≤2*(K:ℝ)^2*(δ:ℝ)^2+16*(δ:ℝ) := by
    nlinarith [δ.coe_nonneg]
  have hb := mul_le_mul hEV he (Real.exp_nonneg _) hV
  have hh := mul_le_mul hp hb (mul_nonneg hE (Real.exp_nonneg _)) (by positivity)
  exact hh.trans_eq (by ring)

theorem terminal_direction_increment_secondMoment (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0→Ω→State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
    {Kb Ks : ℝ≥0} (hb : ∀i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s u δ : ℝ≥0) (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))
    (hSpherePath : ∀ᵐ omega ∂P,∀t,t≤s+(u+δ)→OnSphere (X t omega))
    (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (v : State N) :
    let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (u+δ) hSphere
    MemLp (fun omega => (M (u+δ) v) omega-(M u v) omega) 2 P ∧
      (∫omega,‖(M (u+δ) v) omega-(M u v) omega‖^2 ∂P)≤
        ‖v‖^2*incrementCeiling p β J (u+δ) δ := by
  dsimp only
  let Z0 := fun omega => projection (X s omega) v
  let a := TwoTimePhysicalResponse.driftRows X hXa hXc β J R hR hb s (u+δ)
  let σ := TwoTimePhysicalResponse.noiseRows X hXa hXc R hR hs s (u+δ)
  have hZ0 := projectedInitial_stronglyMeasurable hXa s v
  have hmem := projectedInitial_memLp (Nat.ne_of_gt hN) hXa s v hSphere
  have hbound : ∀ᵐ omega ∂P,‖Z0 omega‖≤‖v‖₊ := hSphere.mono (fun omega hw =>
    projection_norm_le_onSphere (Nat.ne_of_gt hN) _ v hw)
  have hc := shiftedRows_physical_bounds hN hp β R hR hNR J X hXa hXc s (u+δ) hSpherePath hb hs
  let Y := process (ShiftedBrownian.driver D s) a σ Z0 hZ0 hmem (u+δ)
  have hn : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[ShiftedBrownian.filtration F s 0] A := by
    intro A hA hzero
    rw [ShiftedBrownian.filtration_zero]
    exact (F.mono (show (0:ℝ≥0)≤s from bot_le)) _ (hnull A hA hzero)
  have hh := random_vector_increment_secondMoment u δ
    (process_strongSolution (ShiftedBrownian.driver D s) a σ Z0 hZ0 hmem (u+δ))
    hmem ‖v‖₊ hbound (physicalDriftBound p β J) (physicalNoiseTraceBound N) hc.1 hc.2 hn
  have he : (fun omega =>
      (terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (u+δ) hSphere (u+δ) v) omega-
      (terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (u+δ) hSphere u v) omega)=ᵐ[P]
      fun omega => Y (u+δ) omega-Y u omega := by
    filter_upwards [terminalResponse_ae (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (u+δ) hSphere (u+δ) v,
      terminalResponse_ae (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (u+δ) hSphere u v]
      with omega hT hU
    exact congrArg₂ (fun x y : State N => x-y) hT hU
  refine ⟨hh.1.ae_eq he.symm,?_⟩
  rw [integral_congr_ae (he.mono (fun _ hq => congrArg (fun x : State N => ‖x‖^2) hq))]
  have hz : (∫omega,‖Z0 omega‖^2 ∂P)≤‖v‖^2 := by
    have hi := integral_mono_ae hmem.integrable_norm_pow' (integrable_const (‖v‖^2))
      (hbound.mono (fun _ hw => pow_le_pow_left₀ (norm_nonneg _) hw 2))
    simpa using hi
  exact hh.2.trans (scalar_increment_ceiling_bound (physicalDriftBound p β J)
    (physicalNoiseTraceBound N) (u+δ) δ (physicalNoiseTraceBound_le_eight hN)
    _ _ (integral_nonneg (fun _ => by positivity)) (sq_nonneg ‖v‖) hz)

end SphericalAging.PhysicalResponseTerminalIncrement
