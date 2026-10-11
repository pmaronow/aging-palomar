module

public import SphericalAging.PhysicalResponseTerminalIncrement
public import SphericalAging.SphereProjectionIncrement

public section

/-! Actual intermediate response minus the later tangent projection.
The estimate combines a true short-time response increment with the
inverse-dimension projection increment; neither is assumed as a bound. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalResponseInitialDifference
open HardSphereDynamics LocalSDE TwoTimePhysicalResponse TwoTimeResponseMatrix
  TwoTimeResponseHorizon PhysicalResponseTerminalIncrement SphereProjectionIncrement
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}

lemma norm_sub_sq_le_two (a b c : State N) :
    ‖a-c‖^2≤2*‖a-b‖^2+2*‖b-c‖^2 := by
  have hh : ‖a-c‖≤‖a-b‖+‖b-c‖ := by
    calc
      _=‖(a-b)+(b-c)‖ := by congr 1;abel
      _≤_ := norm_add_le _ _
  nlinarith [norm_nonneg (a-c),norm_nonneg (a-b),norm_nonneg (b-c),sq_nonneg (‖a-b‖-‖b-c‖)]

theorem initial_difference_secondMoment (hN : 0<N) (hp : 2≤p)
    (D : BrownianDriver N P F) (β R : ℝ≥0) (hR : 0<(R:ℝ))
    (hNR : (N:ℝ)<(R:ℝ)^2) (J : FiniteModel.Disorder N p)
    (X : ℝ≥0→Ω→State N) (hXa : StronglyAdapted F X)
    (hXc : ∀ᵐ ω ∂P,Continuous (fun t => X t ω))
    {Kb Ks : ℝ≥0} (hb : ∀i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
    (hs : ∀i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j))
    (s δ u : ℝ≥0) (hSphere : ∀ᵐ ω ∂P,OnSphere (X s ω))
    (hLater : ∀ᵐ ω ∂P,OnSphere (X (s+δ) ω))
    (hSpherePath : ∀ᵐ ω ∂P,∀t,t≤s+(δ+u)→OnSphere (X t ω))
    (hnull : ∀A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (v : State N) :
    let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere
    (∫ω,‖M δ v ω-projection (X (s+δ) ω) v‖^2 ∂P)≤
      2*‖v‖^2*incrementCeiling p β J δ δ+
        (8/(N:ℝ)*‖v‖^2)*(∫ω,‖X (s+δ) ω-X s ω‖^2 ∂P) := by
  dsimp only
  let M := terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere
  let Z := fun ω => projection (X s ω) v
  let W := fun ω => projection (X (s+δ) ω) v
  have hmZ := projectedInitial_memLp (Nat.ne_of_gt hN) hXa s v hSphere
  have hmW := projectedInitial_memLp (Nat.ne_of_gt hN) hXa (s+δ) v hLater
  have hmM : MemLp (fun ω => M δ v ω) 2 P := Lp.memLp _
  have hiM : Integrable (fun ω => ‖M δ v ω-Z ω‖^2) P := (hmM.sub hmZ).integrable_norm_pow'
  have hiW : Integrable (fun ω => ‖Z ω-W ω‖^2) P := (hmZ.sub hmW).integrable_norm_pow'
  have hiOut : Integrable (fun ω => ‖M δ v ω-W ω‖^2) P := (hmM.sub hmW).integrable_norm_pow'
  have hmX : MemLp (fun ω => X (s+δ) ω-X s ω) 2 P := by
    apply MemLp.of_bound
      (((hXa (s+δ)).mono (F.le (s+δ))).sub ((hXa s).mono (F.le s))).aestronglyMeasurable
      (2*Real.sqrt (N:ℝ))
    filter_upwards [hSphere,hLater] with ω hs hl
    have hn1 := LandscapeDerivatives.sphere_norm (X s ω) ((onSphere_iff_norm_sq _).mp hs)
    have hn2 := LandscapeDerivatives.sphere_norm (X (s+δ) ω) ((onSphere_iff_norm_sq _).mp hl)
    calc
      _≤‖X (s+δ) ω‖+‖X s ω‖ := norm_sub_le _ _
      _=_ := by rw [hn1,hn2];ring
  have hiX : Integrable (fun ω => ‖X (s+δ) ω-X s ω‖^2) P := hmX.integrable_norm_pow'
  have hproj : (∫ω,‖Z ω-W ω‖^2 ∂P)≤
      (4/(N:ℝ)*‖v‖^2)*(∫ω,‖X (s+δ) ω-X s ω‖^2 ∂P) := by
    calc
      _≤∫ω,(4/(N:ℝ)*‖v‖^2)*‖X (s+δ) ω-X s ω‖^2 ∂P := by
        apply integral_mono_ae hiW (hiX.const_mul _)
        filter_upwards [hSphere,hLater] with ω hs hl
        have hh := projection_difference_norm_sq hN (X s ω) (X (s+δ) ω) v hs hl
        simpa only [Z,W,norm_sub_rev,mul_assoc,mul_left_comm,mul_comm] using hh
      _=_ := integral_const_mul _ _
  have hsmall : ∀ᵐ ω ∂P,∀t,t≤s+δ→OnSphere (X t ω) :=
    hSpherePath.mono (fun _ h t ht => h t (ht.trans (add_le_add le_rfl (le_add_right le_rfl))))
  have hinc := (terminal_direction_increment_secondMoment hN hp D β R hR hNR J X hXa hXc hb hs
    s 0 δ hSphere (by simpa only [zero_add] using hsmall) hnull v).2
  simp only [zero_add] at hinc
  have hinit : terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s δ hSphere 0 v=ᵐ[P] Z := by
    rw [terminalResponse_initial (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s δ hSphere hNR hsmall]
    exact hmZ.coeFn_toLp
  have hhor := terminalResponse_horizon_independent (Nat.ne_of_gt hN) D X hXa hXc β J R hR hNR hb hs
    s δ (δ+u) (le_add_right le_rfl) hSphere hSpherePath hnull δ le_rfl
  have hshort : (∫ω,‖M δ v ω-Z ω‖^2 ∂P)≤‖v‖^2*incrementCeiling p β J δ δ := by
    change (∫ω,‖terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s (δ+u) hSphere δ v ω-Z ω‖^2 ∂P)≤_
    rw [hhor]
    rw [integral_congr_ae (hinit.mono (fun ω h => congrArg (fun z =>
      ‖terminalResponse (Nat.ne_of_gt hN) D X hXa hXc β J R hR hb hs s δ hSphere δ v ω-z‖^2) h))] at hinc
    exact hinc
  calc
    _≤∫ω,2*‖M δ v ω-Z ω‖^2+2*‖Z ω-W ω‖^2 ∂P :=
      integral_mono hiOut ((hiM.const_mul 2).add (hiW.const_mul 2))
        (fun ω => norm_sub_sq_le_two _ _ _)
    _=2*(∫ω,‖M δ v ω-Z ω‖^2 ∂P)+2*(∫ω,‖Z ω-W ω‖^2 ∂P) := by
      rw [integral_add (hiM.const_mul 2) (hiW.const_mul 2),integral_const_mul,integral_const_mul]
    _≤2*(‖v‖^2*incrementCeiling p β J δ δ)+
        2*((4/(N:ℝ)*‖v‖^2)*(∫ω,‖X (s+δ) ω-X s ω‖^2 ∂P)) := by linarith
    _=_ := by ring

end SphericalAging.PhysicalResponseInitialDifference
