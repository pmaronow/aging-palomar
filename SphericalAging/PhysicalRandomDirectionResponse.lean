module

public import SphericalAging.RandomLinearTerminalOperations
public import SphericalAging.ResponseMatrixEnergyContraction
public import SphericalAging.HamiltonianParameter

public section

/-! The actual two-time sample matrix propagates genuinely random bounded
F_s directions. This is derived from actual random-initial SDE linearity,
including correlated initial coordinates and the tangent projection. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.PhysicalRandomDirectionResponse
open HardSphereDynamics LocalSDE TwoTimePhysicalResponse PredictableLinearCoefficient
open RandomLinearVariationalSDE RandomLinearTerminalOperations ResponseMatrixEnergyContraction
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ}

lemma randomProjected_measurable (Y V : Ω → State N)
    {G : MeasurableSpace Ω} (hY : StronglyMeasurable[G] Y) (hV : StronglyMeasurable[G] V) :
    StronglyMeasurable[G] (fun omega => projection (Y omega) (V omega)) := by
  convert hV.sub (((hY.inner (𝕜 := ℝ) hV).mul_const (N : ℝ)⁻¹).smul hY) using 1
  funext omega
  simp only [projection,div_eq_mul_inv,Pi.sub_apply,Pi.smul_apply]
  rfl

lemma randomProjected_memLp (hN : N≠0) (Y V : Ω → State N)
    {G : MeasurableSpace Ω} (hG : G≤mΩ)
    (hY : StronglyMeasurable[G] Y) (hV : StronglyMeasurable[G] V)
    (hSphere : ∀ᵐ omega ∂P,OnSphere (Y omega)) (K : ℝ≥0) (hK : ∀ omega,‖V omega‖≤K) :
    MemLp (fun omega => projection (Y omega) (V omega)) 2 P := by
  apply (memLp_const (K : ℝ) : MemLp (fun _ : Ω => (K : ℝ)) 2 P).mono'
    (((randomProjected_measurable Y V hY hV).mono hG).aestronglyMeasurable)
  filter_upwards [hSphere] with omega hSphere
  simpa only [Real.norm_eq_abs,abs_of_nonneg K.coe_nonneg] using
    (projection_norm_le_onSphere hN _ _ hSphere).trans (hK omega)

@[expose] def boundedDirection (V : Ω → State N) (K : ℝ≥0) (omega : Ω) : State N :=
  if ‖V omega‖≤K then V omega else 0

lemma boundedDirection_measurable (V : Ω → State N) {G : MeasurableSpace Ω}
    (hV : StronglyMeasurable[G] V) (K : ℝ≥0) : StronglyMeasurable[G] (boundedDirection V K) :=
  StronglyMeasurable.piecewise (measurableSet_le hV.measurable.norm measurable_const) hV stronglyMeasurable_const

lemma boundedDirection_bound (V : Ω → State N) (K : ℝ≥0) : ∀ omega,‖boundedDirection V K omega‖≤K := by
  intro omega
  by_cases h : ‖V omega‖≤K
  · simpa only [boundedDirection,h,ite_true] using h
  · simp only [boundedDirection,h,ite_false,norm_zero]
    exact K.coe_nonneg

lemma boundedDirection_ae (V : Ω → State N) (K : ℝ≥0) (hK : ∀ᵐ omega ∂P,‖V omega‖≤K) :
    boundedDirection V K=ᵐ[P] V := hK.mono (fun _ h => if_pos h)

lemma randomProjected_ae_memLp (hN : N≠0) (Y V : Ω → State N)
    {G : MeasurableSpace Ω} (hG : G≤mΩ)
    (hY : StronglyMeasurable[G] Y) (hV : StronglyMeasurable[G] V)
    (hSphere : ∀ᵐ omega ∂P,OnSphere (Y omega)) (K : ℝ≥0) (hK : ∀ᵐ omega ∂P,‖V omega‖≤K) :
    MemLp (fun omega => projection (Y omega) (V omega)) 2 P := by
  apply (memLp_const (K : ℝ) : MemLp (fun _ : Ω => (K : ℝ)) 2 P).mono'
    (((randomProjected_measurable Y V hY hV).mono hG).aestronglyMeasurable)
  filter_upwards [hSphere,hK] with omega hSphere hK
  simpa only [Real.norm_eq_abs,abs_of_nonneg K.coe_nonneg] using
    (projection_norm_le_onSphere hN _ _ hSphere).trans hK

section Physical
variable (hN : N≠0) (D : BrownianDriver N P F)
  (X : ℝ≥0 → Ω → State N) (hXa : StronglyAdapted F X)
  (hXc : ∀ᵐ omega ∂P,Continuous (fun t => X t omega))
  (β : ℝ) (J : FiniteModel.Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ))
  {Kb Ks : ℝ≥0}
  (hb : ∀ i,LipschitzWith Kb (CutoffSDE.cutoffDrift β J R hR i))
  (hs : ∀ i j,LipschitzWith Ks (CutoffSDE.cutoffNoise N R hR i j)) (s T : ℝ≥0)
  (hSphere : ∀ᵐ omega ∂P,OnSphere (X s omega))

/-- Genuine random-direction two-time propagation, including P_{X_s}. -/
@[expose] def randomTerminal (V : Ω → State N) (hV : StronglyMeasurable[F s] V)
    (K : ℝ≥0) (hK : ∀ omega,‖V omega‖≤K) (t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass (ShiftedBrownian.driver D s) (driftRows X hXa hXc β J R hR hb s T)
    (noiseRows X hXa hXc R hR hs s T) (fun omega => projection (X s omega) (V omega))
    (by rw [ShiftedBrownian.filtration_zero];exact randomProjected_measurable _ _ (hXa s) hV)
    (randomProjected_memLp hN (X s) V (F.le s) (hXa s) hV hSphere K hK) T t

/-- An actual bounded correlated F_s direction is propagated by the
finite sample matrix of the true projected response columns. -/
theorem randomTerminal_eq_sampleMatrix (V : Ω → State N) (hV : StronglyMeasurable[F s] V)
    (K : ℝ≥0) (hK : ∀ omega,‖V omega‖≤K) (t : ℝ≥0) (ht : t≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F s] A) :
    randomTerminal hN D X hXa hXc β J R hR hb hs s T hSphere V hV K hK t =ᵐ[P]
      (fun omega => sampleMatrix
        (TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t) omega (V omega)) := by
  let Z0 := fun omega => projection (X s omega) (V omega)
  let hZ0 : StronglyMeasurable[ShiftedBrownian.filtration F s 0] Z0 := by
    rw [ShiftedBrownian.filtration_zero]
    exact randomProjected_measurable _ _ (hXa s) hV
  let hmZ0 := randomProjected_memLp hN (X s) V (F.le s) (hXa s) hV hSphere K hK
  let Z := fun i omega => projection (X s omega) (basisVector i)
  let hZ := fun i => projectedInitial_stronglyMeasurable hXa s (basisVector i)
  let hmZ := fun i => projectedInitial_memLp hN hXa s (basisVector i) hSphere
  let C := fun i omega => V omega i
  have hC (i : Fin N) : StronglyMeasurable[ShiftedBrownian.filtration F s 0] (C i) := by
    rw [ShiftedBrownian.filtration_zero]
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin N => ℝ) i).continuous.comp_stronglyMeasurable hV
  have hCbound (i : Fin N) (omega : Ω) : ‖C i omega‖≤K :=
    (PiLp.norm_apply_le (V omega) i).trans (hK omega)
  have hdecomp : Z0=ᵐ[P] (fun omega => ∑ i,C i omega • Z i omega) := by
    filter_upwards [] with omega
    change projection (X s omega) (V omega)=∑ i,V omega i • projection (X s omega) (basisVector i)
    conv_lhs => rw [← state_sum_basis (V omega)]
    rw [HamiltonianParameter.projection_sum]
    simp only [projection_smul]
  have hn : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[ShiftedBrownian.filtration F s 0] A := by
    intro A hA hp
    rw [ShiftedBrownian.filtration_zero]
    exact hnull A hA hp
  have he := terminalClass_bounded_sum (ShiftedBrownian.driver D s)
    (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
    Z0 hZ0 hmZ0 Z hZ hmZ C hC K hCbound hdecomp T t ht hn
  have hcolumns (i : Fin N) : terminalClass (ShiftedBrownian.driver D s)
      (driftRows X hXa hXc β J R hR hb s T) (noiseRows X hXa hXc R hR hs s T)
      (Z i) (hZ i) (hmZ i) T t=
      TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t (basisVector i) :=
    (TwoTimeResponseMatrix.terminalResponse_eq_terminalClass hN D X hXa hXc β J R hR hb hs s T hSphere t (basisVector i)).symm
  filter_upwards [he] with omega he
  rw [sampleMatrix_apply]
  exact he.trans (Finset.sum_congr rfl (fun i _ => congrArg (fun z : Lp (State N) 2 P => C i omega • z omega) (hcolumns i)))

/-- Actual random-direction response requiring only a genuine AE bound. -/
@[expose] def randomTerminalAE (V : Ω → State N) (hV : StronglyMeasurable[F s] V)
    (K : ℝ≥0) (hK : ∀ᵐ omega ∂P,‖V omega‖≤K) (t : ℝ≥0) : Lp (State N) 2 P :=
  terminalClass (ShiftedBrownian.driver D s) (driftRows X hXa hXc β J R hR hb s T)
    (noiseRows X hXa hXc R hR hs s T) (fun omega => projection (X s omega) (V omega))
    (by rw [ShiftedBrownian.filtration_zero];exact randomProjected_measurable _ _ (hXa s) hV)
    (randomProjected_ae_memLp hN (X s) V (F.le s) (hXa s) hV hSphere K hK) T t

/-- The finite actual sample response also propagates directions bounded
only almost surely, without changing their physical initial values. -/
theorem randomTerminalAE_eq_sampleMatrix (V : Ω → State N) (hV : StronglyMeasurable[F s] V)
    (K : ℝ≥0) (hK : ∀ᵐ omega ∂P,‖V omega‖≤K) (t : ℝ≥0) (ht : t≤T)
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F s] A) :
    randomTerminalAE hN D X hXa hXc β J R hR hb hs s T hSphere V hV K hK t =ᵐ[P]
      (fun omega => sampleMatrix
        (TwoTimeResponseMatrix.terminalResponse hN D X hXa hXc β J R hR hb hs s T hSphere t) omega (V omega)) := by
  let W := boundedDirection V K
  let hW := boundedDirection_measurable V hV K
  let hWb := boundedDirection_bound V K
  have he : (fun omega => projection (X s omega) (V omega))=ᵐ[P]
      (fun omega => projection (X s omega) (W omega)) :=
    (boundedDirection_ae V K hK).mono (fun _ h => congrArg (projection _) h.symm)
  have htclass : randomTerminalAE hN D X hXa hXc β J R hR hb hs s T hSphere V hV K hK t=
      randomTerminal hN D X hXa hXc β J R hR hb hs s T hSphere W hW K hWb t :=
    terminalClass_initial_congr _ _ _ _ _ _ _ _ _ he T t
  rw [htclass]
  have hsamp := randomTerminal_eq_sampleMatrix hN D X hXa hXc β J R hR hb hs s T hSphere W hW K hWb t ht hnull
  filter_upwards [hsamp,boundedDirection_ae V K hK] with omega hsamp he
  exact hsamp.trans (congrArg _ he)

end Physical
end SphericalAging.PhysicalRandomDirectionResponse
