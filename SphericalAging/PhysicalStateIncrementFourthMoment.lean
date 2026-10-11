module

public import SphericalAging.BoundedIncrementFourthMoment
public import SphericalAging.PhysicalStateIncrementMoments

public section

/-! Genuine fourth time increments of the hard-sphere dynamics, with
quadratic time scaling and no coordinate dimension loss. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalStateIncrementFourthMoment
open HardSphereDynamics FiniteModel GaussianLandscape AnnealedSDECore LandscapeDerivatives
open PhysicalStateIncrementMoments BoundedIncrementFourthMoment ShiftedRandomSDE ShiftedSDE
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def fourthIncrementCeiling (β : ℝ≥0) (J : Disorder N p) (t : ℝ≥0) : ℝ :=
  (8*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)+12)*
    (2*(t : ℝ)^3*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2+4*(t : ℝ)^2)

theorem physical_increment_fourthMoment (hN : 0<N) (β : ℝ≥0) (J : Disorder N p)
    (D : BrownianDriver N P F) (Z0 : Ω→State N) (X : ℝ≥0→Ω→State N) (s t : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D (fun _ i x => hamiltonianDrift β J x i)
      (fun _ i j x => noiseColumn x j i) Z0 X (s+t))
    (hSphere : ∀ᵐ omega ∂P,∀ r,r≤s+t → OnSphere (X r omega))
    (hnull : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[F 0] A) :
    MemLp (fun omega => X (s+t) omega-X s omega) 4 P ∧
      (∫ omega,‖X (s+t) omega-X s omega‖^4 ∂P)/(N : ℝ)^2≤fourthIncrementCeiling β J t := by
  let Y := stateShift X s
  have hy := randomStrongSolution_timeShift D _ _
    (fun _ i => (CutoffSDE.coordinate_lipschitz i).continuous.comp
      (contDiff_hamiltonianDrift β J).continuous) Z0 X s t hX
  let rN : ℝ≥0 := ⟨Real.sqrt N,Real.sqrt_nonneg _⟩
  let A : ℝ≥0 := ⟨1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J,by
    have := landscapeNorm_nonnegative N p J;positivity⟩
  let B : ℝ≥0 := A*rN
  let C : ℝ≥0 := 2*N
  have hc : ∀ᵐ omega ∂P,∀ r,r≤t → ‖Y r omega-X s omega‖≤(2*rN : ℝ≥0) := by
    filter_upwards [hSphere] with omega hsp
    intro r hr
    have hxr := sphere_norm (X (s+r) omega) ((onSphere_iff_norm_sq _).mp (hsp (s+r) (add_le_add le_rfl hr)))
    have hxs := sphere_norm (X s omega) ((onSphere_iff_norm_sq _).mp (hsp s (le_add_right le_rfl)))
    change ‖X (s+r) omega-X s omega‖≤(2*rN : ℝ≥0)
    exact (norm_sub_le _ _).trans_eq (by rw [hxr,hxs];change Real.sqrt N+Real.sqrt N=2*Real.sqrt N;ring)
  have hbn : ∀ᵐ omega ∂P,∀ r,r≤t → ‖hamiltonianDrift β J (Y r omega)‖≤B := by
    filter_upwards [hSphere] with omega hsp
    intro r hr
    exact drift_norm_onSphere hN β J _ (hsp (s+r) (add_le_add le_rfl hr))
  have htr : ∀ᵐ omega ∂P,∀ r,r≤t → (∑ i : Fin N,∑ j : Fin N,(noiseColumn (Y r omega) j i)^2)≤C := by
    filter_upwards [hSphere] with omega hsp
    intro r hr
    change (∑ i : Fin N,∑ j : Fin N,(noiseColumn (X (s+r) omega) j i)^2)≤C
    rw [noise_trace_onSphere hN _ (hsp (s+r) (add_le_add le_rfl hr))]
    simp only [C,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast]
    linarith
  have hrow : ∀ᵐ omega ∂P,∀ r,r≤t → ∀ i j,‖noiseColumn (Y r omega) j i‖≤(2 : ℝ≥0) := by
    filter_upwards [hSphere] with omega hsp
    intro r hr i j
    have hh := noiseCoordinate_norm_le_onSphere (Nat.ne_of_gt hN) _
      (hsp (s+r) (add_le_add le_rfl hr)) i j
    exact hh.trans (by norm_num)
  have hn : ∀ A : Set Ω,MeasurableSet A → P A=0 → MeasurableSet[(ShiftedBrownian.filtration F s) 0] A := by
    intro A hm hz
    change MeasurableSet[F (s+0)] A
    rw [add_zero]
    exact F.mono (zero_le : (0 : ℝ≥0)≤s) A (hnull A hm hz)
  have he := bounded_increment_fourthMoment (ShiftedBrownian.driver D s)
    (hamiltonianDrift β J) (fun i j x => noiseColumn x j i)
    (contDiff_hamiltonianDrift β J).continuous continuous_noiseCoordinate
    (X s) Y t hy (2*rN) B C 2 hc hbn htr hrow hn
  refine ⟨he.1,?_⟩
  have hRB : 4*((2*rN : ℝ≥0) : ℝ)*B+6*C=(N : ℝ)*(8*(A : ℝ)+12) := by
    change 4*(2*Real.sqrt N)*((A : ℝ)*Real.sqrt N)+6*(2*(N : ℝ))=(N : ℝ)*(8*(A : ℝ)+12)
    ring_nf
    rw [Real.sq_sqrt (Nat.cast_nonneg N)]
    ring
  have hB2 : (B : ℝ)^2=(A : ℝ)^2*(N : ℝ) := by
    change ((A : ℝ)*Real.sqrt N)^2=(A : ℝ)^2*(N : ℝ)
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [hRB,hB2] at he
  have hh := he.2
  change (∫ omega,‖X (s+t) omega-X s omega‖^4 ∂P)≤
    (N : ℝ)*(8*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)+12)*(t : ℝ)*
      (2*(t : ℝ)^2*((1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2*(N : ℝ))+2*(t : ℝ)*(2*(N : ℝ))) at hh
  apply (div_le_iff₀ (by positivity : (0 : ℝ)<(N : ℝ)^2)).mpr
  convert hh using 1 <;> unfold fourthIncrementCeiling <;> ring

theorem jointProcess_increment_fourthMoment (hN : 0<N) (D0 : BrownianDriver N P F)
    (β R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (s t : ℝ≥0) :
    MemLp (fun omega => ActualSphereTransition.jointProcess (NullAugmentation.driver D0) β R hR (J,x) (s+t) omega-
      ActualSphereTransition.jointProcess (NullAugmentation.driver D0) β R hR (J,x) s omega) 4 P ∧
    (∫ omega,‖ActualSphereTransition.jointProcess (NullAugmentation.driver D0) β R hR (J,x) (s+t) omega-
      ActualSphereTransition.jointProcess (NullAugmentation.driver D0) β R hR (J,x) s omega‖^4 ∂P)/(N : ℝ)^2≤
      fourthIncrementCeiling β J t := by
  exact physical_increment_fourthMoment hN β J (NullAugmentation.driver D0) (fun _ => x) _ s t
    (ActualSphereMarkovRestart.jointProcess_physical (Nat.ne_of_gt hN) D0 β R hR hNR J x hx (s+t))
    ((ActualSphereTransition.jointProcess_onSphere (Nat.ne_of_gt hN) D0 β R hR hNR J x hx).mono
      (fun _ ho r _ => ho r))
    (fun A hm hz => NullAugmentation.augment_null_known_zero F hm hz)

end SphericalAging.PhysicalStateIncrementFourthMoment
