module

public import SphericalAging.RandomSDEIncrementEnergy
public import SphericalAging.PhysicalVariationalBounds
public import SphericalAging.ActualSphereMarkovRestart

public section

/-! Quantitative normalized increments of the actual hard-sphere SDE.
The whole-vector Itô isometry, actual waiting-time restart, physical
landscape gradient estimate, and exact spherical noise trace imply a
dimension-uniform second-moment time modulus. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.PhysicalStateIncrementMoments
open HardSphereDynamics FiniteModel GaussianLandscape LandscapeDerivatives
open PhysicalVariationalBounds AnnealedSDECore ShiftedRandomSDE ShiftedSDE
open RandomSDEIncrementEnergy
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [IsProbabilityMeasure P] {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

theorem drift_norm_onSphere (hN : 0<N) (β : ℝ≥0) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) :
    ‖hamiltonianDrift β J x‖≤(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)*Real.sqrt N := by
  have hr : 0<Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hg := (div_le_iff₀ hr).mp (Hamiltonian_gradient_sphere_bound hN J x
    ((onSphere_iff_norm_sq x).mp hx))
  have hnorm := sphere_norm x ((onSphere_iff_norm_sq x).mp hx)
  unfold hamiltonianDrift drift
  calc
    _≤‖(β : ℝ) • projection x (hamiltonianGradient J x)‖+‖kappa N • x‖ := norm_sub_le _ _
    _≤(β : ℝ)*‖hamiltonianGradient J x‖+‖x‖ := by
      rw [norm_smul,norm_smul,Real.norm_of_nonneg β.coe_nonneg]
      exact add_le_add (mul_le_mul_of_nonneg_left
        (projection_norm_le_onSphere (Nat.ne_of_gt hN) x _ hx) β.coe_nonneg)
        ((mul_le_mul_of_nonneg_right (kappa_norm_le_one hN) (norm_nonneg x)).trans_eq (one_mul _))
    _≤(β : ℝ)*((p : ℝ)*landscapeNorm N p J*Real.sqrt N)+Real.sqrt N := by
      rw [hnorm]
      exact add_le_add (mul_le_mul_of_nonneg_left hg β.coe_nonneg) le_rfl
    _=_ := by ring

theorem noise_trace_onSphere (hN : 0<N) (x : State N) (hx : OnSphere x) :
    (∑ i : Fin N,∑ j : Fin N,(noiseColumn x j i)^2)=2*((N : ℝ)-1) := by
  rw [Finset.sum_comm]
  simp_rw [coordinate_square_sum]
  change noiseQuadraticTrace x=2*((N : ℝ)-1)
  rw [noiseQuadraticTrace_eq,projectionTraceSquare_onSphere (Nat.ne_of_gt hN) x hx]

/-- A true physical solution with an arbitrary random initial state has
the same dimension-uniform waiting-time increment estimate. -/
theorem physical_increment_secondMoment (hN : 0<N) (β : ℝ≥0) (J : Disorder N p)
    (D : BrownianDriver N P F) (Z0 : Ω → State N) (X : ℝ≥0 → Ω → State N)
    (s t : ℝ≥0)
    (hX : IsRandomStrongSolutionOn D (fun _ i x => hamiltonianDrift β J x i)
      (fun _ i j x => noiseColumn x j i) Z0 X (s+t))
    (hSphere : ∀ᵐ ω ∂P,∀ r,r≤s+t → OnSphere (X r ω)) :
    (∫ ω,‖X (s+t) ω-X s ω‖^2 ∂P)/(N : ℝ)≤
      2*(t : ℝ)^2*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2+4*(t : ℝ) := by
  let Y := stateShift X s
  have hy := randomStrongSolution_timeShift D _ _
    (fun _ i => (CutoffSDE.coordinate_lipschitz i).continuous.comp
      (contDiff_hamiltonianDrift β J).continuous) Z0 X s t hX
  let B : ℝ := (1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)*Real.sqrt N
  let C : ℝ≥0 := 2*N
  have hb (r : ℝ≥0) (hr : r≤t) : AEStronglyMeasurable
      (fun ω => hamiltonianDrift β J (Y r ω)) P :=
    ((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable
      ((hy.2.1 r).mono ((ShiftedBrownian.filtration F s).le r))).aestronglyMeasurable
  have hbn (r : ℝ≥0) (hr : r≤t) : ∀ᵐ ω ∂P,‖hamiltonianDrift β J (Y r ω)‖≤B := by
    filter_upwards [hSphere] with ω hω
    exact drift_norm_onSphere hN β J _ (hω (s+r) (add_le_add le_rfl hr))
  have hn (i j : Fin N) (r : ℝ≥0) (hr : r≤t) : AEStronglyMeasurable
      (fun ω => noiseColumn (Y r ω) j i) P :=
    ((CutoffSDE.coordinate_lipschitz i).continuous.comp (contDiff_noiseColumn j).continuous).comp_aestronglyMeasurable
      (((hy.2.1 r).mono ((ShiftedBrownian.filtration F s).le r)).aestronglyMeasurable)
  have hnn (r : ℝ≥0) (hr : r≤t) : ∀ᵐ ω ∂P,
      (∑ i : Fin N,∑ j : Fin N,(noiseColumn (Y r ω) j i)^2)≤(C : ℝ) := by
    filter_upwards [hSphere] with ω hω
    change (∑ i : Fin N,∑ j : Fin N,(noiseColumn (X (s+r) ω) j i)^2)≤(C : ℝ)
    rw [noise_trace_onSphere hN _ (hω (s+r) (add_le_add le_rfl hr))]
    simp only [C,NNReal.coe_mul,NNReal.coe_ofNat,NNReal.coe_natCast]
    linarith
  have he := randomStrongSolution_increment_bound (ShiftedBrownian.driver D s)
    (fun _ x => hamiltonianDrift β J x) (fun _ i j x => noiseColumn x j i)
    (X s) Y t hy (fun _ => B) (memLp_const B) C hb hbn hn hnn t le_rfl
  simp only [integral_const,probReal_univ,one_smul,Y,stateShift,C,NNReal.coe_mul,
    NNReal.coe_ofNat,NNReal.coe_natCast] at he
  have hBe : B^2=(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2*(N : ℝ) := by
    dsimp only [B]
    rw [mul_pow,Real.sq_sqrt (Nat.cast_nonneg N)]
  rw [hBe] at he
  apply (div_le_iff₀ (Nat.cast_pos.mpr hN)).mpr
  convert he using 1 <;> ring

/-- The measurable canonical actual flow satisfies the estimate without
an SDE, sphere-support, or increment-energy premise. -/
theorem jointProcess_increment_secondMoment (hN : 0<N) (D0 : BrownianDriver N P F)
    (β : ℝ≥0) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (J : Disorder N p) (x : State N) (hx : OnSphere x) (s t : ℝ≥0) :
    (∫ ω,‖ActualSphereTransition.jointProcess (NullAugmentation.driver D0) β R hR (J,x) (s+t) ω-
      ActualSphereTransition.jointProcess (NullAugmentation.driver D0) β R hR (J,x) s ω‖^2 ∂P)/(N : ℝ)≤
      2*(t : ℝ)^2*(1+(β : ℝ)*(p : ℝ)*landscapeNorm N p J)^2+4*(t : ℝ) := by
  exact physical_increment_secondMoment hN β J (NullAugmentation.driver D0) (fun _ => x) _ s t
    (ActualSphereMarkovRestart.jointProcess_physical (Nat.ne_of_gt hN) D0 β R hR hNR J x hx (s+t))
    ((ActualSphereTransition.jointProcess_onSphere (Nat.ne_of_gt hN) D0 β R hR hNR J x hx).mono
      (fun _ h r _ => h r))

end SphericalAging.PhysicalStateIncrementMoments
