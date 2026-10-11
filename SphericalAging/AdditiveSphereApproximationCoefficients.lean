module

public import SphericalAging.LandscapeMetricProjection
public import SphericalAging.SphereBallMetricProjection
public import SphericalAging.AdditiveSphereNoise
public import SphericalAging.ClippedHamiltonianDriftBounds
public import SphericalAging.GlobalSDE

public section

/-! Globally Lipschitz additive-noise approximating coefficients. Both
cutoffs are genuine nonexpansive Hilbert metric projections. The state
and Euclidean coefficient bounds are independent of the dimension. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal InnerProductSpace
namespace SphericalAging.AdditiveSphereApproximationCoefficients
open FiniteModel GaussianLandscape HardSphereDynamics LandscapeMetricProjection
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def stateRate (p : ℕ) (β A : ℝ≥0) : ℝ≥0 :=
  ⟨1+(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5),by positivity⟩
@[expose] def parameterRate (p : ℕ) (β : ℝ≥0) : ℝ≥0 :=
  ⟨3*(β:ℝ)*(p:ℝ)*2^(p-1),by positivity⟩
@[expose] def normRate (p : ℕ) (β A : ℝ≥0) : ℝ≥0 :=
  ⟨2+3*(β:ℝ)*(p:ℝ)*2^(p-1)*(A:ℝ),by positivity⟩

@[expose] def drift (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) : State N :=
  hamiltonianDrift (β:ℝ) (LandscapeMetricProjection.project N p A J).ofLp
    (SphereBallMetricProjection.project (SphereBallMetricProjection.doubleRadius N) x)
@[expose] def driftCoordinate (β A : ℝ≥0) (J : CoefficientSpace N p) (i : Fin N) (x : State N) : ℝ :=
  drift β A J x i

theorem drift_state_bound (hN : 0<N) (hp : 2≤p) (β A : ℝ≥0)
    (J : CoefficientSpace N p) (x y : State N) :
    ‖drift β A J x-drift β A J y‖≤(stateRate p β A:ℝ)*‖x-y‖ := by
  have hh := ClippedHamiltonianDriftBounds.drift_state_clipped_bound hN hp β.coe_nonneg
    (LandscapeMetricProjection.project N p A J).ofLp
    (SphereBallMetricProjection.project (SphereBallMetricProjection.doubleRadius N))
    (SphereBallMetricProjection.project_lipschitz _) (SphereBallMetricProjection.project_norm_le _) x y
  have hJ := LandscapeMetricProjection.project_landscape_le hN p A J
  change ‖drift β A J x-drift β A J y‖≤_
  exact hh.trans (mul_le_mul_of_nonneg_right (by
    change 1+(β:ℝ)*(p:ℝ)*landscapeNorm N p _*2^(p-2)*(3*(p:ℝ)+5)≤_
    change 1+(β:ℝ)*(p:ℝ)*landscapeNorm N p _*2^(p-2)*(3*(p:ℝ)+5)≤
      1+(β:ℝ)*(p:ℝ)*(A:ℝ)*2^(p-2)*(3*(p:ℝ)+5)
    gcongr) (norm_nonneg _))

theorem drift_state_lipschitz (hN : 0<N) (hp : 2≤p) (β A : ℝ≥0)
    (J : CoefficientSpace N p) : LipschitzWith (stateRate p β A) (drift β A J) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [dist_eq_norm] using drift_state_bound hN hp β A J x y

theorem drift_coordinate_lipschitz (hN : 0<N) (hp : 2≤p) (β A : ℝ≥0)
    (J : CoefficientSpace N p) (i : Fin N) :
    LipschitzWith (stateRate p β A) (driftCoordinate β A J i) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simpa only [driftCoordinate,dist_eq_norm,PiLp.sub_apply] using
    (PiLp.norm_apply_le (drift β A J x-drift β A J y) i).trans
      (drift_state_bound hN hp β A J x y)

theorem drift_parameter_bound (hN : 0<N) (β A : ℝ≥0)
    (J K : CoefficientSpace N p) (x : State N) :
    ‖drift β A J x-drift β A K x‖≤(parameterRate p β:ℝ)*‖J-K‖ := by
  have hh := ClippedHamiltonianDriftBounds.drift_disorder_ball_bound hN β.coe_nonneg
    (LandscapeMetricProjection.project N p A J).ofLp
    (LandscapeMetricProjection.project N p A K).ofLp
    (SphereBallMetricProjection.project (SphereBallMetricProjection.doubleRadius N) x)
    (SphereBallMetricProjection.project_norm_le _ x)
  have hpj : ‖LandscapeMetricProjection.project N p A J-LandscapeMetricProjection.project N p A K‖≤‖J-K‖ := by
    simpa only [dist_eq_norm,NNReal.coe_one,one_mul] using
      (LandscapeMetricProjection.project_lipschitz N p A).dist_le_mul J K
  change ‖drift β A J x-drift β A K x‖≤_
  exact hh.trans (mul_le_mul_of_nonneg_left (by
    rw [←WithLp.ofLp_sub,WithLp.toLp_ofLp]
    exact hpj)
    (parameterRate p β).coe_nonneg)

theorem drift_parameter_lipschitz (hN : 0<N) (β A : ℝ≥0) (x : State N) :
    LipschitzWith (parameterRate p β) (fun J : CoefficientSpace N p => drift β A J x) := by
  apply LipschitzWith.of_dist_le_mul
  intro J K
  simpa only [dist_eq_norm] using drift_parameter_bound hN β A J K x

theorem drift_joint_continuous (hN : 0<N) (hp : 2≤p) (β A : ℝ≥0) :
    Continuous (Function.uncurry (drift (N:=N) (p:=p) β A)) :=
  (LipschitzWith.uncurry (drift_parameter_lipschitz hN β A)
    (drift_state_lipschitz hN hp β A)).continuous

theorem drift_norm_bound (hN : 0<N) (β A : ℝ≥0) (J : CoefficientSpace N p) (x : State N) :
    ‖drift β A J x‖≤(normRate p β A:ℝ)*Real.sqrt N := by
  have hh := ClippedHamiltonianDriftBounds.drift_ball_norm_bound hN β.coe_nonneg
    (LandscapeMetricProjection.project N p A J).ofLp
    (SphereBallMetricProjection.project_norm_le (SphereBallMetricProjection.doubleRadius N) x)
  have hJ := LandscapeMetricProjection.project_landscape_le hN p A J
  exact hh.trans (mul_le_mul_of_nonneg_right (by
    change 2+3*(β:ℝ)*(p:ℝ)*2^(p-1)*landscapeNorm N p _≤
      2+3*(β:ℝ)*(p:ℝ)*2^(p-1)*(A:ℝ)
    gcongr) (Real.sqrt_nonneg _))

theorem drift_eq_onSphere (hN : 0<N) (β A : ℝ≥0) (J : CoefficientSpace N p)
    (hJ : landscapeNorm N p J.ofLp≤A) (x : State N) (hx : OnSphere x) :
    drift β A J x=hamiltonianDrift (β:ℝ) J.ofLp x := by
  unfold drift
  rw [LandscapeMetricProjection.project_eq_self hN p A J hJ,
    SphereBallMetricProjection.project_doubleRadius_eq_onSphere x hx]

end SphericalAging.AdditiveSphereApproximationCoefficients
