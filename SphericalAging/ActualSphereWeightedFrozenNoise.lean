module

public import SphericalAging.ActualSphereWeightedFutureIncrement
public import SphericalAging.ActualSphereFrozenNoiseMeasurability
public import SphericalAging.ActualGammaBackwardPredictor

public section

/-! Genuine Brownian-past-weighted physical frozen-noise approximation.
Its O(h²) error retains the actual correlation of waiting state and Brownian
vector and is derived from the literal future product law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereWeightedFrozenNoise
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereLinearTransition ActualSphereMarkovRestart
open BrownianVectorMoments BrownianFuturePath BrownianFutureWeightedMoment
open ActualGammaFutureInnovation ActualSphereFrozenNoiseIncrement ActualSphereFrozenNoiseMeasurability
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem weighted_future_frozenNoise (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (S r h : ℝ≥0) (hhS : h≤S)
    (Xr : VectorBrownian.Space N→State N)
    (hXr : Measurable[NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) r] Xr)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,OnSphere (Xr ω)) :
    Integrable (fun ω => (1+‖brownianVector r ω‖^2)*
      ‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,Xr ω) h (future r ω)-
        Xr ω-frozenNoise h (Xr ω) (future r ω)‖^2) (VectorBrownian.law N) ∧
    (∫ ω,(1+‖brownianVector r ω‖^2)*
      ‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,Xr ω) h (future r ω)-
        Xr ω-frozenNoise h (Xr ω) (future r ω)‖^2 ∂VectorBrownian.law N)≤
      frozenErrorCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*r) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let Z : VectorBrownian.Space N→State N×State N := fun ω => (Xr ω,brownianVector r ω)
  have hZ : Measurable[NullAugmentation.augment (VectorBrownian.filtration N) P r] Z :=
    hXr.prodMk (brownianVector_waiting_measurable r)
  have hZm : Measurable Z := hZ.mono ((NullAugmentation.augment (VectorBrownian.filtration N) P).le r) le_rfl
  let W : State N×State N→ℝ := fun z => 1+‖z.2‖^2
  let G : (State N×State N)×VectorBrownian.Space N→ℝ :=
    fun q => ‖jointProcess D β R hR (J,q.1.1) h q.2-q.1.1-frozenNoise h q.1.1 q.2‖^2
  have hW : StronglyMeasurable W := (continuous_const.add (continuous_snd.norm.pow 2)).stronglyMeasurable
  have hWi : Integrable (fun ω => W (Z ω)) P :=
    (integrable_const 1).add ((brownianVector_memLp r (q:=2) (by norm_num)).integrable_norm_pow')
  have hG : StronglyMeasurable G := by
    have hj := (jointProcess_measurable D β R hR).comp_measurable
      (show Measurable (fun q : (State N×State N)×VectorBrownian.Space N => ((J,q.1.1),(h,q.2))) from by fun_prop)
    have hn := (frozenNoise_joint_stronglyMeasurable (N:=N) h).comp_measurable
      (show Measurable (fun q : (State N×State N)×VectorBrownian.Space N => (q.1.1,q.2)) from by fun_prop)
    exact ((hj.sub ((measurable_fst.comp measurable_fst).stronglyMeasurable)).sub hn).norm.pow 2
  have hsp : ∀ᵐ z ∂P.map Z,OnSphere z.1 := by
    apply (ae_map_iff hZm.aemeasurable ?_).mpr
    exact hSphere
    unfold OnSphere
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hGi : ∀ᵐ z ∂P.map Z,Integrable (fun η => G (z,η)) P := by
    filter_upwards [hsp] with z hz
    exact (((jointProcess_memLp_two D β R hR J h z.1).sub (memLp_const z.1)).sub
      (frozenNoise_memLp_two hN h z.1 hz)).integrable_norm_pow'
  have hGb : ∀ᵐ z ∂P.map Z,(∫ η,G (z,η) ∂P)≤frozenErrorCeiling β J S*(h : ℝ)^2 := by
    filter_upwards [hsp] with z hz
    exact actual_frozenNoise_error hN hp β S h hhS J R hR hNR z.1 hz
  have hC : 0≤frozenErrorCeiling β J S*(h : ℝ)^2 := by
    unfold frozenErrorCeiling ActualSphereOneStepEulerError.oneStepCeiling
    positivity
  have hh := weighted_future_moment r Z hZ W hW hWi (.of_forall (fun z => by dsimp [W];positivity))
    G hG (fun _ _ => by dsimp [G];positivity) hGi _ hC hGb
  refine ⟨hh.1,?_⟩
  have hwint : (∫ ω,W (Z ω) ∂P)=1+(N : ℝ)*r := by
    rw [integral_add (integrable_const 1) ((brownianVector_memLp r (q:=2) (by norm_num)).integrable_norm_pow')]
    simp only [integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul]
    rw [brownianVector_secondMoment]
  rw [hwint] at hh
  exact hh.2

theorem actual_weighted_frozenNoise (hN : 0<N) (hp : 2≤p) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (S r h : ℝ≥0) (hhS : h≤S)
    {Z0 : VectorBrownian.Space N→State N} (X : ℝ≥0→VectorBrownian.Space N→State N)
    (hX : ∀ T,AnnealedSDECore.IsRandomStrongSolutionOn (NullAugmentation.driver (VectorBrownian.driver N))
      (fun _ i z => hamiltonianDrift β J z i) (fun _ i j z => noiseColumn z j i) Z0 X T)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,∀ u,OnSphere (X u ω)) :
    Integrable (fun ω => (1+‖brownianVector r ω‖^2)*
      ‖X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω)‖^2)
      (VectorBrownian.law N) ∧
    (∫ ω,(1+‖brownianVector r ω‖^2)*
      ‖X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω)‖^2
        ∂VectorBrownian.law N)≤frozenErrorCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*r) := by
  have hh := weighted_future_frozenNoise hN hp β R hR hNR J S r h hhS (X r)
    ((hX 0).2.1 r).measurable (hSphere.mono (fun _ hh => hh r))
  have he := actual_future_eq_joint (Nat.ne_of_gt hN) β R hR hNR J X hX hSphere r h
  have hn (ω : VectorBrownian.Space N) : frozenNoise h (X r ω) (future r ω)=
      Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω) := by
    unfold frozenNoise
    rw [increment_eq_brownian,ActualGammaBackwardPredictor.brownianVector_future,
      ActualGammaBackwardPredictor.brownianVector_future,add_zero,sub_self,sub_zero]
  have hv : (fun ω => (1+‖brownianVector r ω‖^2)*
      ‖X (r+h) ω-X r ω-Real.sqrt 2 • projection (X r ω) (brownianVector (r+h) ω-brownianVector r ω)‖^2)=ᵐ[VectorBrownian.law N]
      fun ω => (1+‖brownianVector r ω‖^2)*
      ‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,X r ω) h (future r ω)-
        X r ω-frozenNoise h (X r ω) (future r ω)‖^2 := by
    filter_upwards [he] with ω hω
    rw [hω,hn]
  exact ⟨hh.1.congr hv.symm,(integral_congr_ae hv).trans_le hh.2⟩

end SphericalAging.ActualSphereWeightedFrozenNoise
