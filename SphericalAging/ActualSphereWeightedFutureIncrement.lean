module

public import SphericalAging.ActualSphereInitialFourthIncrement
public import SphericalAging.ActualSphereFrozenNoiseIncrement
public import SphericalAging.BrownianFutureWeightedMoment
public import SphericalAging.ActualGammaFutureInnovation

public section

/-! Actual waiting-time weights and genuine independent future increments.
The Brownian waiting vector and physical state retain their joint law. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereWeightedFutureIncrement
open FiniteModel HardSphereDynamics ActualSphereTransition
open BrownianVectorMoments BrownianFuturePath BrownianFutureWeightedMoment
open ActualGammaFutureInnovation ActualSphereInitialFourthIncrement
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem weighted_future_fourth (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (S r h : ℝ≥0) (hhS : h≤S)
    (Xr : VectorBrownian.Space N→State N)
    (hXr : Measurable[NullAugmentation.augment (VectorBrownian.filtration N) (VectorBrownian.law N) r] Xr)
    (hSphere : ∀ᵐ ω ∂VectorBrownian.law N,OnSphere (Xr ω)) :
    Integrable (fun ω => (1+‖brownianVector r ω‖^2)*
      ‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,Xr ω) h (future r ω)-Xr ω‖^4)
      (VectorBrownian.law N) ∧
    (∫ ω,(1+‖brownianVector r ω‖^2)*
      ‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,Xr ω) h (future r ω)-Xr ω‖^4
        ∂VectorBrownian.law N)≤smallFourthCeiling β J S*(h : ℝ)^2*(1+(N : ℝ)*r) := by
  let P := VectorBrownian.law N
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let Z : VectorBrownian.Space N→State N×State N := fun ω => (Xr ω,brownianVector r ω)
  have hZ : Measurable[NullAugmentation.augment (VectorBrownian.filtration N) P r] Z :=
    hXr.prodMk (brownianVector_waiting_measurable r)
  have hZm : Measurable Z := hZ.mono ((NullAugmentation.augment (VectorBrownian.filtration N) P).le r) le_rfl
  let W : State N×State N→ℝ := fun z => 1+‖z.2‖^2
  let G : (State N×State N)×VectorBrownian.Space N→ℝ :=
    fun q => ‖jointProcess D β R hR (J,q.1.1) h q.2-q.1.1‖^4
  have hW : StronglyMeasurable W := by exact (continuous_const.add (continuous_snd.norm.pow 2)).stronglyMeasurable
  have hWi : Integrable (fun ω => W (Z ω)) P :=
    (integrable_const 1).add ((brownianVector_memLp r (q:=2) (by norm_num)).integrable_norm_pow')
  have hG : StronglyMeasurable G := by
    have hj := (jointProcess_measurable D β R hR).comp_measurable
      (show Measurable (fun q : (State N×State N)×VectorBrownian.Space N => ((J,q.1.1),(h,q.2))) from by fun_prop)
    exact (hj.sub ((measurable_fst.comp measurable_fst).stronglyMeasurable)).norm.pow 4
  have hsp : ∀ᵐ z ∂P.map Z,OnSphere z.1 := by
    apply (ae_map_iff hZm.aemeasurable ?_).mpr
    exact hSphere
    unfold OnSphere
    exact measurableSet_eq_fun (by fun_prop) measurable_const
  have hGi : ∀ᵐ z ∂P.map Z,Integrable (fun η => G (z,η)) P := by
    filter_upwards [hsp] with z hz
    exact (actual_initial_fourthMoment hN β R hR hNR J S h hhS z.1 hz).1.integrable_norm_pow'
  have hGb : ∀ᵐ z ∂P.map Z,(∫ η,G (z,η) ∂P)≤smallFourthCeiling β J S*(h : ℝ)^2 := by
    filter_upwards [hsp] with z hz
    exact (actual_initial_fourthMoment hN β R hR hNR J S h hhS z.1 hz).2
  have hC : 0≤smallFourthCeiling β J S*(h : ℝ)^2 := by
    unfold smallFourthCeiling
    have := GaussianLandscape.landscapeNorm_nonnegative N p J
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

end SphericalAging.ActualSphereWeightedFutureIncrement
