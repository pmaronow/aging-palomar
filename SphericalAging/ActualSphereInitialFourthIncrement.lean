module

public import SphericalAging.PhysicalStateIncrementFourthMoment
public import SphericalAging.ActualSphereMarkovRestart
public import SphericalAging.LinearSDELocalization

public section

/-! Genuine actual transition fourth increments, uniformly in the initial
sphere point, with a fixed-horizon O(h²) ceiling. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter StochasticCalculus
open scoped NNReal ENNReal
namespace SphericalAging.ActualSphereInitialFourthIncrement
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
open PhysicalStateIncrementFourthMoment
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def smallFourthCeiling (β : ℝ≥0) (J : Disorder N p) (S : ℝ≥0) : ℝ :=
  (N : ℝ)^2*(8*(1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)+12)*
    (2*(S : ℝ)*(1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)^2+4)

theorem actual_initial_fourthMoment (hN : 0<N) (β R : ℝ≥0) (hR : 0<(R : ℝ))
    (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p) (S h : ℝ≥0) (hhS : h≤S)
    (x : State N) (hx : OnSphere x) :
    MemLp (fun ω => jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) h ω-x)
      4 (VectorBrownian.law N) ∧
    (∫ ω,‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) h ω-x‖^4
      ∂VectorBrownian.law N)≤smallFourthCeiling β J S*(h : ℝ)^2 := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let X := jointProcess D β R hR (J,x)
  have hX := jointProcess_physical (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx h
  have hsp := jointProcess_onSphere (Nat.ne_of_gt hN) (VectorBrownian.driver N) β R hR hNR J x hx
  have hfour := physical_increment_fourthMoment hN β J D (fun _ => x) X 0 h
    (by simpa only [zero_add] using hX)
    (hsp.mono (fun _ hh r _ => hh r))
    (fun _ hm hz => NullAugmentation.augment_null_known_zero _ hm hz)
  have hzero : X 0=ᵐ[VectorBrownian.law N] fun _ => x := by
    obtain ⟨A,U,_,_,hEq⟩ := hX.2.2.2
    have hall := ae_all_iff.mpr (fun i : Fin N => hEq 0 bot_le i)
    have hi : ∀ᵐ ω ∂VectorBrownian.law N,∀ i : Fin N,(VectorIto.vectorProcessLp D (U i) 0 : VectorBrownian.Space N→ℝ) ω=0 :=
      ae_all_iff.mpr (fun i => by
        rw [LinearSDELocalization.vectorProcessLp_zero_time]
        exact Lp.coeFn_zero ℝ 2 (VectorBrownian.law N))
    filter_upwards [hall,hi] with ω hω hiω
    apply PiLp.ext
    intro i
    have he := hω i
    simp only [NNReal.coe_zero,intervalIntegral.integral_same,add_zero] at he
    change (X 0 ω) i=x i+(VectorIto.vectorProcessLp D (U i) 0 : VectorBrownian.Space N→ℝ) ω at he
    rw [hiω i,add_zero] at he
    exact he
  have he : (fun ω => X (0+h) ω-X 0 ω)=ᵐ[VectorBrownian.law N] fun ω => X h ω-x := by
    filter_upwards [hzero] with ω hω
    simp only [zero_add,hω]
  refine ⟨hfour.1.ae_eq he,?_⟩
  rw [integral_congr_ae (he.mono (fun _ hh => congrArg (fun z : State N => ‖z‖^4) hh))] at hfour
  have hb := (div_le_iff₀ (by positivity : (0 : ℝ)<(N : ℝ)^2)).mp hfour.2
  change (∫ ω,‖X h ω-x‖^4 ∂VectorBrownian.law N)≤_
  refine hb.trans ?_
  unfold smallFourthCeiling fourthIncrementCeiling
  have hhS' : (h : ℝ)≤S := by exact_mod_cast hhS
  have hA : 0≤1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J := by
    have := GaussianLandscape.landscapeNorm_nonnegative N p J
    positivity
  have htemp : 2*(h : ℝ)^3*(1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)^2+4*(h : ℝ)^2≤
      (2*(S : ℝ)*(1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)^2+4)*(h : ℝ)^2 := by
    nlinarith [mul_nonneg (sq_nonneg (h : ℝ)) (mul_nonneg (sub_nonneg.mpr hhS')
      (sq_nonneg (1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)))]
  have hb' := mul_le_mul_of_nonneg_left htemp
    (show 0≤(N : ℝ)^2*(8*(1+(β : ℝ)*(p : ℝ)*GaussianLandscape.landscapeNorm N p J)+12) by positivity)
  convert hb' using 1 <;> ring

end SphericalAging.ActualSphereInitialFourthIncrement
