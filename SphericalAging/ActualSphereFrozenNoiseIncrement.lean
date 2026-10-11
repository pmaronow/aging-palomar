module

public import SphericalAging.ActualSphereOneStepEulerError
public import SphericalAging.ActualSphereLinearTransition
public import SphericalAging.BrownianVectorMoments

public section

/-! Genuine physical first-step noise approximation with an O(h²)
mean-square remainder, uniformly on the initial sphere. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.ActualSphereFrozenNoiseIncrement
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereLinearTransition
open SphereEulerPredictable SphereEulerInterpolationAlgebra SphereEulerCoefficients
open SphereEulerPhysicalComparison HamiltonianPicardDependence GlobalHamiltonianParameter
open ActualSphereOneStepEulerError
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def frozenNoise (h : ℝ≥0) (x : State N) (ω : VectorBrownian.Space N) : State N :=
  Real.sqrt 2 • projection x (increment (NullAugmentation.driver (VectorBrownian.driver N)) h 0 ω)

theorem oneStep_node (β h : ℝ≥0) (J : Disorder N p) (x : State N) (hx : OnSphere x)
    (ω : VectorBrownian.Space N) :
    node (NullAugmentation.driver (VectorBrownian.driver N)) β h J x 1 ω=
      x+(h : ℝ) • hamiltonianDrift β J x+frozenNoise h x ω := by
  rw [show (1 : ℕ)=0+1 from rfl,node_succ]
  simp only [node,SphereEulerQuerySpan.state,fullBlock,SphereEulerCoefficients.drift,clip_eq_onSphere x hx,frozenNoise]
  abel

@[expose] def frozenErrorCeiling (β : ℝ≥0) (J : Disorder N p) (S : ℝ≥0) : ℝ :=
  2*oneStepCeiling β J S+2*(driftCap β J : ℝ)^2

theorem actual_frozenNoise_error (hN : 0<N) (hp : 2≤p) (β S h : ℝ≥0) (hhS : h≤S)
    (J : Disorder N p) (R : ℝ≥0) (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2)
    (x : State N) (hx : OnSphere x) :
    (∫ ω,‖jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x) h ω-
      x-frozenNoise h x ω‖^2 ∂VectorBrownian.law N)≤frozenErrorCeiling β J S*(h : ℝ)^2 := by
  let D := NullAugmentation.driver (VectorBrownian.driver N)
  let P := VectorBrownian.law N
  let A := fun ω => jointProcess D β R hR (J,x) h ω-node D β h J x 1 ω
  let b := (h : ℝ) • hamiltonianDrift β J x
  let hb := drift_family_lipschitz (β : ℝ) R hR (‖J‖₊+1) ⟨J,by simp⟩
  let hs := noise_family_lipschitz N R hR
  have hg : grid h 1=h := by simp only [grid,Nat.cast_one,mul_one]
  have hAe : A=ᵐ[P] fun ω => hardProcess (VectorBrownian.driver N) β h J R hR hb hs x 1 h ω-
      interpolant D β h J x 1 h ω := by
    filter_upwards [jointProcess_ae D β R hR (J,x),
      GlobalSDE.process_eq_horizon D hb hs x (grid h 1)] with ω hj hh
    dsimp only [A]
    have hactual : jointProcess D β R hR (J,x) h ω=
        hardProcess (VectorBrownian.driver N) β h J R hR hb hs x 1 h ω :=
      (hj h).trans (hh h (by rw [hg]))
    rw [hactual]
    have hn := (interpolant_grid D β h J x (by rfl : 1≤1) ω).symm
    rw [hg] at hn
    rw [hn]
  have hA : MemLp A 2 P :=
    (Lp.memLp (differenceClass hN (VectorBrownian.driver N) β h J R hR hb hs x 1 h)).ae_eq
      ((differenceClass_ae hN (VectorBrownian.driver N) β h J R hR hb hs x 1 h).trans hAe.symm)
  have hL : Integrable (fun ω => ‖A ω+b‖^2) P := (hA.add (memLp_const b)).integrable_norm_pow'
  have hU : Integrable (fun ω => 2*‖A ω‖^2+2*‖b‖^2) P :=
    (hA.integrable_norm_pow'.const_mul 2).add (integrable_const _)
  have hpw (ω : VectorBrownian.Space N) : ‖A ω+b‖^2≤2*‖A ω‖^2+2*‖b‖^2 := by
    have hh := norm_add_le (A ω) b
    nlinarith [norm_nonneg (A ω+b),norm_nonneg (A ω),norm_nonneg b,sq_nonneg (‖A ω‖-‖b‖)]
  have he : (fun ω => jointProcess D β R hR (J,x) h ω-x-frozenNoise h x ω)=fun ω => A ω+b := by
    funext ω
    dsimp only [A,b]
    rw [oneStep_node β h J x hx]
    abel
  change (∫ ω,‖jointProcess D β R hR (J,x) h ω-x-frozenNoise h x ω‖^2 ∂P)≤_
  have hei : (∫ ω,‖jointProcess D β R hR (J,x) h ω-x-frozenNoise h x ω‖^2 ∂P)=
      ∫ ω,‖A ω+b‖^2 ∂P := integral_congr_ae (.of_forall (fun ω => congrArg (fun z : State N => ‖z‖^2) (congrFun he ω)))
  rw [hei]
  have hi := integral_mono hL hU hpw
  rw [integral_add (hA.integrable_norm_pow'.const_mul 2) (integrable_const _),integral_const_mul,integral_const] at hi
  have hbnd : ‖b‖^2≤(h : ℝ)^2*(driftCap β J : ℝ)^2 := by
    dsimp only [b]
    rw [norm_smul,Real.norm_of_nonneg h.coe_nonneg,mul_pow]
    gcongr
    change ‖hamiltonianDrift β J x‖≤(2+3*(β : ℝ)*(p : ℝ)*2^(p-1)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N
    simpa only [SphereEulerCoefficients.drift,clip_eq_onSphere x hx] using drift_norm_bound hN β.coe_nonneg J x
  have hea := actual_oneStep_euler_error hN hp (VectorBrownian.driver N) β S h hhS J R hR hNR x hx
  change (∫ ω,‖A ω‖^2 ∂P)≤oneStepCeiling β J S*(h : ℝ)^2 at hea
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hi
  unfold frozenErrorCeiling
  nlinarith only [hi,hbnd,hea]

end SphericalAging.ActualSphereFrozenNoiseIncrement
