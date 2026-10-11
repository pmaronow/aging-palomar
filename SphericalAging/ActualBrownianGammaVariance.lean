module

public import SphericalAging.ActualGammaEarlierWienerVariance

public section

/-! The full Brownian variance of the literal physical two-time Γ pairing.
The earlier predictor and later innovation are constructed from the actual
Wiener history and physical SDE, then combined by true conditional variance. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.ActualBrownianGammaVariance
open FiniteModel HardSphereDynamics ActualSphereTransition ActualSphereMarkovRestart
open ActualSphereGammaVariance ActualDisorderGammaVariance BrownianVectorMoments
open ActualGammaFutureInnovation ActualGammaBackwardPredictor ActualGammaPredictorMartingale
open ActualGammaEarlierWienerVariance ActualGammaPredictorLocalIncrement
open ConditionalPredictionVariance ActualBackgroundGammaLaw
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def brownianVarianceCeiling (β : ℝ≥0) (J : Disorder N p) (T : ℝ≥0) : ℝ :=
  4*(T : ℝ)^2*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+(3/2)*(T : ℝ)

theorem brownian_gamma_variance_le (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    variance (fun ω => jointGamma β R hR (s+u) s ((J,x),ω)) (VectorBrownian.law N)≤
      ((s : ℝ)*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u)+
        rowCeiling β J T s*(s : ℝ) := by
  let P := VectorBrownian.law N
  let X := jointProcess (NullAugmentation.driver (VectorBrownian.driver N)) β R hR (J,x)
  let A : VectorBrownian.Space N→ℝ := fun ω => ⟪brownianVector s ω,X (s+u) ω⟫_ℝ/(Real.sqrt 2*(N : ℝ))
  let M := backwardProcess β R hR J X T (s+u) s
  have hn : 0<N := by omega
  have hX (V : ℝ≥0) := jointProcess_physical (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J x hx V
  have hSphere := jointProcess_onSphere (Nat.ne_of_gt hn) (VectorBrownian.driver N) β R hR hNR J x hx
  have hst : s≤s+u := le_add_of_nonneg_right (show (0 : ℝ≥0)≤u from bot_le)
  have hA2 : MemLp A 2 P := terminalGamma_memLp_two hn β J X hX hSphere (s+u) s
  have hCE := backwardProcess_eq_condExp hn β R hR hNR J X hX hSphere T (s+u) s hsu hst s
  have hvar := innovation_variance_identity (stoppedFiltration N s |>.le s) hA2 hCE
  have hc0 : brownianClass (N:=N) 0=0 := by
    apply norm_eq_zero.mp
    apply sq_eq_zero_iff.mp
    simpa using brownianClass_norm_sq (N:=N) 0
  have hM (ω : VectorBrownian.Space N) : M s ω=
      ⟪brownianVector s ω,mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J u (X s ω)⟫_ℝ/
        (Real.sqrt 2*(N : ℝ)) := by
    simp only [M,backwardProcess,min_self,predictor,add_tsub_cancel_left,tsub_self,gammaMean,hc0,
      inner_zero_left,zero_div,add_zero]
  have hf := future_gamma_innovation_variance_le hN hp β R hR hNR J X hX hSphere s u
  have hfi : (∫ω,(A ω-M s ω)^2 ∂P)≤
      ((s : ℝ)*u/(N : ℝ))*Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u) := by
    simpa only [A,hM,sub_div] using hf
  have he := joint_earlier_predictor_variance_le hN hp β R hR hNR J x hx T (s+u) s hsu hst hT
  have hh : variance A P≤_ := hvar.symm.trans_le (add_le_add hfi he)
  simpa only [A,X,jointGamma,real_inner_comm] using hh

theorem brownian_gamma_variance_le_horizon (hN : 3≤N) (hp : 2≤p) (β R : ℝ≥0)
    (hR : 0<(R : ℝ)) (hNR : (N : ℝ)<(R : ℝ)^2) (J : Disorder N p)
    (x : State N) (hx : OnSphere x) (s u T : ℝ≥0) (hsu : s+u≤T) (hT : 0<T) :
    variance (fun ω => jointGamma β R hR (s+u) s ((J,x),ω)) (VectorBrownian.law N)≤
      brownianVarianceCeiling β J T/(N : ℝ) := by
  have hh := brownian_gamma_variance_le hN hp β R hR hNR J x hx s u T hsu hT
  refine hh.trans ?_
  have hs : s≤T := (le_add_of_nonneg_right (show (0 : ℝ≥0)≤u from bot_le)).trans hsu
  have hu : u≤T := (le_add_of_nonneg_left (show (0 : ℝ≥0)≤s from bot_le)).trans hsu
  have hs' : (s : ℝ)≤T := by exact_mod_cast hs
  have hu' : (u : ℝ)≤T := by exact_mod_cast hu
  have hc : 0≤2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J := by
    have := GaussianLandscape.landscapeNorm_nonnegative N p J
    positivity
  have hExp : Real.exp (2*((β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*u)≤
      Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := by
    apply Real.exp_le_exp.mpr
    convert mul_le_mul_of_nonneg_left hu' hc using 1 <;> ring
  have hn : (0 : ℝ)<N := Nat.cast_pos.mpr (by omega : 0<N)
  have he : 0≤Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T) := Real.exp_nonneg _
  unfold rowCeiling brownianVarianceCeiling
  calc
    _≤((s : ℝ)*u/(N : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+
      (((3*(s : ℝ))*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+3/2)/(N : ℝ))*(s : ℝ) :=
        add_le_add (mul_le_mul_of_nonneg_left hExp (by positivity)) le_rfl
    _=((s : ℝ)*u*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+
      3*(s : ℝ)^2*Real.exp ((2*(β : ℝ)*(p : ℝ)^2*GaussianLandscape.landscapeNorm N p J)*T)+(3/2)*(s : ℝ))/(N : ℝ) := by ring
    _≤_ := by
      apply div_le_div_of_nonneg_right _ hn.le
      have hsu' : (s : ℝ)*(u : ℝ)≤(T : ℝ)^2 := by simpa only [pow_two] using mul_le_mul hs' hu' u.coe_nonneg T.coe_nonneg
      have hss : (s : ℝ)^2≤(T : ℝ)^2 := by nlinarith [s.coe_nonneg,T.coe_nonneg]
      nlinarith [mul_le_mul_of_nonneg_right hsu' he,mul_le_mul_of_nonneg_right hss he]

end SphericalAging.ActualBrownianGammaVariance
