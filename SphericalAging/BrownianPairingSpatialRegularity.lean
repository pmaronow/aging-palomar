module

public import SphericalAging.BrownianPairingSpatialTaylor
public import SphericalAging.ActualGammaPredictorNoiseBounds
public import SphericalAging.SphereEulerQuerySpan

public section

/-! Genuine continuity of the pairing Taylor terms and exact identification
of its physical frozen-noise linear term with the actual Γ noise row. -/
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators InnerProductSpace
namespace SphericalAging.BrownianPairingSpatialRegularity
open FiniteModel HardSphereDynamics LocalSDE BrownianPairingSpatialTaylor
open ActualGammaPredictorNoiseBounds ActualSphereTransition ActualSphereGammaVariance
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

theorem pairing_continuous (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun q : State N×State N => pairing f g d q.1 q.2) :=
  ((continuous_snd.inner (hf.comp continuous_fst)).div_const d).add (hg.comp continuous_fst)

theorem linearIncrement_continuous (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    Continuous (fun q : (State N×State N)×(State N×State N) => linearIncrement f g d q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hD : Continuous (fun q : (State N×State N)×(State N×State N) => fderiv ℝ f q.1.1 q.2.1) :=
    ((hf.continuous_fderiv (by norm_num)).comp (continuous_fst.comp continuous_fst)).clm_apply (continuous_fst.comp continuous_snd)
  have hG : Continuous (fun q : (State N×State N)×(State N×State N) => fderiv ℝ g q.1.1 q.2.1) :=
    ((hg.continuous_fderiv (by norm_num)).comp (continuous_fst.comp continuous_fst)).clm_apply (continuous_fst.comp continuous_snd)
  exact ((((continuous_snd.comp continuous_fst).inner hD).div_const d).add hG).add
    (((continuous_snd.comp continuous_snd).inner (hf.continuous.comp (continuous_fst.comp continuous_fst))).div_const d)

theorem remainder_continuous (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) :
    Continuous (fun q : (State N×State N)×(State N×State N) => remainder f g d q.1.1 q.1.2 q.2.1 q.2.2) := by
  have hmapA : Continuous (fun q : (State N×State N)×(State N×State N) => (q.1.2,q.2.1+q.2.2)) := by fun_prop
  have hmapB : Continuous (fun q : (State N×State N)×(State N×State N) => (q.1.1,q.2.1)) := by fun_prop
  have hmapL : Continuous (fun q : (State N×State N)×(State N×State N) => ((q.1.1,q.2.1),(q.1.2-q.1.1,q.2.2))) := by fun_prop
  have hA : Continuous (fun q : (State N×State N)×(State N×State N) => pairing f g d q.1.2 (q.2.1+q.2.2)) :=
    (pairing_continuous f g d hf.continuous hg.continuous).comp hmapA
  have hB : Continuous (fun q : (State N×State N)×(State N×State N) => pairing f g d q.1.1 q.2.1) :=
    (pairing_continuous f g d hf.continuous hg.continuous).comp hmapB
  have hL : Continuous (fun q : (State N×State N)×(State N×State N) => linearIncrement f g d q.1.1 q.2.1 (q.1.2-q.1.1) q.2.2) :=
    (linearIncrement_continuous f g d hf hg).comp hmapL
  exact (hA.sub hB).sub hL

theorem linearIncrement_noise_sum (f : State N→State N) (g : State N→ℝ) (d : ℝ)
    (x b w : State N) :
    linearIncrement f g d x b (Real.sqrt 2 • projection x w) w=
      ∑ j : Fin N,(⟪b,fderiv ℝ f x (noiseColumn x j)⟫_ℝ/d+
        fderiv ℝ g x (noiseColumn x j)+(f x) j/d)*w j := by
  have hwi : ⟪w,f x⟫_ℝ=∑ j : Fin N,w j*(f x) j := by
    calc
      _=⟪∑ j : Fin N,w j • basisVector j,f x⟫_ℝ := congrArg (fun z : State N => ⟪z,f x⟫_ℝ) (state_sum_basis w).symm
      _=_ := by
        rw [sum_inner]
        apply Finset.sum_congr rfl
        intro j _
        rw [real_inner_smul_left,real_inner_comm,basis_inner]
  rw [←SphereEulerQuerySpan.noise_sum x w]
  unfold linearIncrement
  simp only [map_sum,map_smul,inner_sum,real_inner_smul_right,smul_eq_mul,hwi]
  simp only [Finset.sum_div,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem actual_linearIncrement_noise_sum (β R : ℝ≥0) (hR : 0<(R : ℝ)) (J : Disorder N p)
    (T t s q : ℝ≥0) (x b w : State N) :
    linearIncrement (mean (NullAugmentation.driver (VectorBrownian.driver N)) β R hR J (t-q))
      (initialMean β R hR J T (t-q) (s-q)) (Real.sqrt 2*(N : ℝ)) x b
      (Real.sqrt 2 • projection x w) w=∑ j : Fin N,noiseRow β R hR J T t s q x b j*w j := by
  rw [linearIncrement_noise_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [noiseRow,linearTest_fderiv]

end SphericalAging.BrownianPairingSpatialRegularity
