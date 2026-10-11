module

public import SphericalAging.SphereEulerQuerySpan
public import SphericalAging.TerminalStateRepresentation
public import SphericalAging.VectorIto

public section

/-! Actual Brownian Euler nodes and their genuine full-filtration elementary
predictable integrands. All coefficients are constructed from the literal
query recursion; no interpolation equation is assumed. -/
noncomputable section
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter
open scoped BigOperators NNReal ENNReal InnerProductSpace
namespace SphericalAging.SphereEulerPredictable
open HardSphereDynamics SphereEulerCoefficients
open FourPapersCommon.FilteredBrownian
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

@[expose] def grid (h : ℝ≥0) (k : ℕ) : ℝ≥0 := h*k
theorem grid_mono (h : ℝ≥0) : Monotone (grid h) := by
  intro k l hkl
  unfold grid
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hkl) h.coe_nonneg

@[expose] def increment (D : BrownianDriver N P F) (h : ℝ≥0) (k : ℕ) (omega : Ω) : State N :=
  ∑j : Fin N,(D.coordinate j (grid h (k+1)) omega-D.coordinate j (grid h k) omega) • basisVector j

@[expose] def node (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (k : ℕ) (omega : Ω) : State N :=
  SphereEulerQuerySpan.state β h J x (fun j => increment D h j omega) k

omit [IsProbabilityMeasure P] in
theorem increment_stronglyMeasurable (D : BrownianDriver N P F) (h : ℝ≥0) (k : ℕ) :
    StronglyMeasurable[F (grid h (k+1))] (increment D h k) := by
  have hh := Finset.stronglyMeasurable_sum Finset.univ (fun j (_ : j∈Finset.univ) =>
    (((D.filtered j).stronglyAdapted (grid h (k+1))).sub
      (((D.filtered j).stronglyAdapted (grid h k)).mono
        (F.mono (grid_mono h (Nat.le_succ k))))).smul_const (basisVector j))
  convert hh using 1
  funext omega
  simp only [increment,Finset.sum_apply,Pi.sub_apply]

omit [IsProbabilityMeasure P] in
theorem node_stronglyMeasurable (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) :
    StronglyMeasurable[F (grid h k)] (node D β h J x k) := by
  let inc : ℕ→Ω→State N := increment D h
  have hz (j : ℕ) (hj : j<k) : Measurable[F (grid h k)] (inc j) :=
    ((increment_stronglyMeasurable D h j).mono
      (F.mono (grid_mono h (Nat.succ_le_of_lt hj)))).measurable
  change StronglyMeasurable[F (grid h k)]
    (fun omega => SphereEulerQuerySpan.state (β:ℝ) (h:ℝ) J x (fun j => inc j omega) k)
  letI : MeasurableSpace Ω := F (grid h k)
  apply Measurable.stronglyMeasurable
  exact SphereEulerQuerySpan.state_measurable_prefix (β:ℝ) (h:ℝ)
    (fun _ : Ω => J) (fun _ => x) inc measurable_const measurable_const k hz

omit [IsProbabilityMeasure P] in
theorem node_measurable (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) : Measurable (node D β h J x k) :=
  ((node_stronglyMeasurable D β h J x k).mono (F.le _)).measurable

@[expose] def boundedKnown (a : ℝ≥0) (f : Ω→ℝ) (hf : StronglyMeasurable[F a] f) (C : ℝ≥0)
    (hC : ∀omega,‖f omega‖≤C) : lpMeas ℝ ℝ (F a) 2 P :=
  let hm : MemLp f 2 P := MemLp.of_bound (hf.mono (F.le a)).aestronglyMeasurable C (.of_forall hC)
  ⟨hm.toLp f,hf.aestronglyMeasurable.congr hm.coeFn_toLp.symm⟩

theorem boundedKnown_ae (a : ℝ≥0) (f : Ω→ℝ) (hf : StronglyMeasurable[F a] f) (C : ℝ≥0)
    (hC : ∀omega,‖f omega‖≤C) :
    (boundedKnown (P:=P) a f hf C hC : Ω→ℝ)=ᵐ[P] f := by
  exact (MemLp.of_bound (μ:=P) (p:=2) (hf.mono (F.le a)).aestronglyMeasurable C (.of_forall hC)).coeFn_toLp

@[expose] def driftCap (β : ℝ≥0) (J : FiniteModel.Disorder N p) : ℝ≥0 :=
  ⟨(2+3*(β:ℝ)*(p:ℝ)*2^(p-1)*GaussianLandscape.landscapeNorm N p J)*Real.sqrt N,
    by have := GaussianLandscape.landscapeNorm_nonnegative N p J;positivity⟩
@[expose] def noiseCap : ℝ≥0 := ⟨3*Real.sqrt 2,by positivity⟩

@[expose] def driftField (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (k : ℕ) (i : Fin N) (omega : Ω) : ℝ :=
  SphereEulerCoefficients.drift β J (node D β h J x k omega) i
@[expose] def noiseField (D : BrownianDriver N P F) (β h : ℝ≥0) (J : FiniteModel.Disorder N p)
    (x : State N) (k : ℕ) (i j : Fin N) (omega : Ω) : ℝ :=
  SphereEulerCoefficients.noise (node D β h J x k omega) j i

theorem driftField_stronglyMeasurable (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (i : Fin N) :
    StronglyMeasurable[F (grid h k)] (driftField D β h J x k i) :=
  (PiLp.continuous_apply 2 (fun _ : Fin N => ℝ) i).comp_stronglyMeasurable
    ((contDiff_hamiltonianDrift β J).continuous.comp_stronglyMeasurable
      (clip_lipschitz.continuous.comp_stronglyMeasurable (node_stronglyMeasurable D β h J x k)))
theorem noiseField_stronglyMeasurable (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (i j : Fin N) :
    StronglyMeasurable[F (grid h k)] (noiseField D β h J x k i j) :=
  (continuous_noiseCoordinate i j).comp_stronglyMeasurable
    (clip_lipschitz.continuous.comp_stronglyMeasurable (node_stronglyMeasurable D β h J x k))

theorem driftField_bound (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (i : Fin N) (omega : Ω) :
    ‖driftField D β h J x k i omega‖≤driftCap β J :=
  (PiLp.norm_apply_le _ i).trans (drift_norm_bound hN β.coe_nonneg J _)
theorem noiseField_bound (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (i j : Fin N) (omega : Ω) :
    ‖noiseField D β h J x k i j omega‖≤noiseCap := by
  have hb : ‖basisVector j‖=1 := by simp [basisVector]
  have hx := clip_norm_le (node D β h J x k omega)
  have hn := ClippedHamiltonianDriftBounds.projection_norm_le_three hN
    (clip (node D β h J x k omega)) (basisVector j)
    (hx.trans (by nlinarith [Real.sqrt_nonneg (N:ℝ)]))
  refine (PiLp.norm_apply_le _ i).trans ?_
  change ‖Real.sqrt 2 • projection (clip (node D β h J x k omega)) (basisVector j)‖≤3*Real.sqrt 2
  rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  rw [hb] at hn
  exact (mul_le_mul_of_nonneg_left hn (Real.sqrt_nonneg _)).trans_eq (by ring)

@[expose] def driftKnown (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (i : Fin N) : lpMeas ℝ ℝ (F (grid h k)) 2 P :=
  boundedKnown (grid h k) (driftField D β h J x k i)
    (driftField_stronglyMeasurable D β h J x k i) (driftCap β J) (driftField_bound hN D β h J x k i)
@[expose] def noiseKnown (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (k : ℕ) (i j : Fin N) : lpMeas ℝ ℝ (F (grid h k)) 2 P :=
  boundedKnown (grid h k) (noiseField D β h J x k i j)
    (noiseField_stronglyMeasurable D β h J x k i j) noiseCap (noiseField_bound hN D β h J x k i j)

@[expose] def driftRows (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (M : ℕ) (i : Fin N) : PredictableProcessL2 F P :=
  ∑k ∈ Finset.range M,elementaryPredictable F (grid h k) (grid h (k+1)) (driftKnown hN D β h J x k i)
@[expose] def noiseRows (hN : 0<N) (D : BrownianDriver N P F) (β h : ℝ≥0)
    (J : FiniteModel.Disorder N p) (x : State N) (M : ℕ) (i j : Fin N) : PredictableProcessL2 F P :=
  ∑k ∈ Finset.range M,elementaryPredictable F (grid h k) (grid h (k+1)) (noiseKnown hN D β h J x k i j)

end SphericalAging.SphereEulerPredictable
