module

public import SphericalAging.GlobalHamiltonianParameter
public import SphericalAging.RandomInitialDependence

public section

/-! Actual joint dependence of the cutoff Hamiltonian flow on finite disorder
and arbitrary correlated L² initial data in the full initial filtration.
All classes are genuine Picard fixed points; coefficient bound independence
and joint continuity follow from the true fixed-point equation. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators InnerProductSpace
namespace SphericalAging.RandomHamiltonianParameter
open HardSphereDynamics LocalSDE PredictableItoTime PredictableDriftTime
open WeightedPredictable WeightedPicard PicardDependence HamiltonianParameter
open HamiltonianPicardDependence RandomInitialDependence
set_option maxHeartbeats 1800000
variable {N p : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 ‹MeasurableSpace Ω›}

/-- The actual cutoff SDE horizon class, parameterized by finite disorder
and the full-filtration random initial state. -/
@[expose] def randomHamiltonianClass (D : BrownianDriver N P F) (β : ℝ) (R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (q : BoundedDisorder N p A × InitialSpace N F P) : PredictableStateL2 N F P :=
  RandomInitialDependence.horizonClass D (drift_family_lipschitz β R hR A q.1) (noise_family_lipschitz N R hR) T q.2

/-- The actual cutoff Picard state class is jointly Lipschitz in disorder
and full-filtration random initial data on every bounded disorder set and finite time horizon. -/
theorem randomHamiltonianClass_lipschitz (D : BrownianDriver N P F) (β : ℝ)
    (R : ℝ) (hR : 0 < R) (A T : ℝ≥0) :
    ∃ K : ℝ≥0, LipschitzWith K (randomHamiltonianClass (p := p) D β R hR A T) := by
  let Kb := driftBound (N := N) (p := p) β R hR A
  let Ks := noiseBound N R hR
  obtain ⟨α, hα, Cd, Ci, hCd, hCi, hsmall⟩ := exists_contraction_parameters N Kb Ks T
  obtain ⟨C, hC⟩ := cutoffDrift_disorder_lipschitz (N := N) (p := p) β R hR
  have hd : ∀ V : PredictableProcessL2 F P, ‖multiply α T (driftVolterra T V)‖ ≤ Cd * ‖multiply α T V‖ := by
    intro V
    rw [hCd]
    exact WeightedDriftNorm.norm_weighted_driftVolterra_le hα T V
  have hi : ∀ j (V : PredictableProcessL2 F P),
      ‖multiply α T (itoVolterra (D.brownian j) (D.coordinateStronglyMeasurable j) (D.filtered j) T V)‖ ≤
        Ci * ‖multiply α T V‖ := by
    intro j V
    rw [hCi, one_div]
    exact WeightedItoNorm.norm_weighted_itoVolterra_le (D.brownian j)
      (D.coordinateStronglyMeasurable j) (D.filtered j) hα T V
  let Q : ℝ := (N : ℝ)*Cd*Kb+(N : ℝ)^2*Ci*Ks
  have hQ : Q < 1 := by dsimp only [Q]; exact_mod_cast hsmall
  let L : ℝ := Real.exp (|α| *T)*Real.exp (|α| *T)*
    (‖initialOperator (N := N) (F := F) (P := P) T‖+(N : ℝ)*T*C*(initialScale (P := P) T : ℝ))/(1-Q)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨⟨L, hL⟩, LipschitzWith.of_dist_le_mul (fun q r => ?_)⟩
  have hbc : ∀ i x, ‖CutoffSDE.cutoffDrift β q.1.1 R hR i x-CutoffSDE.cutoffDrift β r.1.1 R hR i x‖ ≤
      (C : ℝ)*‖q.1.1-r.1.1‖ := by
    intro i x
    change ‖(cutoffCoefficient R hR (hamiltonianDrift β q.1.1) x) i -
      (cutoffCoefficient R hR (hamiltonianDrift β r.1.1) x) i‖ ≤ _
    rw [← PiLp.sub_apply]
    exact (PiLp.norm_apply_le _ i).trans (hC _ _ x)
  have hnormSource : ‖multiply α T (initialOperator (F := F) (P := P) T q.2-initialOperator T r.2)‖ ≤
      Real.exp (|α| *T) * (‖initialOperator (N := N) (F := F) (P := P) T‖ * dist q r) := by
    have hh := norm_multiply_le α T (initialOperator (F := F) (P := P) T q.2-initialOperator T r.2)
    rw [← map_sub] at hh
    rw [← map_sub]
    have hdist : ‖q.2-r.2‖ ≤ dist q r := by
      simpa only [dist_eq_norm] using
        (show dist q.2 r.2 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_right _ _)
    exact hh.trans (mul_le_mul_of_nonneg_left
      (((initialOperator T).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))) (Real.exp_pos _).le)
  have hJ : ‖q.1.1-r.1.1‖ ≤ dist q r := by
    simpa only [Subtype.dist_eq, dist_eq_norm] using (show dist q.1 r.1 ≤ dist q r from by rw [Prod.dist_eq]; exact le_max_left _ _)
  have hw := weighted_sourceClass_family_sub_bound D
    (drift_family_lipschitz β R hR A q.1) (drift_family_lipschitz β R hR A r.1)
    (noise_family_lipschitz N R hR) α T Cd Ci hd hi hsmall
    (initialOperator (F := F) (P := P) T q.2) (initialOperator T r.2)
    ((C : ℝ)*‖q.1.1-r.1.1‖) (mul_nonneg C.coe_nonneg (norm_nonneg _)) hbc
  change ‖multiply α T (randomHamiltonianClass D β R hR A T q-randomHamiltonianClass D β R hR A T r)‖ ≤ _ at hw
  have hnum : ‖multiply α T (initialOperator (F := F) (P := P) T q.2-initialOperator T r.2)‖ +
      Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*‖q.1.1-r.1.1‖)*(initialScale (P := P) T : ℝ) ≤
      Real.exp (|α| *T)*(‖initialOperator (N := N) (F := F) (P := P) T‖*dist q r) +
      Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*dist q r)*(initialScale (P := P) T : ℝ) := by
    apply add_le_add hnormSource
    gcongr
  simp only [dist_eq_norm]
  have hu : randomHamiltonianClass D β R hR A T q-randomHamiltonianClass D β R hR A T r =
      multiply (-α) T (multiply α T (randomHamiltonianClass D β R hR A T q-randomHamiltonianClass D β R hR A T r)) :=
    (inverse_multiply α T _).symm
  calc
    _ = ‖multiply (-α) T (multiply α T (randomHamiltonianClass D β R hR A T q-randomHamiltonianClass D β R hR A T r))‖ := congrArg norm hu
    _ ≤ Real.exp (|α| *T) * ‖multiply α T (randomHamiltonianClass D β R hR A T q-randomHamiltonianClass D β R hR A T r)‖ := by
      simpa only [abs_neg] using norm_multiply_le (-α) T (multiply α T (randomHamiltonianClass D β R hR A T q-randomHamiltonianClass D β R hR A T r))
    _ ≤ Real.exp (|α| *T) * ((Real.exp (|α| *T)*(‖initialOperator (N := N) (F := F) (P := P) T‖*dist q r) +
        Real.exp (|α| *T)*(N : ℝ)*T*((C : ℝ)*dist q r)*(initialScale (P := P) T : ℝ))/(1-Q)) :=
      mul_le_mul_of_nonneg_left (hw.trans ((div_le_div_iff_of_pos_right (sub_pos.mpr hQ)).mpr hnum)) (Real.exp_pos _).le
    _ = L * dist q r := by dsimp only [L]; ring


lemma horizonClass_drift_bound_independent (D : BrownianDriver N P F)
    {K L Ks : ℝ≥0} {b : Fin N → State N → ℝ}
    {sigma : Fin N → Fin N → State N → ℝ}
    (hb : ∀ i,LipschitzWith K (b i)) (hc : ∀ i,LipschitzWith L (b i))
    (hs : ∀ i j,LipschitzWith Ks (sigma i j)) (T : ℝ≥0) (Z : InitialSpace N F P) :
    RandomInitialDependence.horizonClass D hb hs T Z =
      RandomInitialDependence.horizonClass D hc hs T Z := by
  apply (GlobalSDE.exists_unique_picard_fixedPoint D hc hs T (initialOperator T Z)).choose_spec.2
  rw [← GlobalHamiltonianParameter.finiteDrift_bound_independent hb hc]
  exact PicardDependence.sourceClass_fixedPoint D hb hs T (initialOperator T Z)

lemma randomHamiltonianClass_bound_independent (D : BrownianDriver N P F)
    (β R : ℝ) (hR : 0 < R) (A B T : ℝ≥0)
    (J : FiniteModel.Disorder N p) (hA : ‖J‖ ≤ A) (hB : ‖J‖ ≤ B)
    (Z : InitialSpace N F P) :
    randomHamiltonianClass D β R hR A T (⟨J,hA⟩,Z) =
      randomHamiltonianClass D β R hR B T (⟨J,hB⟩,Z) :=
  horizonClass_drift_bound_independent D _ _ _ T Z

/-- Canonical actual random-initial Picard class on unrestricted disorder. -/
@[expose] def globalClass (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0)
    (q : FiniteModel.Disorder N p × InitialSpace N F P) : PredictableStateL2 N F P :=
  randomHamiltonianClass D β R hR (‖q.1‖₊+1) T (⟨q.1,by simp⟩,q.2)

lemma globalClass_eq_bounded (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (A T : ℝ≥0)
    (J : FiniteModel.Disorder N p) (hA : ‖J‖ ≤ A) (Z : InitialSpace N F P) :
    globalClass D β R hR T (J,Z) = randomHamiltonianClass D β R hR A T (⟨J,hA⟩,Z) :=
  randomHamiltonianClass_bound_independent D β R hR _ A T J _ hA Z

/-- The canonical class is precisely the genuine constructed random-initial
Hamiltonian solution for every actual measurable L² initial state. -/
theorem globalClass_initialStateClass (D : BrownianDriver N P F) (β R : ℝ)
    (hR : 0 < R) (T : ℝ≥0) (J : FiniteModel.Disorder N p)
    (Z0 : Ω → State N) (hZ : StronglyMeasurable[F 0] Z0) (hmZ : MemLp Z0 2 P)
    (A : ℝ≥0) (hA : ‖J‖ ≤ A) :
    globalClass D β R hR T (J,initialStateClass Z0 hZ hmZ) =
      RandomInitialSDE.horizonClass D (drift_family_lipschitz β R hR A ⟨J,hA⟩)
        (noise_family_lipschitz N R hR) Z0 hZ hmZ T := by
  rw [globalClass_eq_bounded D β R hR A T J hA]
  exact horizonClass_initialStateClass D _ _ Z0 hZ hmZ T

/-- Joint continuity in unrestricted disorder and full-filtration random initial state. -/
theorem globalClass_continuous (D : BrownianDriver N P F) (β R : ℝ) (hR : 0 < R) (T : ℝ≥0) :
    Continuous (globalClass (p := p) D β R hR T) := by
  apply continuous_iff_continuousAt.mpr
  intro q
  let A : ℝ≥0 := ‖q.1‖₊+1
  have hqA : ‖q.1‖ ≤ A := by dsimp [A]; simp
  obtain ⟨K,hK⟩ := randomHamiltonianClass_lipschitz (p := p) D β R hR A T
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  let δ : ℝ := min 1 (ε/((K : ℝ)+1))
  have hδ : 0 < δ := lt_min (by norm_num) (div_pos hε (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro r hr
  have hr1 : dist r q < 1 := hr.trans_le (min_le_left _ _)
  have hJdist : dist r.1 q.1 ≤ dist r q := by rw [Prod.dist_eq]; exact le_max_left _ _
  have hrA : ‖r.1‖ ≤ A := by
    have hnorm := norm_le_norm_add_norm_sub q.1 r.1
    rw [← dist_eq_norm] at hnorm
    rw [dist_comm q.1 r.1] at hnorm
    change ‖r.1‖ ≤ ‖q.1‖+1
    linarith
  rw [globalClass_eq_bounded D β R hR A T r.1 hrA r.2,
    globalClass_eq_bounded D β R hR A T q.1 hqA q.2]
  have hd : dist ((⟨r.1,hrA⟩,r.2) : BoundedDisorder N p A × InitialSpace N F P)
      ((⟨q.1,hqA⟩,q.2) : BoundedDisorder N p A × InitialSpace N F P) = dist r q := by
    simp only [Prod.dist_eq, Subtype.dist_eq]
  calc
    _ ≤ (K : ℝ)*dist r q := by simpa only [hd] using hK.dist_le_mul (⟨r.1,hrA⟩,r.2) (⟨q.1,hqA⟩,q.2)
    _ ≤ ((K : ℝ)+1)*dist r q := mul_le_mul_of_nonneg_right (by linarith) dist_nonneg
    _ < ε := by
      have hsmall := hr.trans_le (min_le_right _ _)
      have hm := (lt_div_iff₀ (by positivity : (0 : ℝ) < (K : ℝ)+1)).mp hsmall
      simpa only [mul_comm] using hm


end SphericalAging.RandomHamiltonianParameter
