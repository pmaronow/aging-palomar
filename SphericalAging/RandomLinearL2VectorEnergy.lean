module

public import SphericalAging.RandomVectorSDELocalization
public import SphericalAging.RandomLinearTerminalOperations

public section

/-! Whole-vector linear energy for arbitrary initial-filtration L² data.
Bounded past-event localization and Fatou preserve the true vector drift
and full noise trace constants, with no dimension factor. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory StochasticCalculus Filter Topology
open scoped NNReal ENNReal InnerProductSpace
namespace SphericalAging.RandomLinearL2VectorEnergy
open HardSphereDynamics LocalSDE PredictableLinearCoefficient RandomLinearVariationalSDE
  RandomLinearTerminalOperations RandomVectorSDELocalization
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
variable {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 mΩ} {Kb Ks : ℝ≥0}

lemma integrable_norm_sq (Z : Ω→State N) (hm : MemLp Z 2 P) :
    Integrable (fun ω => ‖Z ω‖^2) P := by
  simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat,Real.rpow_natCast]
    using hm.integrable_norm_rpow'

/-- The actual linear terminal class has dimension-free vector energy
for every square-integrable, possibly unbounded and correlated F₀ state. -/
theorem terminalClass_secondMoment
    (D : BrownianDriver N P F)
    (a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb)
    (sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks)
    (Z0 : Ω→State N) (hZ0 : StronglyMeasurable[F 0] Z0) (hm : MemLp Z0 2 P)
    (driftBound noiseTraceBound : ℝ≥0)
    (haNorm : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      ‖WithLp.toLp 2 (fun i => (a i).value q v)‖≤driftBound*‖v‖)
    (hsTrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q v)^2)≤noiseTraceBound*‖v‖^2)
    (hnull : ∀ A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (T t : ℝ≥0) (ht : t≤T) :
    (∫ ω,‖terminalClass D a sigma Z0 hZ0 hm T t ω‖^2 ∂P)≤
      (∫ ω,‖Z0 ω‖^2 ∂P)*Real.exp (((2*driftBound+1+noiseTraceBound):ℝ)*(t:ℝ)) := by
  let C (k : ℕ) (ω : Ω) : ℝ := if ‖Z0 ω‖≤k then 1 else 0
  have hC (k : ℕ) : StronglyMeasurable[F 0] (C k) := by
    exact StronglyMeasurable.ite
      (StronglyMeasurable.measurableSet_le hZ0.norm stronglyMeasurable_const)
      stronglyMeasurable_const stronglyMeasurable_const
  have hCb (k : ℕ) : ∀ ω,‖C k ω‖≤(1 : ℝ≥0) := by
    intro ω
    dsimp only [C]
    split_ifs <;> norm_num
  let W (k : ℕ) : Ω→State N := fun ω => C k ω • Z0 ω
  have hW (k : ℕ) : StronglyMeasurable[F 0] (W k) := (hC k).smul hZ0
  have hWm (k : ℕ) : MemLp (W k) 2 P := bounded_scalar_memLp Z0 hm (C k) (hC k) 1 (hCb k)
  have hWb (k : ℕ) : ∀ᵐ ω ∂P,‖W k ω‖≤(k : ℝ≥0) := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [W,C]
    split_ifs with hω
    · simpa only [one_smul,NNReal.coe_natCast] using hω
    · simp
  have hWle (k : ℕ) : ∀ᵐ ω ∂P,‖W k ω‖^2≤‖Z0 ω‖^2 := by
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [W,C]
    split_ifs <;> simp
  let Z (k : ℕ) : Ω→State N := terminalClass D a sigma (W k) (hW k) (hWm k) T t
  let Y : Ω→State N := terminalClass D a sigma Z0 hZ0 hm T t
  let E : ℝ := Real.exp (((2*driftBound+1+noiseTraceBound):ℝ)*(t:ℝ))
  let B : ℝ := (∫ ω,‖Z0 ω‖^2 ∂P)*E
  have hB : 0≤B := by dsimp only [B,E];positivity
  have hZm (k : ℕ) : MemLp (Z k) 2 P := Lp.memLp _
  have hbound (k : ℕ) : (∫ ω,‖Z k ω‖^2 ∂P)≤B := by
    have he := terminalClass_ae D a sigma (W k) (hW k) (hWm k) T t
    have hsol := process_strongSolution D a sigma (W k) (hW k) (hWm k) T
    have hh := random_vector_solution_secondMoment hsol (hWm k) k (hWb k)
      driftBound noiseTraceBound haNorm hsTrace hnull t ht
    calc
      _ = ∫ ω,‖process D a sigma (W k) (hW k) (hWm k) T t ω‖^2 ∂P :=
        integral_congr_ae (he.mono (fun _ h => congrArg (fun v => ‖v‖^2) h))
      _ ≤ (∫ ω,‖W k ω‖^2 ∂P)*E := hh.2
      _ ≤ B := mul_le_mul_of_nonneg_right
        (integral_mono_ae (integrable_norm_sq _ (hWm k)) (integrable_norm_sq _ hm) (hWle k))
        (Real.exp_pos _).le
  have hlim : ∀ᵐ ω ∂P,Tendsto (fun k => Z k ω) atTop (𝓝 (Y ω)) := by
    have he (k : ℕ) := terminalClass_bounded_scalar D a sigma Z0 hZ0 hm
      (C k) (hC k) 1 (hCb k) T t ht hnull
    filter_upwards [ae_all_iff.mpr he] with ω hω
    obtain ⟨k,hk⟩ := exists_nat_ge ‖Z0 ω‖
    have hev : ∀ᶠ n : ℕ in atTop,Z n ω=Y ω := by
      filter_upwards [eventually_ge_atTop k] with n hn
      have hz : ‖Z0 ω‖≤(n : ℝ) := hk.trans (by exact_mod_cast hn)
      have hc : C n ω=1 := ite_eq_left hz
      have heq := hω n
      change Z n ω=C n ω • Y ω at heq
      simpa only [hc,one_smul] using heq
    exact tendsto_const_nhds.congr' (hev.mono (fun _ h => h.symm))
  exact (secondMoment_of_ae_tendsto Z Y B hB (fun k => (hZm k).aestronglyMeasurable)
    (Lp.memLp _).aestronglyMeasurable (fun k => integrable_norm_sq _ (hZm k)) hbound hlim).2

/-- Every true random-initial linear strong solution has the same energy
bound; the initial data need only lie in L². -/
theorem strongSolution_secondMoment
    {a : Fin N→Coefficient (N:=N) (F:=F) (P:=P) Kb}
    {sigma : Fin N→Fin N→Coefficient (N:=N) (F:=F) (P:=P) Ks}
    {D : BrownianDriver N P F} {Z0 : Ω→State N} {X : ℝ≥0→Ω→State N} {T : ℝ≥0}
    (h : IsStrongSolutionOn a sigma D Z0 X T)
    (hZ0 : StronglyMeasurable[F 0] Z0) (hm : MemLp Z0 2 P)
    (driftBound noiseTraceBound : ℝ≥0)
    (haNorm : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      ‖WithLp.toLp 2 (fun i => (a i).value q v)‖≤driftBound*‖v‖)
    (hsTrace : ∀ᵐ q ∂nonnegativeLebesgueMeasure.prod P,∀ v : State N,
      (∑ i : Fin N,∑ j : Fin N,((sigma i j).value q v)^2)≤noiseTraceBound*‖v‖^2)
    (hnull : ∀ A : Set Ω,MeasurableSet A→P A=0→MeasurableSet[F 0] A)
    (t : ℝ≥0) (ht : t≤T) :
    MemLp (X t) 2 P ∧ (∫ ω,‖X t ω‖^2 ∂P)≤
      (∫ ω,‖Z0 ω‖^2 ∂P)*Real.exp (((2*driftBound+1+noiseTraceBound):ℝ)*(t:ℝ)) := by
  have he := pathwise_uniqueness (process_strongSolution D a sigma Z0 hZ0 hm T) h hnull
  have htclass : terminalClass D a sigma Z0 hZ0 hm T t=ᵐ[P] X t :=
    (terminalClass_ae D a sigma Z0 hZ0 hm T t).trans (he.mono (fun _ h => h t ht))
  refine ⟨(Lp.memLp _).ae_eq htclass,?_⟩
  rw [←integral_congr_ae (htclass.mono (fun _ h => congrArg (fun v => ‖v‖^2) h))]
  exact terminalClass_secondMoment D a sigma Z0 hZ0 hm driftBound noiseTraceBound haNorm hsTrace hnull T t ht

end SphericalAging.RandomLinearL2VectorEnergy
