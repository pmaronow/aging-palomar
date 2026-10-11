module

public import SphericalAging.ActualAlgorithmTree
public import SphericalAging.GaussianTreeTerminalPairLaw
public import SphericalAging.AlgorithmicCorrelationMonotonicity
public import SphericalAging.RegularTreeGlobalPathSpecification

public section

/-! Concentration of literal terminal algorithm overlaps in the true
independently branching Gaussian tree. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAlgorithmTreeOverlap
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open ActualAlgorithmTree GaussianTreePathState GaussianTreeTerminalPairLaw
open IndependentBranchingSuccess GaussianBranchingSuccess PartialVarianceBranchingCoefficients
open AlgorithmicOverlapLipschitz AlgorithmicOverlapConcentration AlgorithmicCorrelationContinuity
open AlgorithmicCorrelationMonotonicity GaussianNoiseSymmetry GaussianLinearMixtureLaw
open scoped InnerProductSpace NNReal
variable {N p K : ℕ}

@[expose] def pairOverlap (A : TensorSpace N p→Vector N) (z : TensorSpace N p×TensorSpace N p) : ℝ :=
  ⟪A z.1,A z.2⟫_ℝ/(N:ℝ)

@[expose] def noisePair (ρ : ℝ) (z : TensorSpace N p×TensorSpace N p) : TensorSpace N p×TensorSpace N p :=
  (z.1,ρ•z.1+Real.sqrt (1-ρ^2)•z.2)

theorem pairOverlap_continuous (A : TensorSpace N p→Vector N) (hA : Continuous A) :
    Continuous (pairOverlap A) := ((hA.comp continuous_fst).inner (hA.comp continuous_snd)).div_const _

theorem noisePair_continuous (ρ : ℝ) : Continuous (noisePair (N:=N) (p:=p) ρ) :=
  continuous_fst.prodMk ((continuous_fst.const_smul ρ).add (continuous_snd.const_smul (Real.sqrt (1-ρ^2))))

theorem terminalOutput_eq_state (A : TensorSpace N p→Vector N)
    (u : ℕ→TensorSpace N p→TensorSpace N p→TensorSpace N p) (d : ℕ) (a : Fin d→Fin K) :
    terminalOutput A u d a=A∘terminalState u d a := by
  induction d with
  | zero => rfl
  | succ d ih =>
    funext z
    exact congrFun (ih (fun i => a i.succ)) _

theorem independent_pair_overlap_tail (hN : 0<N) (ρ : ℝ) (hρ : 0≤ρ) (hρ1 : ρ≤1)
    {L : ℝ≥0} (A : TensorSpace N p→Vector N) (hA : LipschitzWith L A)
    (hball : ∀s,‖A s‖≤Real.sqrt N) (ε : ℝ) (hε : 0≤ε) :
    ((stdGaussian (TensorSpace N p)).prod (stdGaussian (TensorSpace N p))).real
      {z | ε≤|pairOverlap A (noisePair ρ z)-correlation A ρ|}≤
      2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ))) := by
  have hc := (pairOverlap_continuous A hA.continuous).comp (noisePair_continuous ρ)
  have hB : MeasurableSet {z : TensorSpace N p×TensorSpace N p | ε≤|pairOverlap A (noisePair ρ z)-correlation A ρ|} :=
    measurableSet_le measurable_const ((hc.sub continuous_const).abs.measurable)
  have hm := inputPair_measurePreserving.hasLaw.measureReal_eq hB
  have ht := rawOverlap_centered_absolute_tail hN ρ hρ hρ1 A hA hball ε hε
  change (pairLaw N p).real {J | ε≤|rawOverlap ρ A J-correlation A ρ|}≤_ at ht
  have he : {J : Fin 2→Disorder N p | ε≤|pairOverlap A (noisePair ρ (inputPair J))-correlation A ρ|}=
      {J | ε≤|rawOverlap ρ A J-correlation A ρ|} := by ext J;rfl
  rw [he] at hm
  rw [←hm]
  exact ht

theorem actual_terminal_cross_overlap_tail (hN : 0<N) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) (hV0 : V 0=1)
    (hV1 : ∀j,V j≤1) {L : ℝ≥0} (A : TensorSpace N p→Vector N)
    (hA : LipschitzWith L A) (hball : ∀s,‖A s‖≤Real.sqrt N)
    (d : ℕ) (a b : Fin d→Fin K) (j : Fin d) (hab : a j≠b j)
    (hbefore : ∀i : Fin d,i<j→a i=b i) (ε : ℝ) (hε : 0≤ε) :
    ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real
      {z | ε≤|pairOverlap A (terminalState (update (parentCoefficient V) (freshCoefficient V)) d a z,
        terminalState (update (parentCoefficient V) (freshCoefficient V)) d b z)-correlation A (V (d-j.val))|}≤
      2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ))) := by
  let ρ := V (d-j.val)
  let ν := (stdGaussian (TensorSpace N p)).prod (stdGaussian (TensorSpace N p))
  have hlaw : HasLaw (fun z : TensorSpace N p×TreeSample (TensorSpace N p) K d =>
      (terminalState (update (parentCoefficient V) (freshCoefficient V)) d a z,
        terminalState (update (parentCoefficient V) (freshCoefficient V)) d b z))
      (ν.map (noisePair ρ)) ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)) :=
    ⟨((terminalState_measurable _ (update_measurable _ _) d a).prodMk
      (terminalState_measurable _ (update_measurable _ _) d b)).aemeasurable,
      actual_terminal_pair_map V hV hVm hV0 d a b j hab hbefore⟩
  have hB : MeasurableSet {z : TensorSpace N p×TensorSpace N p | ε≤|pairOverlap A z-correlation A ρ|} :=
    measurableSet_le measurable_const (((pairOverlap_continuous A hA.continuous).sub continuous_const).abs.measurable)
  have hm := hlaw.measureReal_eq hB
  have hnoise : MeasurePreserving (noisePair ρ) ν (ν.map (noisePair ρ)) :=
    ⟨(noisePair_continuous ρ).measurable,rfl⟩
  have hn := hnoise.hasLaw.measureReal_eq hB
  rw [hm,←hn]
  exact independent_pair_overlap_tail hN ρ (hV _) (hV1 _) A hA hball ε hε

theorem actual_terminal_self_overlap_tail (hN : 0<N) (V : ℕ→ℝ)
    (hV : ∀j,0≤V j) (hVm : ∀j,V (j+1)≤V j) {L : ℝ≥0}
    (A : TensorSpace N p→Vector N) (hA : LipschitzWith L A)
    (hball : ∀s,‖A s‖≤Real.sqrt N) (d : ℕ) (a : Fin d→Fin K) (ε : ℝ) (hε : 0≤ε) :
    ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real
      {z | ε≤|‖terminalOutput A (update (parentCoefficient V) (freshCoefficient V)) d a z‖^2/(N:ℝ)-correlation A 1|}≤
      2*Real.exp (-ε^2/(2*(overlapConstant N L:ℝ))) := by
  have hu : ∀j,MeasurePreserving (Function.uncurry (update (E:=TensorSpace N p)
      (parentCoefficient V) (freshCoefficient V) j))
      ((stdGaussian (TensorSpace N p)).prod (stdGaussian (TensorSpace N p))) (stdGaussian (TensorSpace N p)) :=
    fun j => mixture_measurePreserving _ _ (coefficients_unit V hV hVm j)
  have hB : MeasurableSet {s : TensorSpace N p | ε≤|‖A s‖^2/(N:ℝ)-correlation A 1|} :=
    measurableSet_le measurable_const ((((hA.continuous.norm.pow 2).div_const (N:ℝ)).sub continuous_const).abs.measurable)
  have hm := (terminalState_measurePreserving (stdGaussian (TensorSpace N p))
    (stdGaussian (TensorSpace N p)) _ hu d a).hasLaw.measureReal_eq hB
  have hn := (measurePreserving_fst (μ:=stdGaussian (TensorSpace N p))
    (ν:=stdGaussian (TensorSpace N p))).hasLaw.measureReal_eq hB
  have he : {z : TensorSpace N p×TensorSpace N p | ε≤|‖A z.1‖^2/(N:ℝ)-correlation A 1|}=
      {z | ε≤|pairOverlap A (noisePair 1 z)-correlation A 1|} := by
    ext z
    simp only [noisePair,one_smul,one_pow,sub_self,Real.sqrt_zero,zero_smul,add_zero,pairOverlap,
      real_inner_self_eq_norm_sq]
  rw [terminalOutput_eq_state]
  change ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K d)).real
    {z | ε≤|‖A (terminalState (update (parentCoefficient V) (freshCoefficient V)) d a z)‖^2/(N:ℝ)-correlation A 1|}≤_
  rw [hm,←hn,he]
  exact independent_pair_overlap_tail hN 1 (by norm_num) (by norm_num) A hA hball ε hε

end SphericalAging.ActualAlgorithmTreeOverlap
