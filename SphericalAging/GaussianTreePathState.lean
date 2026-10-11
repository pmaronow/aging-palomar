module

public import SphericalAging.BranchingNodeLaw
public import SphericalAging.PartialVarianceBranchingCoefficients

public section

/-! Literal terminal states and their exact affine dependence on the root
under the actual independently branching product sample space. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianTreePathState
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess BranchingNodeLaw
open GaussianBranchingSuccess GaussianLinearMixtureLaw PartialVarianceBranchingCoefficients
variable {S G E : Type} [MeasurableSpace S] [MeasurableSpace G] {K : ℕ}

@[expose] def terminalState (update : ℕ→S→G→S) :
    (d : ℕ)→(Fin d→Fin K)→S×TreeSample G K d→S
  | 0,_,z => z.1
  | d+1,a,z => terminalState update d (fun i => a i.succ) (childSampler update d (a 0) z)

theorem terminalState_measurable (update : ℕ→S→G→S)
    (hu : ∀d,Measurable (Function.uncurry (update d)))
    (d : ℕ) (a : Fin d→Fin K) : Measurable (terminalState update d a) := by
  induction d with
  | zero => exact measurable_fst
  | succ d ih =>
    have hg : Measurable (fun z : S×TreeSample G K (d+1) => z.2 (a 0)) :=
      (measurable_pi_apply (a 0)).comp measurable_snd
    exact (ih (fun i => a i.succ)).comp
      (((hu d).comp (measurable_fst.prodMk hg.fst)).prodMk hg.snd)

theorem terminalState_measurePreserving (μ : Measure S) [IsProbabilityMeasure μ]
    (ν : Measure G) [IsProbabilityMeasure ν] (update : ℕ→S→G→S)
    (hu : ∀d,MeasurePreserving (Function.uncurry (update d)) (μ.prod ν) μ)
    (d : ℕ) (a : Fin d→Fin K) :
    MeasurePreserving (terminalState update d a) (μ.prod (treeLaw ν K d)) μ := by
  induction d with
  | zero => exact measurePreserving_fst
  | succ d ih =>
    exact (ih (fun i => a i.succ)).comp
      (childSampler_measurePreserving μ ν update hu d (a 0))

section Hilbert
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

@[expose] def rootCoefficient (α : ℕ→ℝ) : ℕ→ℝ
  | 0 => 1
  | d+1 => rootCoefficient α d*α d

@[expose] def noiseVariance (α β : ℕ→ℝ) : ℕ→ℝ
  | 0 => 0
  | d+1 => (rootCoefficient α d*β d)^2+noiseVariance α β d

@[expose] def residualState (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K) (z : TreeSample E K d) : E :=
  terminalState (update α β) d a (0,z)

theorem terminalState_affine (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K)
    (s : E) (z : TreeSample E K d) :
    terminalState (update α β) d a (s,z)=rootCoefficient α d•s+residualState α β d a z := by
  induction d generalizing s with
  | zero => simp [terminalState,rootCoefficient,residualState]
  | succ d ih =>
    have hr := ih (fun i => a i.succ) (β d•(z (a 0)).1) (z (a 0)).2
    change terminalState (update α β) d (fun i => a i.succ)
      (α d•s+β d•(z (a 0)).1,(z (a 0)).2)=_
    rw [ih]
    have hz : residualState α β (d+1) a z=
        rootCoefficient α d•(β d•(z (a 0)).1)+residualState α β d (fun i => a i.succ) (z (a 0)).2 := by
      simpa only [residualState,terminalState,childSampler,update,smul_zero,zero_add] using hr
    rw [rootCoefficient,hz,smul_add,smul_smul]
    abel

theorem residualState_succ (α β : ℕ→ℝ) (d : ℕ) (a : Fin (d+1)→Fin K)
    (z : TreeSample E K (d+1)) :
    residualState α β (d+1) a z=(rootCoefficient α d*β d)•(z (a 0)).1+
      residualState α β d (fun i => a i.succ) (z (a 0)).2 := by
  unfold residualState
  simp only [terminalState,childSampler,update,smul_zero,zero_add]
  rw [terminalState_affine,smul_smul]
  rfl

theorem residualState_measurable (α β : ℕ→ℝ) (d : ℕ) (a : Fin d→Fin K) :
    Measurable (residualState (E:=E) α β d a) :=
  (terminalState_measurable (update α β) (update_measurable α β) d a).comp
    (measurable_const.prodMk measurable_id)

theorem noiseVariance_nonneg (α β : ℕ→ℝ) (d : ℕ) : 0≤noiseVariance α β d := by
  induction d with
  | zero => rfl
  | succ d ih => exact add_nonneg (sq_nonneg _) ih

theorem totalVariance_one (α β : ℕ→ℝ) (h : ∀d,(α d)^2+(β d)^2=1) (d : ℕ) :
    (rootCoefficient α d)^2+noiseVariance α β d=1 := by
  induction d with
  | zero => norm_num [rootCoefficient,noiseVariance]
  | succ d ih =>
    simp only [rootCoefficient,noiseVariance,mul_pow]
    nlinarith [h d]

end Hilbert
end SphericalAging.GaussianTreePathState
