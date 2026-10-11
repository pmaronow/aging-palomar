module

public import SphericalAging.GaussianTreeFirstForkPairLaw

public section

/-! Exact terminal-pair law at the actual first divergent child of two
paths. Its correlation is the prescribed partial variance at their LCA. -/
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianTreeTerminalPairLaw
open MeasureTheory ProbabilityTheory IndependentBranchingSuccess GaussianTreePathState
open GaussianTreeFirstForkPairLaw GaussianCommonFuturePairLaw GaussianBranchingSuccess
open BranchingNodeLaw GaussianLinearMixtureLaw GaussianTreePathNoiseLaw PartialVarianceBranchingCoefficients
variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] {K : ℕ}

theorem terminal_pair_measurePreserving (α β : ℕ→ℝ)
    (hunit : ∀d,(α d)^2+(β d)^2=1) (d : ℕ) (a b : Fin d→Fin K)
    (j : Fin d) (hab : a j≠b j) (hbefore : ∀i : Fin d,i<j→a i=b i) :
    MeasurePreserving (fun z : E×TreeSample E K d =>
      (terminalState (update α β) d a z,terminalState (update α β) d b z))
      ((stdGaussian E).prod (treeLaw (stdGaussian E) K d))
      (((stdGaussian E).prod (stdGaussian E)).map (correlatedPair (rootCoefficient α (d-j.val)))) := by
  induction d with
  | zero => exact Fin.elim0 j
  | succ d ih =>
    cases j using Fin.cases with
    | zero =>
      simpa only [Fin.val_zero,Nat.sub_zero] using firstFork_pair_measurePreserving α β hunit d a b hab
    | succ j =>
      have h0 : a 0=b 0 := hbefore 0 (by simp)
      have hpre : ∀i : Fin d,i<j→a i.succ=b i.succ :=
        fun i hi => hbefore i.succ (Fin.succ_lt_succ_iff.mpr hi)
      have htail := ih (fun i => a i.succ) (fun i => b i.succ) j hab hpre
      have hu : ∀n,MeasurePreserving (Function.uncurry (update (E:=E) α β n))
          ((stdGaussian E).prod (stdGaussian E)) (stdGaussian E) :=
        fun n => mixture_measurePreserving (α n) (β n) (hunit n)
      have hchild := childSampler_measurePreserving (stdGaussian E) (stdGaussian E)
        (update α β) hu d (b 0)
      have hf : (fun z : E×TreeSample E K (d+1) =>
          (terminalState (update α β) (d+1) a z,terminalState (update α β) (d+1) b z))=
          (fun z : E×TreeSample E K d =>
            (terminalState (update α β) d (fun i => a i.succ) z,
              terminalState (update α β) d (fun i => b i.succ) z)) ∘ childSampler (update α β) d (b 0) := by
        funext z
        simp only [terminalState,Function.comp_def,h0]
      rw [hf]
      simpa only [Fin.val_succ,Nat.succ_sub_succ_eq_sub] using htail.comp hchild

theorem actual_terminal_pair_map (V : ℕ→ℝ) (hV : ∀d,0≤V d)
    (hmono : ∀d,V (d+1)≤V d) (hV0 : V 0=1) (d : ℕ) (a b : Fin d→Fin K)
    (j : Fin d) (hab : a j≠b j) (hbefore : ∀i : Fin d,i<j→a i=b i) :
    ((stdGaussian E).prod (treeLaw (stdGaussian E) K d)).map
      (fun z : E×TreeSample E K d =>
        (terminalState (update (parentCoefficient V) (freshCoefficient V)) d a z,
          terminalState (update (parentCoefficient V) (freshCoefficient V)) d b z))=
      ((stdGaussian E).prod (stdGaussian E)).map
        (fun z : E×E => (z.1,V (d-j.val)•z.1+Real.sqrt (1-(V (d-j.val))^2)•z.2)) := by
  have hh := (terminal_pair_measurePreserving (E:=E) (parentCoefficient V) (freshCoefficient V)
    (coefficients_unit V hV hmono) d a b j hab hbefore).map_eq
  rw [rootCoefficient_partialVariance V hV hmono hV0] at hh
  have hs2 := Real.sq_sqrt (hV (d-j.val))
  have hs4 : (Real.sqrt (V (d-j.val)))^4=(V (d-j.val))^2 := by
    rw [show (4:ℕ)=2*2 by rfl,pow_mul,hs2]
  have hf : (correlatedPair (E:=E) (Real.sqrt (V (d-j.val))) : E×E→E×E)=
      (fun z : E×E => (z.1,V (d-j.val)•z.1+Real.sqrt (1-(V (d-j.val))^2)•z.2)) := by
    funext z
    simp only [correlatedPair_apply,hs2,hs4]
  rw [hf] at hh
  exact hh

end SphericalAging.GaussianTreeTerminalPairLaw
