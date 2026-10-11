module

public import SphericalAging.RegularTreeGlobalToLocal
public import SphericalAging.GaussianBranchingSuccess

public section

/-! The literal complete tree of algorithm outputs under actual independently
branching Gaussian inputs. The joint high-energy event is the derived Jensen
success event on these exact terminal outputs. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualAlgorithmTree
open Set MeasureTheory ProbabilityTheory FiniteModel RegularTreeEnergyTelescoping RegularTreeGlobalToLocal
open IndependentBranchingSuccess IndependentBranchingSuccessEvent GaussianBranchingSuccess
variable {E : Type} [MeasurableSpace E] {N K : ℕ}

@[expose] def outputTree (A : E→Vector N) (u : ℕ→E→E→E) :
    (d : ℕ)→E→TreeSample E K d→TreeData (Vector N) K d
  | 0,s,_ => A s
  | d+1,s,z => (A s,fun i => outputTree A u d (u d s (z i).1) (z i).2)

@[expose] def terminalOutput (A : E→Vector N) (u : ℕ→E→E→E) :
    (d : ℕ)→(Fin d→Fin K)→E×TreeSample E K d→Vector N
  | 0,_,z => A z.1
  | d+1,a,z => terminalOutput A u d (fun i => a i.succ)
      (u d z.1 (z.2 (a 0)).1,(z.2 (a 0)).2)

theorem terminalOutput_measurable (A : E→Vector N) (hA : Measurable A)
    (u : ℕ→E→E→E) (hu : ∀d,Measurable (Function.uncurry (u d)))
    (d : ℕ) (a : Fin d→Fin K) : Measurable (terminalOutput A u d a) := by
  induction d with
  | zero => exact hA.comp measurable_fst
  | succ d ih =>
    have hz : Measurable (fun z : E×TreeSample E K (d+1) => z.2 (a 0)) :=
      (measurable_pi_apply (a 0)).comp measurable_snd
    exact (ih (fun i => a i.succ)).comp
      (((hu d).comp (measurable_fst.prodMk hz.fst)).prodMk hz.snd)

theorem leafAt_outputTree (A : E→Vector N) (u : ℕ→E→E→E)
    (d : ℕ) (s : E) (z : TreeSample E K d) (a : Fin d→Fin K) :
    leafAt d (outputTree A u d s z) a=terminalOutput A u d a (s,z) := by
  induction d generalizing s with
  | zero => rfl
  | succ d ih => exact ih _ _ (fun i => a i.succ)

theorem event_all_leaves (A : E→Vector N) (u : ℕ→E→E→E) (B : Set E)
    (P : Vector N→Prop) (hBP : ∀s∈B,P (A s)) (d : ℕ) (s : E)
    (z : TreeSample E K d) (hz : (s,z)∈event K u B d) :
    AllLeaves P d (outputTree A u d s z) := by
  induction d generalizing s with
  | zero => exact hBP s hz
  | succ d ih => intro i;exact ih _ _ (hz i)

theorem ball_all_leaves (A : E→Vector N) (hball : ∀s,‖A s‖≤Real.sqrt N)
    (u : ℕ→E→E→E) (d : ℕ) (s : E) (z : TreeSample E K d) :
    AllLeaves (fun x => ‖x‖≤Real.sqrt N) d (outputTree A u d s z) := by
  induction d generalizing s with
  | zero => exact hball s
  | succ d ih => intro i;exact ih _ _

section Gaussian
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

theorem actual_joint_success_probability (A : E→Vector N) (a b : ℕ→ℝ)
    (hunit : ∀j,(a j)^2+(b j)^2=1) (B : Set E) (hB : MeasurableSet B) (d : ℕ) :
    ((stdGaussian E).real B)^(K^d)≤
      ((stdGaussian E).prod (treeLaw (stdGaussian E) K d)).real
        (event K (update a b) B d) :=
  actual_gaussian_tree_success_lower K a b hunit B hB d

end Gaussian
end SphericalAging.ActualAlgorithmTree
