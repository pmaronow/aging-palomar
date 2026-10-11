module

public import SphericalAging.CanonicalGramFlag
public import SphericalAging.PredictableTensorRankBranch
public import SphericalAging.SumMeasurePreserving

public section

/-! A finite adaptive disclosure tree with an actual fresh/dependent
branch at each query. Its leaves retain a literal canonical Gaussian
residual tensor, including random ranks and saturated ranks. -/
noncomputable section
set_option maxHeartbeats 500000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureTree
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open CanonicalVectorSpan CanonicalGramSelector CanonicalGramFlag
open PredictableTensorDisclosureStep PredictableTensorCanonicalRegeneration
open PredictableTensorRankBranch BranchMeasurePreserving SumMeasurePreserving

@[expose] abbrev Residual (N p r : ℕ) := residualTensorSpace (p:=p) (space N r)
@[expose] abbrev Block (N p r : ℕ) := freshBlock (p:=p) (space N r) (direction N r)

@[expose] def Leaves (N p : ℕ) : (n r : ℕ)→Type→Type
  | 0,r,S => S×Residual N p r
  | n+1,r,S => Leaves N p n (r+1) (S×Block N p r)⊕Leaves N p n r S

instance leavesMeasurable (N p n r : ℕ) (S : Type) [MeasurableSpace S] :
    MeasurableSpace (Leaves N p n r S) := by
  induction n generalizing r S with
  | zero => exact inferInstanceAs (MeasurableSpace (S×Residual N p r))
  | succ n ih =>
    letI := ih (r+1) (S×Block N p r)
    letI := ih r S
    exact inferInstanceAs (MeasurableSpace (Leaves N p n (r+1) (S×Block N p r)⊕Leaves N p n r S))

@[expose] def Plan (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S], Type
  | 0,_,_,_ => Unit
  | n+1,r,S,_ => {x : S→Vector N // Measurable x}×
      Plan N p n (r+1) (S×Block N p r)×Plan N p n r S

@[expose] def nextResidual {N p r : ℕ} {S : Type} (x : S→Vector N)
    (z : S×Residual N p r) : Residual N p (r+1) :=
  (LinearIsometryEquiv.ofEq _ _ (congrArg (residualTensorSpace (p:=p)) (space_next N r).symm))
    (canonicalRemaining (p:=p) (space N r) (direction N r)
      (direction_mem_orthogonal N r) x z)

@[expose] def step {N p r : ℕ} {S : Type} (x : S→Vector N) :
    S×Residual N p r→((S×Block N p r)×Residual N p (r+1))⊕(S×Residual N p r) :=
  branchMap {z | x z.1∉space N r}
    (fun z => (history (p:=p) (space N r) (direction N r)
      (direction_mem_orthogonal N r) x z,nextResidual x z)) id

@[expose] abbrev freshLaw {N p r : ℕ} {S : Type} [MeasurableSpace S]
    (μ : Measure S) (x : S→Vector N) : Measure (S×Block N p r) :=
  (μ.restrict {s | x s∉space N r}).prod (stdGaussian (Block N p r))

@[expose] abbrev dependentLaw {N r : ℕ} {S : Type} [MeasurableSpace S]
    (μ : Measure S) (x : S→Vector N) : Measure S :=
  μ.restrict {s | x s∈space N r}

theorem actual_step_law {N p r : ℕ} {S : Type} [MeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {x : S→Vector N} (hx : Measurable x) :
    MeasurePreserving (step (p:=p) (r:=r) x)
      (μ.prod (stdGaussian (Residual N p r)))
      (((freshLaw (p:=p) (r:=r) μ x).prod (stdGaussian (Residual N p (r+1)))).map Sum.inl+
        ((dependentLaw (r:=r) μ x).prod (stdGaussian (Residual N p r))).map Sum.inr) := by
  let E : residualTensorSpace (p:=p) (space N r⊔ℝ ∙ direction N r)≃ₗᵢ[ℝ]Residual N p (r+1) :=
    LinearIsometryEquiv.ofEq _ _ (congrArg (residualTensorSpace (p:=p)) (space_next N r).symm)
  have hE : MeasurePreserving E
      (stdGaussian (residualTensorSpace (p:=p) (space N r⊔ℝ ∙ direction N r)))
      (stdGaussian (Residual N p (r+1))) :=
    ⟨E.continuous.measurable,stdGaussian_map E⟩
  have hf := (MeasurePreserving.id (freshLaw (p:=p) (r:=r) μ x)).prod hE
  have hi := MeasurePreserving.id ((dependentLaw (r:=r) μ x).prod (stdGaussian (Residual N p r)))
  have hs := sum_map_preserving _ _ _ _ hf hi
  have hb := actual_rank_branch_law (p:=p) μ (space N r) (direction N r)
    (direction_mem_orthogonal N r) hx
  have hcomp := hs.comp hb
  convert hcomp using 1
  funext z
  classical
  by_cases hz : x z.1∈space N r <;> simp [step,branchMap,hz,nextResidual,E]

@[expose] def execute (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→(S×Residual N p r)→Leaves N p n r S
  | 0,_,_,_,_,z => z
  | n+1,r,S,_,P,z =>
    Sum.map (execute N p n (r+1) (S×Block N p r) P.2.1)
      (execute N p n r S P.2.2) (step P.1.val z)

@[expose] def leafLaw (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→Measure S→Measure (Leaves N p n r S)
  | 0,r,_,_,_,μ => μ.prod (stdGaussian (Residual N p r))
  | n+1,r,S,_,P,μ =>
    (leafLaw N p n (r+1) (S×Block N p r) P.2.1 (freshLaw (p:=p) (r:=r) μ P.1.val)).map Sum.inl+
      (leafLaw N p n r S P.2.2 (dependentLaw (r:=r) μ P.1.val)).map Sum.inr

theorem actual_finite_tree_law (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ] :
    MeasurePreserving (execute N p n r S P)
      (μ.prod (stdGaussian (Residual N p r))) (leafLaw N p n r S P μ) := by
  induction n generalizing r S with
  | zero => exact MeasurePreserving.id _
  | succ n ih =>
    have hF := ih (r+1) (S×Block N p r) P.2.1 (freshLaw (p:=p) (r:=r) μ P.1.val)
    have hD := ih r S P.2.2 (dependentLaw (r:=r) μ P.1.val)
    exact (sum_map_preserving _ _ _ _ hF hD).comp (actual_step_law μ P.1.property)

end SphericalAging.FiniteDisclosureTree
