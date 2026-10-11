module

public import SphericalAging.FiniteDisclosureTree

public section

/-! The actual disclosed past of a finite random-rank tree and its
Gaussian integration kernel. Every leaf law is derived from the actual
fresh/dependent history transformation. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosurePast
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree

@[expose] def Past (N p : ℕ) : (n r : ℕ)→Type→Type
  | 0,_,S => S
  | n+1,r,S => Past N p n (r+1) (S×Block N p r)⊕Past N p n r S

instance pastMeasurable (N p n r : ℕ) (S : Type) [MeasurableSpace S] :
    MeasurableSpace (Past N p n r S) := by
  induction n generalizing r S with
  | zero => exact inferInstanceAs (MeasurableSpace S)
  | succ n ih =>
    letI := ih (r+1) (S×Block N p r)
    letI := ih r S
    exact inferInstanceAs (MeasurableSpace (Past N p n (r+1) (S×Block N p r)⊕Past N p n r S))

@[expose] def past (N p : ℕ) : ∀(n r : ℕ) (S : Type), Leaves N p n r S→Past N p n r S
  | 0,_,_,z => z.1
  | n+1,r,S,z => Sum.map (past N p n (r+1) (S×Block N p r)) (past N p n r S) z

theorem past_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S] :
    Measurable (past N p n r S) := by
  induction n generalizing r S with
  | zero => exact measurable_fst
  | succ n ih => exact (ih (r+1) (S×Block N p r)).sumMap (ih r S)

@[expose] def pastLaw (N p : ℕ) : ∀(n r : ℕ) (S : Type) [MeasurableSpace S],
    Plan N p n r S→Measure S→Measure (Past N p n r S)
  | 0,_,_,_,_,μ => μ
  | n+1,r,S,_,P,μ =>
    (pastLaw N p n (r+1) (S×Block N p r) P.2.1 (freshLaw (p:=p) (r:=r) μ P.1.val)).map Sum.inl+
      (pastLaw N p n r S P.2.2 (dependentLaw (r:=r) μ P.1.val)).map Sum.inr

theorem leafLaw_finite (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (leafLaw N p n r S P μ) := by
  induction n generalizing r S with
  | zero =>
    change IsFiniteMeasure (μ.prod (stdGaussian (Residual N p r)))
    exact inferInstance
  | succ n ih =>
    letI := ih (r+1) (S×Block N p r) P.2.1 (freshLaw (p:=p) (r:=r) μ P.1.val)
    letI := ih r S P.2.2 (dependentLaw (r:=r) μ P.1.val)
    change IsFiniteMeasure ((leafLaw N p n (r+1) (S×Block N p r) P.2.1
      (freshLaw (p:=p) (r:=r) μ P.1.val)).map Sum.inl+
      (leafLaw N p n r S P.2.2 (dependentLaw (r:=r) μ P.1.val)).map Sum.inr)
    exact inferInstance

theorem pastLaw_finite (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ] :
    IsFiniteMeasure (pastLaw N p n r S P μ) := by
  induction n generalizing r S with
  | zero =>
    change IsFiniteMeasure μ
    exact inferInstance
  | succ n ih =>
    letI := ih (r+1) (S×Block N p r) P.2.1 (freshLaw (p:=p) (r:=r) μ P.1.val)
    letI := ih r S P.2.2 (dependentLaw (r:=r) μ P.1.val)
    change IsFiniteMeasure ((pastLaw N p n (r+1) (S×Block N p r) P.2.1
      (freshLaw (p:=p) (r:=r) μ P.1.val)).map Sum.inl+
      (pastLaw N p n r S P.2.2 (dependentLaw (r:=r) μ P.1.val)).map Sum.inr)
    exact inferInstance

@[expose] def average (N p : ℕ) : ∀(n r : ℕ) (S : Type),
    (Leaves N p n r S→ℝ)→Past N p n r S→ℝ
  | 0,r,_,f,s => ∫J,f (s,J) ∂stdGaussian (Residual N p r)
  | n+1,r,S,f,z =>
    Sum.elim (average N p n (r+1) (S×Block N p r) (f∘Sum.inl))
      (average N p n r S (f∘Sum.inr)) z

theorem average_stronglyMeasurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f) :
    StronglyMeasurable (average N p n r S f) := by
  induction n generalizing r S with
  | zero => exact hf.integral_prod_right'
  | succ n ih =>
    exact ((ih (r+1) (S×Block N p r) (hf.comp_measurable measurable_inl)).measurable.sumElim
      (ih r S (hf.comp_measurable measurable_inr)).measurable).stronglyMeasurable

theorem average_norm_le (N p n r : ℕ) (S : Type) (f : Leaves N p n r S→ℝ)
    (C : ℝ) (hC : ∀z,‖f z‖≤C) (s : Past N p n r S) :
    ‖average N p n r S f s‖≤C := by
  induction n generalizing r S with
  | zero =>
    simpa only [average,probReal_univ,mul_one] using
      norm_integral_le_of_norm_le_const (μ:=stdGaussian (Residual N p r))
        (ae_of_all _ (fun J => hC (s,J)))
  | succ n ih =>
    cases s with
    | inl s => exact ih (r+1) (S×Block N p r) (f∘Sum.inl) (fun z => hC (Sum.inl z)) s
    | inr s => exact ih r S (f∘Sum.inr) (fun z => hC (Sum.inr z)) s

end SphericalAging.FiniteDisclosurePast
