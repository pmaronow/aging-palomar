module

public import SphericalAging.FiniteDisclosurePast
public import SphericalAging.SumIntegral

public section

/-! Genuine finite-history Gaussian integration, obtained by induction
through every fresh and dependent branch. -/
noncomputable section
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureIntegral
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast SumIntegral SumMeasurePreserving

theorem actual_leaf_past_law (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ] :
    MeasurePreserving (past N p n r S) (leafLaw N p n r S P μ) (pastLaw N p n r S P μ) := by
  induction n generalizing r S with
  | zero => exact measurePreserving_fst (μ:=μ) (ν:=stdGaussian (Residual N p r))
  | succ n ih =>
    exact sum_map_preserving _ _ _ _
      (ih (r+1) (S×Block N p r) P.2.1 (freshLaw (p:=p) (r:=r) μ P.1.val))
      (ih r S P.2.2 (dependentLaw (r:=r) μ P.1.val))

theorem actual_finite_past_law (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ] :
    MeasurePreserving (past N p n r S∘execute N p n r S P)
      (μ.prod (stdGaussian (Residual N p r))) (pastLaw N p n r S P μ) :=
  (actual_leaf_past_law N p n r S P μ).comp (actual_finite_tree_law N p n r S P μ)

theorem leaf_integral_eq_past_average (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (μ : Measure S) [IsFiniteMeasure μ]
    {f : Leaves N p n r S→ℝ} (hf : StronglyMeasurable f) (C : ℝ) (hC : ∀z,‖f z‖≤C) :
    (∫z,f z ∂leafLaw N p n r S P μ)=
      ∫s,average N p n r S f s ∂pastLaw N p n r S P μ := by
  induction n generalizing r S with
  | zero =>
    exact integral_prod _ (Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC))
  | succ n ih =>
    let μF := freshLaw (p:=p) (r:=r) μ P.1.val
    let μD := dependentLaw (r:=r) μ P.1.val
    letI := leafLaw_finite N p n (r+1) (S×Block N p r) P.2.1 μF
    letI := leafLaw_finite N p n r S P.2.2 μD
    letI := pastLaw_finite N p n (r+1) (S×Block N p r) P.2.1 μF
    letI := pastLaw_finite N p n r S P.2.2 μD
    calc
      (∫z,f z ∂leafLaw N p (n+1) r S P μ)=
          (∫z,f (Sum.inl z) ∂leafLaw N p n (r+1) (S×Block N p r) P.2.1 μF)+
          (∫z,f (Sum.inr z) ∂leafLaw N p n r S P.2.2 μD) := integral_sum_law _ _ hf C hC
      _ = (∫s,average N p n (r+1) (S×Block N p r) (f∘Sum.inl) s
          ∂pastLaw N p n (r+1) (S×Block N p r) P.2.1 μF)+
          (∫s,average N p n r S (f∘Sum.inr) s ∂pastLaw N p n r S P.2.2 μD) :=
        congrArg₂ (fun a b : ℝ => a+b)
          (ih (r+1) (S×Block N p r) P.2.1 μF (hf.comp_measurable measurable_inl)
            (fun z => hC (Sum.inl z)))
          (ih r S P.2.2 μD (hf.comp_measurable measurable_inr) (fun z => hC (Sum.inr z)))
      _ = ∫s,average N p (n+1) r S f s ∂pastLaw N p (n+1) r S P μ :=
        (integral_sum_law _ _ (average_stronglyMeasurable N p (n+1) r S hf) C
          (average_norm_le N p (n+1) r S f C hC)).symm

end SphericalAging.FiniteDisclosureIntegral
