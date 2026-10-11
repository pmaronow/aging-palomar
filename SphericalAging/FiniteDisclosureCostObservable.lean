module

public import SphericalAging.FiniteDisclosureResidualCost
public import SphericalAging.FiniteDisclosureExactHistory

public section

/-! The residual field-cost leaf observable is the literal original-disorder
cost, and is genuinely measurable from the constructed tree. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.FiniteDisclosureCostObservable
open Set Filter MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open FiniteDisclosureTree FiniteDisclosurePast FiniteDisclosurePhysicalState FiniteDisclosureResidual
open FiniteDisclosureDisclosed FiniteDisclosureSeedHistory FiniteDisclosureResidualCost
open FiniteDisclosureMeasurableState FiniteDisclosureGradientState FiniteDisclosureSpaceMeasurable
open FiniteDisclosureAmbient ResidualOriginalEnergy TensorActionComposition
open ExternalFieldSharpScalar SphereGibbsEntropy
open scoped InnerProductSpace

 theorem value_eq_original (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N) (D : S→TensorSpace N p)
    (A : S→TensorSpace N p→Vector N) (u : Past N p n r S→Vector N) (z : Leaves N p n r S) :
    FiniteDisclosureResidualCost.value N p n r S P F D A u z=
      Hamiltonian N p (decode N p n r S P F D z).ofLp
        ((physicalSpace N p n r S P F (past N p n r S z))ᗮ.starProjection
          (A (seed N p n r S (past N p n r S z)) (decode N p n r S P F D z)))/(N:ℝ)+
      betaD p*|⟪u (past N p n r S z),
        A (seed N p n r S (past N p n r S z)) (decode N p n r S P F D z)⟫_ℝ/Real.sqrt (N:ℝ)|^p := by
  induction n generalizing r S with
  | zero =>
    simp only [FiniteDisclosureResidualCost.value,decode,past,physicalSpace,seed,physicalProjection_eq]
  | succ n ih =>
    cases z with
    | inl z =>
      simpa only [FiniteDisclosureResidualCost.value,Sum.elim_inl,decode,past,Sum.map_inl,physicalSpace,seed,
        Function.comp_def] using ih (r+1) (S×Block N p r) P.2.1
          (freshFrame P.1.val F) (freshDisclosed P.1.val D) (fun s => A s.1) (u∘Sum.inl) z
    | inr z =>
      simpa only [FiniteDisclosureResidualCost.value,Sum.elim_inr,decode,past,Sum.map_inr,physicalSpace,seed,
        Function.comp_def] using ih r S P.2.2 F D A (u∘Sum.inr) z

 theorem decode_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    (D : S→TensorSpace N p) (hD : Measurable D) :
    Measurable (decode N p n r S P F D) := by
  have hd := (physicalDisclosed_measurable N p n r S P F hF hD).comp (past_measurable N p n r S)
  have hr := physicalResidual_measurable N p n r S P F hF
  have he := funext (actual_disorder_decomposition N p n r S P F D)
  rw [he]
  exact hd.add hr

 theorem value_measurable (N p n r : ℕ) (S : Type) [MeasurableSpace S]
    (P : Plan N p n r S) (F : S→Frame N)
    (hF : Measurable (fun z : S×Vector N => F z.1 z.2))
    (D : S→TensorSpace N p) (hD : Measurable D)
    (A : S→TensorSpace N p→Vector N) (hA : Measurable (Function.uncurry A))
    (u : Past N p n r S→Vector N) (hu : Measurable u) :
    Measurable (FiniteDisclosureResidualCost.value N p n r S P F D A u) := by
  have hd := decode_measurable N p n r S P F hF D hD
  have hs := (seed_measurable N p n r S).comp (past_measurable N p n r S)
  have harg := hs.prodMk hd
  have hao : Measurable (fun z => A (seed N p n r S (past N p n r S z)) (decode N p n r S P F D z)) :=
    hA.comp harg
  have hproj := (physicalSpace_projection_measurable N p n r S P F hF).comp
    ((past_measurable N p n r S).prodMk hao)
  have hperp : Measurable (fun z => (physicalSpace N p n r S P F (past N p n r S z))ᗮ.starProjection
      (A (seed N p n r S (past N p n r S z)) (decode N p n r S P F D z))) := by
    convert hao.sub hproj using 1
    funext z
    exact Submodule.starProjection_orthogonal_val _
  have hdis := (PiLp.continuous_ofLp 2 (fun _ : TensorIndex N p => ℝ)).measurable.comp hd
  have he := ((Hamiltonian_joint_continuous N p).measurable.comp (hdis.prodMk hperp)).div_const (N:ℝ)
  have hi := ((continuous_fst.inner continuous_snd : Continuous (fun z : Vector N×Vector N => ⟪z.1,z.2⟫_ℝ)).measurable.comp
    ((hu.comp (past_measurable N p n r S)).prodMk hao)).div_const (Real.sqrt (N:ℝ))
  have hm := he.add (((continuous_abs.measurable.comp hi).pow_const p).const_mul (betaD p))
  have heq := funext (value_eq_original N p n r S P F D A u)
  rw [heq]
  exact hm

 theorem actual_value {N p n : ℕ} {S : Type} [MeasurableSpace S]
    (P : Plan N p n 0 S) (A : S→TensorSpace N p→Vector N)
    (u : Past N p n 0 S→Vector N) (z : S×TensorSpace N p) :
    FiniteDisclosureResidualCost.value N p n 0 S P (initialFrame N S) (fun _ => 0) A u
      (execute N p n 0 S P (initialState z))=
      Hamiltonian N p z.2.ofLp ((actualSpace P z)ᗮ.starProjection (A z.1 z.2))/(N:ℝ)+
        betaD p*|⟪u (actualHistory P z),A z.1 z.2⟫_ℝ/Real.sqrt (N:ℝ)|^p := by
  rw [value_eq_original,actual_disorder_preserved,actual_original_seed]
  simp only [initialState,initialFrame,zero_add,initialIso_coe,action_refl,actualSpace,actualHistory,Function.comp_def]

end SphericalAging.FiniteDisclosureCostObservable
