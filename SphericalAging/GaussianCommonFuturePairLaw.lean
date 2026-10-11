module

public import SphericalAging.GaussianLinearMixtureLaw
public import Mathlib.Analysis.InnerProductSpace.Dual

public section

/-! Two independent Gaussian futures after a common Gaussian past have
the literal Gaussian noise-pair law. The joint law is proved by genuine
characteristic functions of the three independent standard inputs. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace
namespace SphericalAging.GaussianCommonFuturePairLaw
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false

@[expose] def commonPair (a b : ℝ) : E×(E×E)→L[ℝ]E×E :=
  (a • ContinuousLinearMap.fst ℝ E (E×E)+
    b • (ContinuousLinearMap.fst ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E×E))).prod
  (a • ContinuousLinearMap.fst ℝ E (E×E)+
    b • (ContinuousLinearMap.snd ℝ E E).comp (ContinuousLinearMap.snd ℝ E (E×E)))

@[expose] def correlatedPair (a : ℝ) : E×E→L[ℝ]E×E :=
  (ContinuousLinearMap.fst ℝ E E).prod
    (a^2 • ContinuousLinearMap.fst ℝ E E+
      Real.sqrt (1-a^4) • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem commonPair_apply (a b : ℝ) (z : E×(E×E)) :
    commonPair a b z=(a•z.1+b•z.2.1,a•z.1+b•z.2.2) := rfl
@[simp] theorem correlatedPair_apply (a : ℝ) (z : E×E) :
    correlatedPair a z=(z.1,a^2•z.1+Real.sqrt (1-a^4)•z.2) := rfl

private theorem pair_dual_eval (L : StrongDual ℝ (E×E)) (x y : E) :
    L (x,y)=L (x,0)+L (0,y) := by
  simpa only [Prod.mk_add_mk,add_zero,zero_add] using L.map_add (x,0) (0,y)

theorem common_dual_past (a b : ℝ) (L : StrongDual ℝ (E×E)) :
    (L.comp (commonPair a b)).comp (ContinuousLinearMap.inl ℝ E (E×E))=
      a • (L.comp (ContinuousLinearMap.inl ℝ E E)+L.comp (ContinuousLinearMap.inr ℝ E E)) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,
    commonPair_apply,Prod.fst_zero,Prod.snd_zero,smul_zero,add_zero,
    ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply]
  rw [pair_dual_eval]
  rw [←Prod.smul_mk_zero,←Prod.smul_zero_mk,map_smul,map_smul]
  simp only [smul_eq_mul]
  ring

theorem common_dual_first (a b : ℝ) (L : StrongDual ℝ (E×E)) :
    ((L.comp (commonPair a b)).comp (ContinuousLinearMap.inr ℝ E (E×E))).comp
      (ContinuousLinearMap.inl ℝ E E)=b • L.comp (ContinuousLinearMap.inl ℝ E E) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,
    commonPair_apply,smul_zero,zero_add,add_zero,ContinuousLinearMap.smul_apply]
  simpa only [Prod.smul_mk_zero] using L.map_smul b (x,0)

theorem common_dual_second (a b : ℝ) (L : StrongDual ℝ (E×E)) :
    ((L.comp (commonPair a b)).comp (ContinuousLinearMap.inr ℝ E (E×E))).comp
      (ContinuousLinearMap.inr ℝ E E)=b • L.comp (ContinuousLinearMap.inr ℝ E E) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,
    commonPair_apply,smul_zero,zero_add,add_zero,ContinuousLinearMap.smul_apply]
  simpa only [Prod.smul_zero_mk] using L.map_smul b (0,x)

theorem correlated_dual_first (a : ℝ) (L : StrongDual ℝ (E×E)) :
    (L.comp (correlatedPair a)).comp (ContinuousLinearMap.inl ℝ E E)=
      L.comp (ContinuousLinearMap.inl ℝ E E)+a^2 • L.comp (ContinuousLinearMap.inr ℝ E E) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inl_apply,ContinuousLinearMap.inr_apply,correlatedPair_apply,
    smul_zero,add_zero,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply]
  rw [pair_dual_eval,←Prod.smul_zero_mk,map_smul]

theorem correlated_dual_second (a : ℝ) (L : StrongDual ℝ (E×E)) :
    (L.comp (correlatedPair a)).comp (ContinuousLinearMap.inr ℝ E E)=
      Real.sqrt (1-a^4) • L.comp (ContinuousLinearMap.inr ℝ E E) := by
  ext x
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.inr_apply,correlatedPair_apply,
    smul_zero,zero_add,ContinuousLinearMap.smul_apply]
  simpa only [Prod.smul_zero_mk] using L.map_smul (Real.sqrt (1-a^4)) (0,x)

theorem dual_norm_identity (a b c : ℝ) (hab : a^2+b^2=1) (hc : c^2=1-a^4)
    (L M : StrongDual ℝ E) :
    ‖a•(L+M)‖^2+‖b•L‖^2+‖b•M‖^2=‖L+a^2•M‖^2+‖c•M‖^2 := by
  let R := (InnerProductSpace.toDual ℝ E).symm
  simp only [GaussianLinearMixtureLaw.dual_scaled_norm_sq]
  have hs : ‖L+M‖^2=‖R L‖^2+2*inner ℝ (R L) (R M)+‖R M‖^2 := by
    rw [←R.norm_map (L+M),R.map_add,norm_add_sq_real]
  have ht : ‖L+a^2•M‖^2=‖R L‖^2+2*a^2*inner ℝ (R L) (R M)+a^4*‖R M‖^2 := by
    rw [←R.norm_map (L+a^2•M),R.map_add]
    have hsm : R (a^2•M)=a^2•R M := R.map_smul _ _
    rw [hsm,norm_add_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  rw [hs,ht,←R.norm_map L,←R.norm_map M]
  rw [hc]
  linear_combination (‖R L‖^2+‖R M‖^2)*(hab)

/-- Exact joint law of the two endpoints. Coefficients may have either
sign; their squared normalization supplies the covariance a². -/
theorem commonPair_map_eq_correlated (a b : ℝ) (hab : a^2+b^2=1) :
    ((stdGaussian E).prod ((stdGaussian E).prod (stdGaussian E))).map (commonPair a b)=
      ((stdGaussian E).prod (stdGaussian E)).map (correlatedPair a) := by
  have ha : a^2≤1 := by nlinarith [sq_nonneg b]
  have hc : (Real.sqrt (1-a^4))^2=1-a^4 := Real.sq_sqrt (by nlinarith [sq_nonneg a])
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map,charFunDual_prod,common_dual_past,charFunDual_prod,
    common_dual_first,common_dual_second,charFunDual_stdGaussian,charFunDual_stdGaussian,
    charFunDual_stdGaussian,charFunDual_map,charFunDual_prod,correlated_dual_first,
    correlated_dual_second,charFunDual_stdGaussian,charFunDual_stdGaussian,
    ←Complex.exp_add,←Complex.exp_add,←Complex.exp_add]
  congr 1
  norm_cast
  have hh := dual_norm_identity a b (Real.sqrt (1-a^4)) hab hc
    (L.comp (ContinuousLinearMap.inl ℝ E E)) (L.comp (ContinuousLinearMap.inr ℝ E E))
  linarith

/-- The same exact law, expressed as the literal endpoint functions. -/
theorem common_future_pair_map (a b : ℝ) (hab : a^2+b^2=1) :
    ((stdGaussian E).prod ((stdGaussian E).prod (stdGaussian E))).map
      (fun z : E×(E×E) => (a•z.1+b•z.2.1,a•z.1+b•z.2.2))=
      ((stdGaussian E).prod (stdGaussian E)).map
        (fun z : E×E => (z.1,a^2•z.1+Real.sqrt (1-a^4)•z.2)) :=
  commonPair_map_eq_correlated a b hab

theorem common_future_pair_hasLaw (a b : ℝ) (hab : a^2+b^2=1) :
    HasLaw (fun z : E×(E×E) => (a•z.1+b•z.2.1,a•z.1+b•z.2.2))
      (((stdGaussian E).prod (stdGaussian E)).map
        (fun z : E×E => (z.1,a^2•z.1+Real.sqrt (1-a^4)•z.2)))
      ((stdGaussian E).prod ((stdGaussian E).prod (stdGaussian E))) :=
  ⟨(commonPair (E:=E) a b).measurable.aemeasurable,common_future_pair_map a b hab⟩

/-- Common variance ρ yields endpoint correlation ρ, rather than sqrt ρ. -/
theorem common_variance_pair_map (ρ : ℝ) (hρ0 : 0≤ρ) (hρ1 : ρ≤1) :
    ((stdGaussian E).prod ((stdGaussian E).prod (stdGaussian E))).map
      (fun z : E×(E×E) =>
        (Real.sqrt ρ•z.1+Real.sqrt (1-ρ)•z.2.1,Real.sqrt ρ•z.1+Real.sqrt (1-ρ)•z.2.2))=
      ((stdGaussian E).prod (stdGaussian E)).map
        (fun z : E×E => (z.1,ρ•z.1+Real.sqrt (1-ρ^2)•z.2)) := by
  have ha2 := Real.sq_sqrt hρ0
  have hb2 := Real.sq_sqrt (sub_nonneg.mpr hρ1)
  have ha4 : (Real.sqrt ρ)^4=ρ^2 := by rw [show (4:ℕ)=2*2 by rfl,pow_mul,ha2]
  have he := common_future_pair_map (E:=E) (Real.sqrt ρ) (Real.sqrt (1-ρ)) (by linarith)
  simpa only [ha2,ha4] using he

theorem common_future_pair_of_inputs {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    (a b : ℝ) (hab : a^2+b^2=1) (S G₁ G₂ : Ω→E)
    (hinputs : HasLaw (fun ω => (S ω,G₁ ω,G₂ ω))
      ((stdGaussian E).prod ((stdGaussian E).prod (stdGaussian E))) μ) :
    HasLaw (fun ω => (a•S ω+b•G₁ ω,a•S ω+b•G₂ ω))
      (((stdGaussian E).prod (stdGaussian E)).map
        (fun z : E×E => (z.1,a^2•z.1+Real.sqrt (1-a^4)•z.2))) μ :=
  (common_future_pair_hasLaw a b hab).comp hinputs

end SphericalAging.GaussianCommonFuturePairLaw
