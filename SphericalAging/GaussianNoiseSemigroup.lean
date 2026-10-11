module

public import SphericalAging.GaussianNoiseOperator

public section

/-! The Gaussian noise averaging semigroup is derived from actual
independent input mixtures, including both endpoint parameters. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianNoiseSemigroup
open Set MeasureTheory ProbabilityTheory GaussianNoiseSymmetry GaussianLinearMixtureLaw
  GaussianNoiseOperator
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem actual_operator_comp (a b : ℝ) (ha0 : 0≤a) (ha1 : a≤1)
    (hb0 : 0≤b) (hb1 : b≤1) (f : E→ℝ) (hf : Measurable f)
    (B : ℝ) (hB : ∀x,|f x|≤B) (x : E) :
    operator a (operator b f) x=operator (a*b) f x := by
  let sa := Real.sqrt (1-a^2)
  let sb := Real.sqrt (1-b^2)
  let c := Real.sqrt (1-(a*b)^2)
  have hab0 : 0≤a*b := mul_nonneg ha0 hb0
  have hab1 : a*b≤1 := by nlinarith
  have hsA : sa^2=1-a^2 := Real.sq_sqrt (by nlinarith)
  have hsB : sb^2=1-b^2 := Real.sq_sqrt (by nlinarith)
  have hsC : c^2=1-(a*b)^2 := Real.sq_sqrt (by nlinarith)
  have hv : (b*sa)^2+sb^2=c^2 := by rw [mul_pow,hsA,hsB,hsC];ring
  let g : E→ℝ := fun w => f ((a*b)•x+w)
  have hg : Measurable g := hf.comp ((measurable_const.add measurable_id))
  have hmp : MeasurePreserving (mixture (E:=E) (b*sa) sb)
      ((stdGaussian E).prod (stdGaussian E)) ((stdGaussian E).map (scale c)) :=
    ⟨(mixture (E:=E) (b*sa) sb).measurable,mixture_map_eq_scaled (b*sa) sb c hv⟩
  have hscale : MeasurePreserving (scale (E:=E) c) (stdGaussian E)
      ((stdGaussian E).map (scale c)) := ⟨(scale (E:=E) c).measurable,rfl⟩
  have he (z : E×E) : noise b (noise a x z.1) z.2=(a*b)•x+mixture (b*sa) sb z := by
    simp only [noise,mixture_apply]
    dsimp only [sa,sb]
    module
  have hm : Measurable (fun z : E×E => f (noise b (noise a x z.1) z.2)) := by
    simp_rw [he]
    exact hg.comp hmp.measurable
  have hi := signed_bounded_integrable ((stdGaussian E).prod (stdGaussian E)) _ hm B
    (fun z => hB _)
  change (∫y,∫z,f (noise b (noise a x y) z) ∂stdGaussian E ∂stdGaussian E)=_
  rw [←integral_prod _ hi]
  have hmixI := hmp.hasLaw.integral_comp hg.aestronglyMeasurable
  have hscaleI := hscale.hasLaw.integral_comp hg.aestronglyMeasurable
  calc
    _=(∫z : E×E,g (mixture (b*sa) sb z) ∂(stdGaussian E).prod (stdGaussian E)) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun z => congrArg f (he z))
    _=(∫w,g w ∂(stdGaussian E).map (scale c)) := hmixI
    _=(∫z,g (scale c z) ∂stdGaussian E) := hscaleI.symm
    _=operator (a*b) f x := rfl

end SphericalAging.GaussianNoiseSemigroup
