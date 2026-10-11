module

public import Mathlib.Probability.Distributions.Gaussian.Multivariate

public section

/-! Literal independent standard Gaussian coordinates form the standard
Gaussian on their finite Hilbert direct sum. -/
noncomputable section
namespace SphericalAging.GaussianPiLpLaw
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {ι : Type*} [Fintype ι] {E : ι→Type*}
  [∀i,NormedAddCommGroup (E i)] [∀i,InnerProductSpace ℝ (E i)]
  [∀i,FiniteDimensional ℝ (E i)] [∀i,MeasurableSpace (E i)] [∀i,BorelSpace (E i)]

theorem map_pi_stdGaussian :
    (Measure.pi (fun i => stdGaussian (E i))).map (WithLp.toLp 2)=stdGaussian (PiLp 2 E) := by
  apply Measure.ext_of_charFun
  ext t
  simp_rw [charFun_pi,charFun_stdGaussian,←Complex.exp_sum]
  simp_rw [←Complex.ofReal_pow]
  rw [PiLp.norm_sq_eq_of_L2]
  congr 1
  simp only [Complex.ofReal_sum,Complex.ofReal_pow]
  rw [←Finset.sum_div,←Finset.sum_neg_distrib]

theorem pi_toLp_hasLaw :
    HasLaw (WithLp.toLp 2) (stdGaussian (PiLp 2 E)) (Measure.pi (fun i => stdGaussian (E i))) :=
  ⟨(PiLp.continuous_toLp 2 E).measurable.aemeasurable,map_pi_stdGaussian⟩

end SphericalAging.GaussianPiLpLaw
