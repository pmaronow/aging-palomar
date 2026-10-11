module

public import SphericalAging.DirichletIncrement

public section

/-! Exact exponential-coordinate conversion of the critical Dirichlet energy. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace SphericalAging.DirichletLogChange
open DirichletKernel DirichletIncrement

theorem exp_sum_cosh (x y : ℝ) :
    Real.exp x+Real.exp y=Real.exp ((x+y)/2)*(2*Real.cosh ((x-y)/2)) := by
  rw [Real.cosh_eq]
  symm
  calc
    _ = Real.exp ((x+y)/2)*Real.exp ((x-y)/2)+
        Real.exp ((x+y)/2)*Real.exp (-((x-y)/2)) := by ring
    _ = _ := by
      rw [←Real.exp_add,←Real.exp_add]
      congr 1 <;> congr 1 <;> ring

theorem exp_kernel_identity (a x y : ℝ) :
    Real.exp x*Real.exp y*Xi a (Real.exp x) (Real.exp y)=
      1/(2*Real.cosh ((x-y)/2))^(2-2*a) := by
  have hc : 0<2*Real.cosh ((x-y)/2) := by positivity
  have hp : Real.exp x*Real.exp y=Real.exp (x+y) := (Real.exp_add x y).symm
  unfold Xi
  rw [hp,exp_sum_cosh,Real.mul_rpow (Real.exp_pos _).le hc.le,
    Real.rpow_def_of_pos (Real.exp_pos (x+y)),Real.log_exp,
    Real.rpow_def_of_pos (Real.exp_pos ((x+y)/2)),Real.log_exp]
  have he : Real.exp (x+y)*Real.exp ((x+y)*(-a))=
      Real.exp (((x+y)/2)*(2-2*a)) := by
    rw [←Real.exp_add]
    congr 1
    ring
  calc
    _ = (Real.exp (x+y)*Real.exp ((x+y)*(-a))) /
        (Real.exp (((x+y)/2)*(2-2*a))*(2*Real.cosh ((x-y)/2))^(2-2*a)) := by ring
    _ = _ := by rw [he]; field_simp

theorem energyDensity_exp_identity (a : ℝ) (D : ℝ → ℝ) (x y : ℝ) :
    energyDensity a D (x,y)=Real.exp x*Real.exp y*
      (Xi a (Real.exp x) (Real.exp y)*(D (Real.log (Real.exp x))-D (Real.log (Real.exp y)))^2) := by
  simp only [Real.log_exp]
  unfold energyDensity
  rw [←mul_assoc,exp_kernel_identity]
  ring

theorem lintegral_exp_change (g : ℝ → ℝ≥0∞) :
    (∫⁻ x : ℝ,ENNReal.ofReal (Real.exp x)*g (Real.exp x))=
      ∫⁻ s in Ioi (0:ℝ),g s := by
  have hi := lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    Real.exp_injective.injOn g
  rw [Set.image_univ,Real.range_exp] at hi
  simpa only [Measure.restrict_univ,abs_of_pos (Real.exp_pos _)] using hi.symm

/-- Genuine nonnegative two-dimensional exponential Jacobian substitution. -/
theorem double_exponential_change (F : ℝ×ℝ → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ q : ℝ×ℝ,ENNReal.ofReal (Real.exp q.1)*ENNReal.ofReal (Real.exp q.2)*
      F (Real.exp q.1,Real.exp q.2) ∂(volume.prod volume))=
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),F q ∂(volume.prod volume) := by
  rw [lintegral_prod _ (by fun_prop),setLIntegral_prod F hF.aemeasurable]
  change (∫⁻ x : ℝ,∫⁻ y : ℝ,ENNReal.ofReal (Real.exp x)*ENNReal.ofReal (Real.exp y)*
      F (Real.exp x,Real.exp y))=∫⁻ s in Ioi (0:ℝ),∫⁻ t in Ioi (0:ℝ),F (s,t)
  calc
    _ = ∫⁻ x : ℝ,ENNReal.ofReal (Real.exp x)*(∫⁻ t in Ioi (0:ℝ),F (Real.exp x,t)) := by
      apply lintegral_congr
      intro x
      calc
        _ = ENNReal.ofReal (Real.exp x)*(∫⁻ y : ℝ,ENNReal.ofReal (Real.exp y)*
            F (Real.exp x,Real.exp y)) := by
          simp only [mul_assoc]
          exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ = _ := by rw [lintegral_exp_change (fun t => F (Real.exp x,t))]
    _ = _ := lintegral_exp_change (fun s => ∫⁻ t in Ioi (0:ℝ),F (s,t))

@[expose] def schurDensity (a : ℝ) (D : ℝ → ℝ) (q : ℝ×ℝ) : ℝ :=
  Xi a q.1 q.2*(D (Real.log q.1)-D (Real.log q.2))^2

theorem schurDensity_measurable {D : ℝ → ℝ} (hD : Measurable D) (a : ℝ) :
    Measurable (schurDensity a D) := by
  unfold schurDensity
  exact (Xi_measurable a).mul (((hD.comp (Real.measurable_log.comp measurable_fst)).sub
    (hD.comp (Real.measurable_log.comp measurable_snd))).pow_const 2)

/-- Exact equality of the actual logarithmic and positive-ray Schur energies. -/
theorem logarithmic_energy_eq_schur {a : ℝ} {D : ℝ → ℝ} (hD : Measurable D) :
    (∫⁻ q : ℝ×ℝ,ENNReal.ofReal (energyDensity a D q) ∂(volume.prod volume))=
      ∫⁻ q in Ioi (0:ℝ) ×ˢ Ioi (0:ℝ),ENNReal.ofReal (schurDensity a D q)
        ∂(volume.prod volume) := by
  rw [←double_exponential_change _ (schurDensity_measurable hD a).ennreal_ofReal]
  apply lintegral_congr
  intro q
  rw [energyDensity_exp_identity]
  unfold schurDensity
  rw [ENNReal.ofReal_mul (mul_pos (Real.exp_pos _) (Real.exp_pos _)).le,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

end SphericalAging.DirichletLogChange
