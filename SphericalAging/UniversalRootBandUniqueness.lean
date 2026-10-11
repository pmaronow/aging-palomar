module

public import SphericalAging.UniversalRootBandMeasure

public section

/-! The nonnegative universal max-kernel is uniquely forced by the actual
squared-mass pushforward law, rather than by a pointwise normalization premise. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal
namespace SphericalAging.UniversalRootBandUniqueness
open UniversalRootInterval UniversalRootKernel UniversalRootBandMeasure
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

@[expose] def weight (x : ℝ) : ℝ := (Real.sqrt (2*x))⁻¹

@[expose] def squaredBandMass (g : ℝ→ℝ) : Measure ℝ :=
  ((unitMeasure.prod unitMeasure).withDensity (fun z => ENNReal.ofReal ((g (band z))^2))).map band

 theorem squaredBandMass_eq_density {g : ℝ→ℝ} (hg : Measurable g) :
    squaredBandMass g=unitMeasure.withDensity (fun x => bandDensity x*ENNReal.ofReal ((g x)^2)) := by
  have hs : Measurable (fun x => ENNReal.ofReal ((g x)^2)) := (hg.pow_const 2).ennreal_ofReal
  change ((unitMeasure.prod unitMeasure).withDensity ((fun x => ENNReal.ofReal ((g x)^2))∘band)).map band=_
  rw [map_withDensity_comp _ band_measurable hs]
  change bandLaw.withDensity (fun x => ENNReal.ofReal ((g x)^2))=_
  rw [bandLaw_eq_density,←withDensity_mul _ bandDensity_measurable hs]
  rfl

 theorem weight_measurable : Measurable weight :=
  (measurable_const.mul measurable_id).sqrt.inv

 theorem weight_nonneg (x : ℝ) : 0≤weight x := inv_nonneg.mpr (Real.sqrt_nonneg _)

 theorem weight_normalization {x : ℝ} (hx : 0<x) : 2*x*(weight x)^2=1 := by
  have hn : 2*x≠0 := by positivity
  rw [weight,inv_pow,Real.sq_sqrt (by positivity : 0≤2*x),mul_inv_cancel₀ hn]

 theorem weight_squaredBandMass : squaredBandMass weight=unitMeasure := by
  rw [squaredBandMass_eq_density weight_measurable]
  have hh : (fun x => bandDensity x*ENNReal.ofReal ((weight x)^2))=ᵐ[unitMeasure] fun _ => 1 := by
    filter_upwards [unit_ae] with x hx
    rw [bandDensity,←ENNReal.ofReal_mul (mul_nonneg (by norm_num) hx.1.le),weight_normalization hx.1]
    norm_num
  rw [withDensity_congr_ae hh]
  change unitMeasure.withDensity (1 : ℝ→ℝ≥0∞)=unitMeasure
  exact withDensity_one

/-- Uniqueness up to unit-interval null sets from the literal law giving
uniform squared root mass to every measurable cumulative-mass band. -/
 theorem weight_unique {g : ℝ→ℝ} (hg : Measurable g) (hn : 0≤ᵐ[unitMeasure] g)
    (hMass : squaredBandMass g=unitMeasure) : g=ᵐ[unitMeasure] weight := by
  have hs : Measurable (fun x => ENNReal.ofReal ((g x)^2)) := (hg.pow_const 2).ennreal_ofReal
  have hD : unitMeasure.withDensity (fun x => bandDensity x*ENNReal.ofReal ((g x)^2))=
      unitMeasure.withDensity (fun _ => 1) := by
    rw [←squaredBandMass_eq_density hg,hMass]
    change unitMeasure=unitMeasure.withDensity (1 : ℝ→ℝ≥0∞)
    exact withDensity_one.symm
  have ha := (withDensity_eq_iff_of_sigmaFinite (bandDensity_measurable.mul hs).aemeasurable
    measurable_const.aemeasurable).mp hD
  filter_upwards [unit_ae,hn,ha] with x hx hn he
  change 0≤g x at hn
  have hp : 0≤2*x := mul_nonneg (by norm_num) hx.1.le
  change bandDensity x*ENNReal.ofReal ((g x)^2)=1 at he
  rw [bandDensity,←ENNReal.ofReal_mul hp] at he
  have hre := congrArg ENNReal.toReal he
  have hnorm : 2*x*(g x)^2=1 := by
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hp (sq_nonneg _)),ENNReal.toReal_one] using hre
  have hw := weight_normalization hx.1
  have heq : (g x)^2=(weight x)^2 := mul_left_cancel₀
    (mul_ne_zero (by norm_num : (2:ℝ)≠0) hx.1.ne') (hnorm.trans hw.symm)
  exact (sq_eq_sq₀ hn (weight_nonneg x)).mp heq

 theorem max_kernel_unique {g : ℝ→ℝ} (hg : Measurable g) (hn : 0≤ᵐ[unitMeasure] g)
    (hMass : squaredBandMass g=unitMeasure) :
    (fun z : ℝ×ℝ => g (max z.1 z.2))=ᵐ[unitMeasure.prod unitMeasure] kernel := by
  have he := weight_unique hg hn hMass
  have hA : bandLaw≪unitMeasure := by rw [bandLaw_eq_density];exact withDensity_absolutelyContinuous _ _
  have he' : g=ᵐ[bandLaw] weight := hA.ae_eq he
  exact (ae_of_ae_map band_measurable.aemeasurable he').mono (fun z hz => hz)

end SphericalAging.UniversalRootBandUniqueness
