module

public import SphericalAging.GaussianNoiseSemigroup
public import SphericalAging.GaussianNoiseContraction

public section

/-! Positive and monotone actual Gaussian noise stability of a bounded
measurable observable. The argument uses the derived noise semigroup,
its symmetric coupling, and its true L2 contraction. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianNoiseCorrelation
open Set MeasureTheory ProbabilityTheory GaussianNoiseSymmetry GaussianNoiseOperator
  GaussianNoiseSemigroup GaussianNoiseContraction GaussianLinearMixtureLaw
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

@[expose] def stability (ρ : ℝ) (f : E→ℝ) : ℝ := ∫x,f x*operator ρ f x ∂stdGaussian E

theorem operator_selfadjoint (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1)
    (f g : E→ℝ) (hf : Measurable f) (hg : Measurable g)
    (Bf Bg : ℝ) (hBf : ∀x,|f x|≤Bf) (hBg : ∀x,|g x|≤Bg) :
    (∫x,f x*operator ρ g x ∂stdGaussian E)=
      ∫x,g x*operator ρ f x ∂stdGaussian E := by
  have hn : Measurable (fun z : E×E => noise ρ z.1 z.2) :=
    (mixture (E:=E) ρ (Real.sqrt (1-ρ^2))).measurable
  have hm : Measurable (fun z : E×E => f z.1*g (noise ρ z.1 z.2)) :=
    (hf.comp measurable_fst).mul (hg.comp hn)
  have hm' : Measurable (fun z : E×E => g z.1*f (noise ρ z.1 z.2)) :=
    (hg.comp measurable_fst).mul (hf.comp hn)
  have hBf0 : 0≤Bf := (abs_nonneg (f 0)).trans (hBf 0)
  have hBg0 : 0≤Bg := (abs_nonneg (g 0)).trans (hBg 0)
  have hi := signed_bounded_integrable ((stdGaussian E).prod (stdGaussian E)) _ hm (Bf*Bg)
    (fun z => by rw [abs_mul];exact mul_le_mul (hBf _) (hBg _) (abs_nonneg _) hBf0)
  have hi' := signed_bounded_integrable ((stdGaussian E).prod (stdGaussian E)) _ hm' (Bg*Bf)
    (fun z => by rw [abs_mul];exact mul_le_mul (hBg _) (hBf _) (abs_nonneg _) hBg0)
  have hs := actual_noise_pair_integral_swap ρ h0 h1 (fun z : E×E => f z.1*g z.2) hi
  change (∫z : E×E,f z.1*g (noise ρ z.1 z.2) ∂(stdGaussian E).prod (stdGaussian E))=
    ∫z : E×E,f (noise ρ z.1 z.2)*g z.1 ∂(stdGaussian E).prod (stdGaussian E) at hs
  have he : (fun z : E×E => f (noise ρ z.1 z.2)*g z.1)=
      (fun z : E×E => g z.1*f (noise ρ z.1 z.2)) := funext (fun z => mul_comm _ _)
  rw [he] at hs
  rw [integral_prod _ hi] at hs
  rw [integral_prod _ hi'] at hs
  simp_rw [integral_const_mul] at hs
  exact hs

theorem stability_square (t : ℝ) (h0 : 0≤t) (h1 : t≤1)
    (f : E→ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀x,|f x|≤B) :
    stability (t*t) f=∫x,(operator t f x)^2 ∂stdGaussian E := by
  have hm := operator_measurable t f hf
  have hb := operator_abs_bound t f hf B hB
  have hs := operator_selfadjoint t h0 h1 f (operator t f) hf hm B B hB hb
  simp_rw [actual_operator_comp t t h0 h1 h0 h1 f hf B hB] at hs
  simpa only [stability,←pow_two] using hs

theorem stability_nonneg (ρ : ℝ) (h0 : 0≤ρ) (h1 : ρ≤1)
    (f : E→ℝ) (hf : Measurable f) (B : ℝ) (hB : ∀x,|f x|≤B) : 0≤stability ρ f := by
  have hs1 : Real.sqrt ρ≤1 := Real.sqrt_le_one.mpr h1
  have hh := stability_square (Real.sqrt ρ) (Real.sqrt_nonneg _) hs1 f hf B hB
  rw [Real.mul_self_sqrt h0] at hh
  rw [hh]
  exact integral_nonneg (fun x => sq_nonneg _)

theorem stability_monotone (f : E→ℝ) (hf : Measurable f) (B : ℝ)
    (hB : ∀x,|f x|≤B) : MonotoneOn (fun ρ => stability ρ f) (Set.Icc 0 1) := by
  intro ρ hρ σ hσ hρσ
  by_cases hσ0 : σ=0
  · have hρ0 : ρ=0 := by rw [hσ0] at hρσ;linarith [hρ.1]
    rw [hσ0,hρ0]
  · have hspos : 0<Real.sqrt σ := Real.sqrt_pos.mpr (lt_of_le_of_ne hσ.1 (Ne.symm hσ0))
    let t := Real.sqrt ρ
    let u := Real.sqrt σ
    let k := t/u
    have ht0 : 0≤t := Real.sqrt_nonneg _
    have hu0 : 0≤u := Real.sqrt_nonneg _
    have ht1 : t≤1 := Real.sqrt_le_one.mpr hρ.2
    have hu1 : u≤1 := Real.sqrt_le_one.mpr hσ.2
    have hk0 : 0≤k := div_nonneg ht0 hu0
    have hk1 : k≤1 := (div_le_one hspos).mpr (Real.sqrt_le_sqrt hρσ)
    have hku : k*u=t := div_mul_cancel₀ _ hspos.ne'
    have hh := operator_L2_contraction k hk0 hk1 (operator u f)
      (operator_measurable u f hf) B ((abs_nonneg (f 0)).trans (hB 0))
      (operator_abs_bound u f hf B hB)
    simp_rw [actual_operator_comp k u hk0 hk1 hu0 hu1 f hf B hB,hku] at hh
    have ht := stability_square t ht0 ht1 f hf B hB
    have hu := stability_square u hu0 hu1 f hf B hB
    rw [show t*t=ρ from Real.mul_self_sqrt hρ.1] at ht
    rw [show u*u=σ from Real.mul_self_sqrt hσ.1] at hu
    rwa [←ht,←hu] at hh

end SphericalAging.GaussianNoiseCorrelation
