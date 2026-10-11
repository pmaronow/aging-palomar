module

public import SphericalAging.ResponsePrimitiveInterchange

public section

/-! Uniform convergence identifies response primitives even for merely
integrable finite-dimensional response rows. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.ResponsePrimitiveLimitIdentification
open ResponsePrimitiveInterchange
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

/-- Uniformly convergent integrable rows have convergent interval integrals.
No continuity of the approximating functions is needed. -/
theorem intervalIntegral_tendsto_of_uniform_integrable {ι : Type*} {l : Filter ι}
    {F : ι → ℝ → ℝ} {f : ℝ → ℝ} {a b : ℝ}
    (hF : ∀ᶠ i in l,IntervalIntegrable (F i) volume a b)
    (hf : IntervalIntegrable f volume a b)
    (hlim : TendstoUniformlyOn F f l (uIcc a b)) :
    Tendsto (fun i => ∫ v in a..b,F i v) l (𝓝 (∫ v in a..b,f v)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  let δ : ℝ := ε/(|b-a|+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  have hh := (Metric.tendstoUniformlyOn_iff.mp hlim) δ hδ
  filter_upwards [hh,hF] with i hi hFi
  rw [Real.dist_eq,← intervalIntegral.integral_sub hFi hf]
  have hb : |∫ v in a..b,F i v-f v|≤δ*|b-a| := by
    have hn := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := a) (b := b) (C := δ) (f := fun v => F i v-f v) (fun v hv => ?_)
    · simpa only [Real.norm_eq_abs] using hn
    · have hd := hi v (uIoc_subset_uIcc hv)
      rw [Real.dist_eq,abs_sub_comm] at hd
      exact hd.le
  refine hb.trans_lt ?_
  dsimp [δ]
  have hdpos : 0 < |b-a|+1 := by positivity
  rw [div_mul_eq_mul_div]
  apply (div_lt_iff₀ hdpos).2
  nlinarith [abs_nonneg (b-a)]

/-- The limit of true finite-dimensional prefixes is the prefix of the
uniform response limit, with no response equation used as a premise. -/
theorem primitive_eq_of_uniform_response_limit {ι : Type*} {l : Filter ι} [NeBot l]
    {Rn : ι → ℝ → ℝ → ℝ} {R : ℝ → ℝ → ℝ}
    {Gn : ι → ℝ → ℝ → ℝ} {G : ℝ → ℝ → ℝ} {t s : ℝ}
    (hRn : ∀ᶠ i in l,IntervalIntegrable (Rn i t) volume 0 (min t s))
    (hR : IntervalIntegrable (R t) volume 0 (min t s))
    (hRlim : TendstoUniformlyOn (fun i => Rn i t) (R t) l (uIcc 0 (min t s)))
    (hprimitive : ∀ᶠ i in l,Gn i t s=responsePrimitive (Rn i) t s)
    (hGlim : Tendsto (fun i => Gn i t s) l (𝓝 (G t s))) :
    G t s=responsePrimitive R t s := by
  have htend := intervalIntegral_tendsto_of_uniform_integrable hRn hR hRlim
  have he : (fun i => Gn i t s)=ᶠ[l]
      (fun i => ∫ v in (0 : ℝ)..min t s,Rn i t v) := hprimitive
  exact tendsto_nhds_unique hGlim (htend.congr' he.symm)

end SphericalAging.ResponsePrimitiveLimitIdentification
