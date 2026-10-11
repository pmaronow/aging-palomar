module

public import SphericalAging.VectorSourceFourthMoment

public section

/-! Literal quartic generator algebra for an actual vector drift/noise
with arbitrary source amplitudes. These are pointwise inequalities, not
moment or higher differentiability assumptions. -/
noncomputable section
open MeasureTheory
open scoped BigOperators NNReal InnerProductSpace
namespace SphericalAging.VectorQuarticSourceBound
open HardSphereDynamics VectorSourceFourthMoment
variable {N : ℕ}

lemma quartic_young (a b : ℝ) (ha : 0≤a) (hb : 0≤b) :
    4*a^3*b≤3*a^4+b^4 := by
  have hh : 0≤(a-b)^2*(3*a^2+2*a*b+b^2) := mul_nonneg (sq_nonneg _) (by positivity)
  nlinarith only [hh]

theorem radial_noise_le_trace (x : State N) (b : Fin N→Fin N→ℝ) :
    (∑j : Fin N,(∑i : Fin N,2*x i*b i j)^2)≤
      4*‖x‖^2*(∑i : Fin N,∑j : Fin N,(b i j)^2) := by
  have hcol (j : Fin N) : (∑i : Fin N,2*x i*b i j)^2≤4*‖x‖^2*(∑i : Fin N,(b i j)^2) := by
    let v : State N := WithLp.toLp 2 (fun i => b i j)
    have hi : (∑i : Fin N,2*x i*b i j)=2*inner ℝ x v := by
      simp only [v,PiLp.inner_apply,RCLike.inner_apply,PiLp.toLp_apply,starRingEnd_apply,star_trivial]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    have hv : (∑i : Fin N,(b i j)^2)=‖v‖^2 := by
      simpa only [v,PiLp.toLp_apply,real_inner_self_eq_norm_sq] using coordinate_square_sum v
    have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm (𝕜:=ℝ) x v) 2
    simp only [Real.norm_eq_abs,sq_abs,mul_pow] at hh
    rw [hi,hv]
    nlinarith only [hh]
  calc
    _≤∑j : Fin N,4*‖x‖^2*(∑i : Fin N,(b i j)^2) := Finset.sum_le_sum (fun j _ => hcol j)
    _=_ := by rw [←Finset.mul_sum,Finset.sum_comm]

/-- Quartic Itô production with both drift and noise source, retaining
the actual source fourth powers. -/
theorem fourthProduction_le (x : State N) (a : Fin N→ℝ) (b : Fin N→Fin N→ℝ)
    (K S f g : ℝ) (hK : 0≤K) (hS : 0≤S) (hf : 0≤f) (hg : 0≤g)
    (ha : ‖WithLp.toLp 2 a‖≤K*‖x‖+f)
    (hb : (∑i : Fin N,∑j : Fin N,(b i j)^2)≤S*‖x‖^2+g^2) :
    fourthProduction x a b≤(4*K+6*S+6)*‖x‖^4+f^4+3*g^4 := by
  have hi : (∑i : Fin N,2*x i*a i)=2*inner ℝ x (WithLp.toLp 2 a) := by
    simp only [PiLp.inner_apply,RCLike.inner_apply,PiLp.toLp_apply,starRingEnd_apply,star_trivial]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have hinner : inner ℝ x (WithLp.toLp 2 a)≤‖x‖*(K*‖x‖+f) :=
    (le_abs_self _).trans ((norm_inner_le_norm (𝕜:=ℝ) x (WithLp.toLp 2 a)).trans
      (mul_le_mul_of_nonneg_left ha (norm_nonneg _)))
  have h1 := mul_le_mul_of_nonneg_left hinner (show 0≤4*‖x‖^2 by positivity)
  have h2 := mul_le_mul_of_nonneg_left hb (show 0≤6*‖x‖^2 by positivity)
  have hnoise := radial_noise_le_trace x b
  have hy := quartic_young ‖x‖ f (norm_nonneg _) hf
  have hs := sq_nonneg (‖x‖^2-g^2)
  unfold fourthProduction
  rw [hi]
  nlinarith only [h1,h2,hnoise,hy,hs]

end SphericalAging.VectorQuarticSourceBound
