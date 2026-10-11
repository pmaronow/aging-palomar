module

public import SphericalAging.ResponsePrimitiveLimitIdentification
public import Mathlib.Topology.Algebra.IsUniformGroup.Basic

public section

/-! Uniform multiplication, powers, and variable-endpoint integration for
bounded measurable kernel families. Approximants need not be continuous. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.UniformBoundedKernelOperations
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {A X Z : Type*} {L : Filter A} {K : Set X}

 theorem uniform_mul_of_bounds {F G : A→X→ℝ} {f g : X→ℝ} {M B : ℝ}
    (hM : 0≤M) (hB : 0≤B) (hF : TendstoUniformlyOn F f L K)
    (hG : TendstoUniformlyOn G g L K)
    (hFn : ∀j x,x∈K → |F j x|≤M) (hg : ∀x,x∈K → |g x|≤B) :
    TendstoUniformlyOn (fun j x => F j x*G j x) (fun x => f x*g x) L K := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := ε/(M+B+1)
  have hd : 0<δ := by dsimp [δ];positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hF) δ hd,
    (Metric.tendstoUniformlyOn_iff.mp hG) δ hd] with j hjF hjG x hx
  have hf : |F j x-f x|≤δ := by
    have hh := hjF x hx
    rw [Real.dist_eq,abs_sub_comm] at hh
    exact hh.le
  have hhg : |G j x-g x|≤δ := by
    have hh := hjG x hx
    rw [Real.dist_eq,abs_sub_comm] at hh
    exact hh.le
  rw [Real.dist_eq,abs_sub_comm]
  have he : F j x*G j x-f x*g x=F j x*(G j x-g x)+(F j x-f x)*g x := by ring
  rw [he]
  have hb : |F j x*(G j x-g x)+(F j x-f x)*g x|≤M*δ+δ*B := (abs_add_le (F j x*(G j x-g x)) ((F j x-f x)*g x)).trans
    (by
      rw [abs_mul,abs_mul]
      exact add_le_add (mul_le_mul (hFn j x hx) hhg (abs_nonneg _) hM)
        (mul_le_mul hf (hg x hx) (abs_nonneg _) hd.le))
  refine hb.trans_lt ?_
  dsimp [δ]
  have hden : 0<M+B+1 := by positivity
  field_simp
  nlinarith

 theorem uniform_pow_of_bound {F : A→X→ℝ} {f : X→ℝ} {M : ℝ}
    (hM : 0≤M) (hF : TendstoUniformlyOn F f L K)
    (hFn : ∀j x,x∈K → |F j x|≤M) (hf : ∀x,x∈K → |f x|≤M) (n : ℕ) :
    TendstoUniformlyOn (fun j x => (F j x)^n) (fun x => (f x)^n) L K := by
  induction n with
  | zero =>
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Eventually.of_forall (fun j x hx => by simpa using hε)
  | succ n hn =>
    simpa only [pow_succ] using uniform_mul_of_bounds (pow_nonneg hM n) hM hn hF
      (fun j x hx => by
        rw [abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hFn j x hx) n) hf

 theorem uniform_variable_interval_integral {D : Set Z} {F : A→Z→ℝ→ℝ}
    {f : Z→ℝ→ℝ} {endpoint : Z→ℝ} {T : ℝ}
    (hT : 0≤T) (he : ∀z,z∈D → 0≤endpoint z ∧ endpoint z≤T)
    (hF : ∀j z,z∈D → IntervalIntegrable (F j z) volume 0 (endpoint z))
    (hf : ∀z,z∈D → IntervalIntegrable (f z) volume 0 (endpoint z))
    (hlim : TendstoUniformlyOn (fun j => fun q : Z×ℝ => F j q.1 q.2)
      (fun q => f q.1 q.2) L (D×ˢIcc 0 T)) :
    TendstoUniformlyOn (fun j z => ∫r in (0 : ℝ)..endpoint z,F j z r)
      (fun z => ∫r in (0 : ℝ)..endpoint z,f z r) L D := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let δ : ℝ := ε/(T+1)
  have hd : 0<δ := by dsimp [δ];positivity
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hlim) δ hd] with j hj z hz
  rw [Real.dist_eq,abs_sub_comm,←intervalIntegral.integral_sub (hF j z hz) (hf z hz)]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := endpoint z) (C := δ) (f := fun r => F j z r-f z r)
    (fun r hr => ?_)
  · simp only [Real.norm_eq_abs,sub_zero,abs_of_nonneg (he z hz).1] at hn
    refine (hn.trans (mul_le_mul_of_nonneg_left (he z hz).2 hd.le)).trans_lt ?_
    dsimp [δ]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0<T+1)).mpr
    nlinarith
  · have hr' : r∈Icc 0 T := by
      rw [uIoc_of_le (he z hz).1] at hr
      exact ⟨hr.1.le,hr.2.trans (he z hz).2⟩
    have hh := hj (z,r) ⟨hz,hr'⟩
    rw [Real.dist_eq,abs_sub_comm] at hh
    exact hh.le

end SphericalAging.UniformBoundedKernelOperations
