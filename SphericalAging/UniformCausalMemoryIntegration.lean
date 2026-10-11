module

public import SphericalAging.UniformBoundedKernelOperations

public section

/-! Variable causal endpoints preserve uniform convergence of genuinely
integrable bounded memory bodies. Only their causal integration domain is needed. -/
noncomputable section
open Set MeasureTheory Filter Topology
namespace SphericalAging.UniformCausalMemoryIntegration
open UniformBoundedKernelOperations
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
variable {A X Z : Type*} {L : Filter A}

 theorem uniform_limit_abs_bound [NeBot L] {K : Set X} {F : A→X→ℝ} {f : X→ℝ} {M : ℝ}
    (hF : TendstoUniformlyOn F f L K) (hFn : ∀j x,x∈K → |F j x|≤M) :
    ∀x,x∈K → |f x|≤M := by
  intro x hx
  exact le_of_tendsto ((hF.tendsto_at hx).abs) (Eventually.of_forall (fun j => hFn j x hx))

 theorem uniform_causal_interval_integral {D : Set Z} {F : A→Z→ℝ→ℝ}
    {f : Z→ℝ→ℝ} {endpoint : Z→ℝ} {T : ℝ}
    (hT : 0≤T) (he : ∀z,z∈D → 0≤endpoint z ∧ endpoint z≤T)
    (hF : ∀j z,z∈D → IntervalIntegrable (F j z) volume 0 (endpoint z))
    (hf : ∀z,z∈D → IntervalIntegrable (f z) volume 0 (endpoint z))
    (hlim : TendstoUniformlyOn (fun j => fun q : Z×ℝ => F j q.1 q.2)
      (fun q => f q.1 q.2) L {q | q.1∈D ∧ q.2∈Icc 0 (endpoint q.1)}) :
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
  · have hr' : r∈Icc 0 (endpoint z) := by
      rw [uIoc_of_le (he z hz).1] at hr
      exact ⟨hr.1.le,hr.2⟩
    have hh := hj (z,r) ⟨hz,hr'⟩
    rw [Real.dist_eq,abs_sub_comm] at hh
    exact hh.le

 theorem uniform_power_product {K : Set X} {C D R : A→X→ℝ} {c d r : X→ℝ} {B Q : ℝ}
    (hB : 0≤B) (hQ : 0≤Q) (hC : TendstoUniformlyOn C c L K)
    (hD : TendstoUniformlyOn D d L K) (hR : TendstoUniformlyOn R r L K)
    (hCn : ∀j x,x∈K → |C j x|≤1) (hc : ∀x,x∈K → |c x|≤1)
    (hDn : ∀j x,x∈K → |D j x|≤B) (hd : ∀x,x∈K → |d x|≤B)
    (hr : ∀x,x∈K → |r x|≤Q) (n : ℕ) :
    TendstoUniformlyOn (fun j x => (C j x)^n*D j x*R j x)
      (fun x => (c x)^n*d x*r x) L K := by
  have hp := uniform_pow_of_bound (by norm_num : (0 : ℝ)≤1) hC hCn hc n
  have hpow : ∀j x,x∈K → |(C j x)^n|≤1 := fun j x hx => by
    rw [abs_pow]
    exact pow_le_one₀ (abs_nonneg _) (hCn j x hx)
  have hprod := uniform_mul_of_bounds (by norm_num : (0 : ℝ)≤1) hB hp hD hpow hd
  have hprodBound : ∀j x,x∈K → |(C j x)^n*D j x|≤B := fun j x hx => by
    rw [abs_mul]
    exact (mul_le_mul (hpow j x hx) (hDn j x hx) (abs_nonneg _) (by norm_num)).trans_eq (one_mul B)
  exact uniform_mul_of_bounds hB hQ hprod hR hprodBound hr

end SphericalAging.UniformCausalMemoryIntegration
