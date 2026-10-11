module

public import SphericalAging.SlowDiagonalChoice
public import SphericalAging.SusceptibilityWindow

public section

/-! Actual integer-age susceptibility diagonal, derived from fixed-age prefix
reflection, center energy, stationary response and marginality. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology InnerProductSpace
namespace SphericalAging.SusceptibilityDiagonal
open CKSpecification CausalTree PrefixReflection PrefixRectangleStability CausalCenterAverage
open CenterNormalization CubicResponseLocalization TreeCeilings SusceptibilityWindow

theorem tendsto_of_abs_error {f g e : ℕ → ℝ} {a : ℝ}
    (hb : ∀ n,|f n-g n|≤e n) (he : Tendsto e atTop (𝓝 0))
    (hg : Tendsto g atTop (𝓝 a)) : Tendsto f atTop (𝓝 a) := by
  have hd : Tendsto (fun n => f n-g n) atTop (𝓝 0) :=
    squeeze_zero_norm (fun n => by simpa only [Real.norm_eq_abs] using hb n) he
  simpa only [sub_add_cancel,zero_add] using hd.add hg

structure FixedAgeGood {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (c r : ℝ → ℝ) (q : ℝ) (k : ℕ) (T : ℝ) : Prop where
  gram : ∀ a b : ℝ,a∈Icc 0 (k+1:ℝ) → b∈Icc 0 (k+1:ℝ) →
    |futureKernel h T a b-c (a+b)|≤1/(k+1:ℝ)
  center_positive : 0<‖localCenter h T (k+1:ℝ)‖
  center_unit : ‖normalizedCenter h (T+(k+1:ℝ)) (k+1:ℝ)‖=1
  deficit : |cubicCeiling-functional (normalizedCenter h (T+(k+1:ℝ)) (k+1:ℝ))-
    deficitLimit β q c r (k+1:ℝ)|≤1/(k+1:ℝ)
  mass : |windowMass d (T+(k+1:ℝ)) (k+1:ℝ)-(1-c (k+1:ℝ))|≤1/(k+1:ℝ)

theorem fixedAge_good_eventually {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) (k : ℕ) :
    ∀ᶠ T : ℝ in atTop, FixedAgeGood h c r q k T := by
  let D : ℝ := k+1
  have hD : 0<D := by dsimp [D]; positivity
  have he : 0<1/D := by positivity
  have hgram := Metric.tendstoUniformlyOn_iff.mp (H.reflected_prefix D hD.le) (1/D) he
  have hunit := CenterNormWaiting.normalized_centers_eventually_unit h hD.le
    (H.q_positive.trans_le (H.correlation_bounds (2*D) (by positivity)).1) (H.reflected_prefix D hD.le)
  have hshift : Tendsto (fun T : ℝ => T+D) atTop atTop :=
    tendsto_atTop_add_const_right atTop D tendsto_id
  have hd := ((center_deficit_real_limit H hD.le).comp hshift).sub_const (deficitLimit β q c r D) |>.abs
  have hm := ((windowMass_tendsto H hD.le).comp hshift).sub_const (1-c D) |>.abs
  have hd' := hd.eventually (gt_mem_nhds (by simpa only [sub_self,abs_zero] using he))
  have hm' := hm.eventually (gt_mem_nhds (by simpa only [sub_self,abs_zero] using he))
  filter_upwards [hgram,hunit,hd',hm'] with T hg hu hd hm
  have hn := hu (T+D) le_rfl
  refine ⟨?_,?_,hn.2,hd.le,hm.le⟩
  · intro a b ha hb
    have hh := hg (a,b) ⟨ha,hb⟩
    simpa only [Function.uncurry_apply_pair,Real.dist_eq,abs_sub_comm] using hh.le
  · simpa only [add_sub_cancel_right] using hn.1

structure Receipt {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    (c : ℝ → ℝ) (q : ℝ) (t L : ℕ → ℝ) : Prop where
  age_positive : ∀ n,0<L n
  waiting_ge_age : ∀ n,L n≤t n-L n
  age_tendsto : Tendsto L atTop atTop
  waiting_tendsto : Tendsto (fun n => t n-L n) atTop atTop
  center_positive : ∀ n,0<‖localCenter h (t n-L n) (L n)‖
  center_unit : ∀ n,‖normalizedCenter h (t n) (L n)‖=1
  gram : ∀ n a b,a∈Icc 0 (L n) → b∈Icc 0 (L n) →
    |futureKernel h (t n-L n) a b-c (a+b)|≤1/L n
  norm_square_tendsto : Tendsto (fun n => ‖prefixVector h (t n-L n) (t n)‖^2) atTop (𝓝 q)
  recent_mass_tendsto : Tendsto (fun n => susceptibility d (t n) (t n-L n)) atTop (𝓝 (1-q))
  energy_tendsto : Tendsto (fun n => functional (normalizedCenter h (t n) (L n))) atTop (𝓝 cubicCeiling)

theorem exists_integer_receipt {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ (N : ℕ) (i : ℕ → ℕ), Receipt h c q (fun n => t (n+N)) (fun n => (i n:ℝ)+1) := by
  obtain ⟨N,i,hi,hgood⟩ := SlowDiagonalChoice.exists_integer_ages
    (FixedAgeGood h c r q) (fixedAge_good_eventually H) t ht
  let L : ℕ → ℝ := fun n => (i n:ℝ)+1
  have hL : Tendsto L atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop.comp hi)
  have hLpos (n : ℕ) : 0<L n := by dsimp [L]; positivity
  have hg (n : ℕ) : FixedAgeGood h c r q (i n) (t (n+N)-L n) := (hgood n).2
  have hsum (n : ℕ) : t (n+N)-L n+L n=t (n+N) := sub_add_cancel _ _
  have he : Tendsto (fun n => 1/L n) atTop (𝓝 (0:ℝ)) := by
    simpa only [one_div,Function.comp_def] using (tendsto_inv_atTop_zero : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0)).comp hL
  refine ⟨N,i,hLpos,fun n => (hgood n).1,hL,
    tendsto_atTop_mono (fun n => (hgood n).1) hL,?_,?_,?_,?_,?_,?_⟩
  · exact fun n => (hg n).center_positive
  · intro n
    have hh := (hg n).center_unit
    change ‖normalizedCenter h (t (n+N)-L n+L n) (L n)‖=1 at hh
    rwa [hsum n] at hh
  · exact fun n => (hg n).gram
  · have hb (n : ℕ) : |‖prefixVector h (t (n+N)-L n) (t (n+N))‖^2-c (2*L n)|≤1/L n := by
      have hh := (hg n).gram (L n) (L n) ⟨(hLpos n).le,le_rfl⟩ ⟨(hLpos n).le,le_rfl⟩
      have hself : futureKernel h (t (n+N)-L n) (L n) (L n)=
          ‖prefixVector h (t (n+N)-L n) (t (n+N))‖^2 := by
        unfold futureKernel prefixKernel
        rw [hsum n,real_inner_self_eq_norm_sq]
      rw [hself,show L n+L n=2*L n by ring] at hh
      exact hh
    exact tendsto_of_abs_error hb he (H.plateau_limit.comp
      ((tendsto_const_mul_atTop_of_pos (show (0:ℝ)<2 by norm_num)).mpr hL))
  · have hb (n : ℕ) : |susceptibility d (t (n+N)) (t (n+N)-L n)-(1-c (L n))|≤1/L n := by
      have hh := (hg n).mass
      rw [hsum n,windowMass_eq] at hh
      exact hh
    exact tendsto_of_abs_error hb he (tendsto_const_nhds.sub (H.plateau_limit.comp hL))
  · have hb (n : ℕ) : |(cubicCeiling-functional (normalizedCenter h (t (n+N)) (L n)))-
        deficitLimit β q c r (L n)|≤1/L n := by
      have hh := (hg n).deficit
      change |cubicCeiling-functional (normalizedCenter h (t (n+N)-L n+L n) (L n))-
        deficitLimit β q c r (L n)|≤1/L n at hh
      rwa [hsum n] at hh
    have hd := tendsto_of_abs_error hb he ((deficitLimit_tendsto H).comp hL)
    simpa only [sub_sub_cancel,sub_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => cubicCeiling) atTop (𝓝 cubicCeiling)).sub hd

theorem exists_receipt {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q)
    (t : ℕ → ℝ) (ht : Tendsto t atTop atTop) :
    ∃ (N : ℕ) (L : ℕ → ℝ), Receipt h c q (fun n => t (n+N)) L := by
  obtain ⟨N,i,hi⟩ := exists_integer_receipt H t ht
  exact ⟨N,fun n => (i n:ℝ)+1,hi⟩

theorem Receipt.waiting_nonnegative {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ → ℝ} {q : ℝ} {t L : ℕ → ℝ} (A : Receipt h c q t L) (n : ℕ) :
    0≤t n-L n := (A.age_positive n).le.trans (A.waiting_ge_age n)

theorem Receipt.center_norm_tendsto {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c : ℝ → ℝ} {q : ℝ} {t L : ℕ → ℝ} (A : Receipt h c q t L) :
    Tendsto (fun n => ‖prefixVector h (t n-L n) (t n)‖) atTop (𝓝 (Real.sqrt q)) := by
  simpa only [Real.sqrt_sq (norm_nonneg _)] using A.norm_square_tendsto.sqrt

end SphericalAging.SusceptibilityDiagonal
