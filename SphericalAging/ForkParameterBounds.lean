module

public import SphericalAging.CenterEnergyTheorem
public import Mathlib.Algebra.Order.Ring.Abs

public section

/-! The literal finite-fork parameters and the uniform source 10.5 error bounds.
All estimates come from the profile FDT and the finite convex averages. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ForkParameterBounds
open ProfileCenterEnergy

@[expose] def forkNorm (c : ℝ → ℝ) (K : ℕ) (L : ℝ) : ℝ :=
  1/(K:ℝ)+(1-1/(K:ℝ))*c (2*L)

@[expose] def mixedOverlap (c : ℝ → ℝ) (K : ℕ) (L u : ℝ) : ℝ :=
  (c u+((K:ℝ)-1)*c (2*L-u))/(K:ℝ)

@[expose] def forkEnergy (p : ℕ) (β e : ℝ) (c r : ℝ → ℝ) (K : ℕ) (L : ℝ) : ℝ :=
  e-β*(p:ℝ)*(∫ u in (0:ℝ)..L, r u*(c u^(p-1)-mixedOverlap c K L u^(p-1)))

@[expose] def prefixEnergy (p : ℕ) (β e : ℝ) (c r : ℝ → ℝ) (L : ℝ) : ℝ :=
  e+β*(p:ℝ)*(∫ u in (0:ℝ)..L, r u*(c (2*L-u)^(p-1)-c u^(p-1)))

theorem norm_error {c r : ℝ → ℝ} {q L : ℝ} {K : ℕ}
    (H : Profile c r q) (hK : 1≤K) (hL : 0≤L) :
    0≤forkNorm c K L-c (2*L) ∧ forkNorm c K L-c (2*L)≤1/(K:ℝ) := by
  have hK0 : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hb := H.bounds (2*L) (by positivity)
  have he : forkNorm c K L-c (2*L)=(1-c (2*L))/(K:ℝ) := by
    unfold forkNorm
    ring
  rw [he]
  constructor
  · exact div_nonneg (sub_nonneg.mpr hb.2) hK0.le
  · exact div_le_div_of_nonneg_right (by linarith [hb.1]) hK0.le

theorem mixed_overlap_bounds {c r : ℝ → ℝ} {q L u : ℝ} {K : ℕ}
    (H : Profile c r q) (hK : 1≤K) (hL : 0≤L) (hu : u∈Icc 0 L) :
    0≤mixedOverlap c K L u ∧ mixedOverlap c K L u≤1 ∧
      |mixedOverlap c K L u-c (2*L-u)|≤1/(K:ℝ) := by
  have hK0 : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hK1 : (1:ℝ)≤K := by exact_mod_cast hK
  have ha := H.bounds u hu.1
  have hb := H.bounds (2*L-u) (by linarith [hu.2])
  have he : mixedOverlap c K L u-c (2*L-u)=(c u-c (2*L-u))/(K:ℝ) := by
    unfold mixedOverlap
    field_simp
    ring
  refine ⟨div_nonneg (by nlinarith : 0≤c u+((K:ℝ)-1)*c (2*L-u)) hK0.le,?_,?_⟩
  · unfold mixedOverlap
    apply (div_le_one hK0).mpr
    nlinarith
  · rw [he,abs_div,abs_of_pos hK0]
    apply div_le_div_of_nonneg_right _ hK0.le
    exact abs_le.mpr ⟨by linarith,by linarith⟩

theorem unit_power_difference {a b : ℝ} (ha : a∈Icc 0 1) (hb : b∈Icc 0 1)
    (n : ℕ) : |a^n-b^n|≤(n:ℝ)*|a-b| := by
  have hmax : max |a| |b|≤1 := by
    rw [abs_of_nonneg ha.1,abs_of_nonneg hb.1]
    exact max_le ha.2 hb.2
  have hmax0 : 0≤max |a| |b| := (abs_nonneg a).trans (le_max_left _ _)
  calc
    |a^n-b^n|≤|a-b| *(n:ℝ)*max |a| |b|^(n-1) := abs_pow_sub_pow_le ..
    _ ≤ |a-b| *(n:ℝ)*1 := mul_le_mul_of_nonneg_left
      (pow_le_one₀ hmax0 hmax) (by positivity)
    _ = (n:ℝ)*|a-b| := by ring

theorem response_interval_mass {c r : ℝ → ℝ} {q L : ℝ}
    (H : Profile c r q) (hL : 0≤L) : (∫ u in (0:ℝ)..L,r u)=1-c L := by
  have hi := (H.continuous_r.mono Icc_subset_Ici_self).intervalIntegrable_of_Icc (μ:=volume) hL
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hL
    (H.continuous_c.mono Icc_subset_Ici_self)
    (fun u hu => H.fdt u hu.1) hi.neg
  rw [intervalIntegral.integral_neg,H.initial] at he
  linarith

theorem energy_difference {p K : ℕ} {β e q L : ℝ} {c r : ℝ → ℝ}
    (H : Profile c r q) (hL : 0≤L) :
    forkEnergy p β e c r K L-prefixEnergy p β e c r L=
      β*(p:ℝ)*(∫ u in (0:ℝ)..L,
        r u*(mixedOverlap c K L u^(p-1)-c (2*L-u)^(p-1))) := by
  have hr := H.continuous_r.mono (Icc_subset_Ici_self : Icc (0:ℝ) L⊆Ici 0)
  have hc := H.continuous_c.mono (Icc_subset_Ici_self : Icc (0:ℝ) L⊆Ici 0)
  have href : ContinuousOn (fun u => c (2*L-u)) (Icc 0 L) :=
    H.continuous_c.comp (by fun_prop) (by intro u hu; change 0≤2*L-u; linarith [hu.2])
  have hm : ContinuousOn (mixedOverlap c K L) (Icc 0 L) :=
    (hc.add (href.const_mul ((K:ℝ)-1))).div_const (K:ℝ)
  have hi1 := (hr.mul ((hc.pow (p-1)).sub (hm.pow (p-1)))).intervalIntegrable_of_Icc (μ:=volume) hL
  have hi2 := (hr.mul ((href.pow (p-1)).sub (hc.pow (p-1)))).intervalIntegrable_of_Icc (μ:=volume) hL
  change IntervalIntegrable (fun u => r u*(c u^(p-1)-mixedOverlap c K L u^(p-1))) volume 0 L at hi1
  change IntervalIntegrable (fun u => r u*(c (2*L-u)^(p-1)-c u^(p-1))) volume 0 L at hi2
  have he : (∫ u in (0:ℝ)..L,r u*(c u^(p-1)-mixedOverlap c K L u^(p-1)))+
      (∫ u in (0:ℝ)..L,r u*(c (2*L-u)^(p-1)-c u^(p-1)))=
      -(∫ u in (0:ℝ)..L,r u*(mixedOverlap c K L u^(p-1)-c (2*L-u)^(p-1))) := by
    rw [←intervalIntegral.integral_add hi1 hi2,←intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro u _
    dsimp only
    ring
  have heB := congrArg (fun x : ℝ => β*(p:ℝ)*x) he
  unfold forkEnergy prefixEnergy
  nlinarith [heB]

theorem energy_error {p K : ℕ} {β e q L : ℝ} {c r : ℝ → ℝ}
    (H : Profile c r q) (hβ : 0≤β) (hK : 1≤K) (hL : 0≤L)
    (hr : ∀ u, 0<u → 0≤r u) :
    |forkEnergy p β e c r K L-prefixEnergy p β e c r L|≤
      β*(p:ℝ)*((p:ℝ)-1)/(K:ℝ) := by
  by_cases hp : p=0
  · subst p
    simp [forkEnergy,prefixEnergy]
  have hK0 : (0:ℝ)<K := by exact_mod_cast (show 0<K by omega)
  have hp1 : 1≤p := by omega
  have hpc : ((p-1:ℕ):ℝ)=(p:ℝ)-1 := by simpa only [Nat.cast_one] using (Nat.cast_sub hp1 : ((p-1:ℕ):ℝ)=(p:ℝ)-(1:ℕ))
  have hbound : ∀ᵐ u : ℝ, u∈Ioc 0 L →
      ‖r u*(mixedOverlap c K L u^(p-1)-c (2*L-u)^(p-1))‖≤
        r u*(((p:ℝ)-1)/(K:ℝ)) := by
    exact Eventually.of_forall (fun u hu => by
      have hm := mixed_overlap_bounds H hK hL ⟨hu.1.le,hu.2⟩
      have hb := H.bounds (2*L-u) (by linarith [hu.2])
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hr u hu.1)]
      apply mul_le_mul_of_nonneg_left _ (hr u hu.1)
      calc
        |mixedOverlap c K L u^(p-1)-c (2*L-u)^(p-1)|≤
          ((p-1:ℕ):ℝ)*|mixedOverlap c K L u-c (2*L-u)| :=
            unit_power_difference ⟨hm.1,hm.2.1⟩ hb (p-1)
        _ ≤ ((p-1:ℕ):ℝ)*(1/(K:ℝ)) :=
          mul_le_mul_of_nonneg_left hm.2.2 (by positivity)
        _ = ((p:ℝ)-1)/(K:ℝ) := by rw [hpc]; ring)
  have hi := ((H.continuous_r.mono Icc_subset_Ici_self).mul_const
      (((p:ℝ)-1)/(K:ℝ))).intervalIntegrable_of_Icc (μ:=volume) hL
  have hb := intervalIntegral.norm_integral_le_of_norm_le hL hbound hi
  rw [intervalIntegral.integral_mul_const,response_interval_mass H hL,Real.norm_eq_abs] at hb
  have hmass : 1-c L≤1 := by linarith [(H.bounds L hL).1]
  have hp1c : (1:ℝ)≤p := by exact_mod_cast hp1
  have hfactor : 0≤((p:ℝ)-1)/(K:ℝ) := div_nonneg (sub_nonneg.mpr hp1c) hK0.le
  have hb' : |∫ u in (0:ℝ)..L,r u*(mixedOverlap c K L u^(p-1)-c (2*L-u)^(p-1))|≤
      ((p:ℝ)-1)/(K:ℝ) := hb.trans (by nlinarith)
  rw [energy_difference H hL,abs_mul,abs_of_nonneg (mul_nonneg hβ (Nat.cast_nonneg p))]
  calc
    β*(p:ℝ)*|∫ u in (0:ℝ)..L,r u*(mixedOverlap c K L u^(p-1)-c (2*L-u)^(p-1))|≤
        β*(p:ℝ)*(((p:ℝ)-1)/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left hb' (mul_nonneg hβ (Nat.cast_nonneg p))
    _ = β*(p:ℝ)*((p:ℝ)-1)/(K:ℝ) := by ring

end SphericalAging.ForkParameterBounds
