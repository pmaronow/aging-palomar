module

public import SphericalAging.ExternalFieldElementaryPenalty
public import Mathlib.Analysis.SpecialFunctions.Sqrt

public section

/-! Sharp scalar all-p external-field opening. The stochastic input remains
separate; this module proves actual scalar coefficients from the printed ALG. -/
noncomputable section
set_option maxHeartbeats 1600000
namespace SphericalAging.ExternalFieldSharpScalar
open Set PlateauAlgebra ExternalFieldElementaryPenalty

@[expose]  def betaD (p : ℕ) : ℝ := Real.sqrt (transitionBetaSquared p)
@[expose]  def transitionOverlap (p : ℕ) : ℝ := Real.sqrt (transitionPlateau p)
@[expose]  def slopeCoefficient (p : ℕ) : ℝ := criticalField p/(transitionOverlap p)^(p-1)
@[expose]  def oneSidedPolynomial (p : ℕ) (q : ℝ) : ℝ := q^(p-2)*(1-q)

 theorem betaD_positive {p : ℕ} (hp : 3≤p) : 0<betaD p :=
  Real.sqrt_pos.mpr (transition_beta_squared_positive hp)
 theorem betaD_sq {p : ℕ} (hp : 3≤p) : betaD p^2=transitionBetaSquared p :=
  Real.sq_sqrt (transition_beta_squared_positive hp).le
 theorem transitionOverlap_positive {p : ℕ} (hp : 3≤p) : 0<transitionOverlap p :=
  Real.sqrt_pos.mpr (transition_plateau_pos hp)
 theorem transitionOverlap_sq {p : ℕ} (hp : 3≤p) : transitionOverlap p^2=transitionPlateau p :=
  Real.sq_sqrt (transition_plateau_pos hp).le
 theorem transitionOverlap_le_one {p : ℕ} (hp : 3≤p) : transitionOverlap p≤1 := by
  exact (Real.sqrt_le_iff.mpr ⟨by norm_num,by simpa only [one_pow] using (transition_plateau_lt_one hp).le⟩)

 theorem oneSidedPolynomial_hasDerivAt {p : ℕ} (hp : 3≤p) (q : ℝ) :
    HasDerivAt (oneSidedPolynomial p)
      (q^(p-3)*((p:ℝ)-2-((p:ℝ)-1)*q)) q := by
  have he : p-2-1=p-3 := by omega
  have he' : p-2=p-3+1 := by omega
  have hc : ((p-2:ℕ):ℝ)=(p:ℝ)-2 := by rw [Nat.cast_sub (by omega : 2≤p)];norm_num
  convert (hasDerivAt_pow (p-2) q).mul ((hasDerivAt_const q (1:ℝ)).sub (hasDerivAt_id q)) using 1
  · ext y;unfold oneSidedPolynomial;rfl
  · change q^(p-3)*((p:ℝ)-2-((p:ℝ)-1)*q)=
      ((p-2:ℕ):ℝ)*q^(p-2-1)*(1-q)+q^(p-2)*(0-1)
    rw [he,hc,he',pow_succ];ring

 theorem oneSidedPolynomial_le_transition {p : ℕ} (hp : 3≤p) {q : ℝ} (hq : q∈Icc 0 1) :
    oneSidedPolynomial p q≤oneSidedPolynomial p (transitionPlateau p) := by
  have hc : Continuous (oneSidedPolynomial p) := (continuous_id.pow _).mul (continuous_const.sub continuous_id)
  have hm : MonotoneOn (oneSidedPolynomial p) (Icc 0 (transitionPlateau p)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _) hc.continuousOn
    · intro x hx;exact (oneSidedPolynomial_hasDerivAt hp x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(oneSidedPolynomial_hasDerivAt hp x).deriv]
      have hx' := (le_div_iff₀ (spin_minus_one_positive hp)).mp (show x≤((p:ℝ)-2)/((p:ℝ)-1) from hx.2.le)
      exact mul_nonneg (pow_nonneg hx.1.le _) (by linarith)
  have ha : AntitoneOn (oneSidedPolynomial p) (Icc (transitionPlateau p) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc.continuousOn
    · intro x hx;exact (oneSidedPolynomial_hasDerivAt hp x).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(oneSidedPolynomial_hasDerivAt hp x).deriv]
      have hx' := (div_le_iff₀ (spin_minus_one_positive hp)).mp (show ((p:ℝ)-2)/((p:ℝ)-1)≤x from hx.1.le)
      exact mul_nonpos_of_nonneg_of_nonpos
        (pow_nonneg ((transition_plateau_pos hp).le.trans hx.1.le) _) (by linarith)
  by_cases h : q≤transitionPlateau p
  · exact hm ⟨hq.1,h⟩ ⟨(transition_plateau_pos hp).le,le_rfl⟩ h
  · exact ha ⟨le_rfl,(transition_plateau_lt_one hp).le⟩ ⟨(le_of_not_ge h),hq.2⟩ (le_of_not_ge h)

 theorem betaD_oneSidedPolynomial_transition {p : ℕ} (hp : 3≤p) :
    (p:ℝ)*betaD p^2*oneSidedPolynomial p (transitionPlateau p)=1 := by
  rw [betaD_sq hp]
  unfold transitionBetaSquared oneSidedPolynomial transitionPlateau
  rw [div_pow]
  have hp0 := (spin_positive hp).ne'
  have hp1 := (spin_minus_one_positive hp).ne'
  have hp2 := (spin_minus_two_positive hp).ne'
  have he : p-1=(p-2)+1 := by omega
  rw [he,pow_succ]
  field_simp
  ring

 theorem betaD_oneSidedPolynomial_le_one {p : ℕ} (hp : 3≤p) {q : ℝ} (hq : q∈Icc 0 1) :
    (p:ℝ)*betaD p^2*oneSidedPolynomial p q≤1 := by
  rw [←betaD_oneSidedPolynomial_transition hp]
  exact mul_le_mul_of_nonneg_left (oneSidedPolynomial_le_transition hp hq)
    (mul_nonneg (spin_positive hp).le (sq_nonneg _))

 theorem slopeCoefficient_eq {p : ℕ} (hp : 3≤p) : slopeCoefficient p=(p:ℝ)*betaD p := by
  have hr := transitionOverlap_positive hp
  have hk := criticalField_positive hp
  have hs : slopeCoefficient p^2=((p:ℝ)*betaD p)^2 := by
    unfold slopeCoefficient
    rw [div_pow,mul_pow,betaD_sq hp]
    have he : (transitionOverlap p^(p-1))^2=(transitionPlateau p)^(p-1) := by
      rw [←pow_mul,Nat.mul_comm,pow_mul,transitionOverlap_sq hp]
    rw [he]
    have hc : criticalField p^2=(p:ℝ)*((p:ℝ)-2) := by
      exact Real.sq_sqrt (mul_nonneg (spin_positive hp).le (spin_minus_two_positive hp).le)
    rw [hc]
    unfold transitionPlateau transitionBetaSquared
    rw [div_pow]
    have he' : p-1=p-2+1 := by omega
    rw [he',pow_succ]
    field_simp [(spin_positive hp).ne',(spin_minus_one_positive hp).ne',(spin_minus_two_positive hp).ne']
  exact (sq_eq_sq₀ (div_nonneg hk.le (pow_nonneg hr.le _))
    (mul_nonneg (spin_positive hp).le (betaD_positive hp).le)).mp hs

 theorem fieldCoefficient_eq {p : ℕ} (hp : 3≤p) :
    ((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1))=
      criticalField p*transitionOverlap p*((p:ℝ)-1)/(p:ℝ) := by
  have hn : 0≤((p:ℝ)-2)/(p:ℝ)*Real.sqrt ((p:ℝ)*((p:ℝ)-1)) :=
    mul_nonneg (div_nonneg (spin_minus_two_positive hp).le (spin_positive hp).le) (Real.sqrt_nonneg _)
  have hn' : 0≤criticalField p*transitionOverlap p*((p:ℝ)-1)/(p:ℝ) := by
    exact div_nonneg (mul_nonneg (mul_nonneg (criticalField_positive hp).le
      (transitionOverlap_positive hp).le) (spin_minus_one_positive hp).le) (spin_positive hp).le
  apply (sq_eq_sq₀ hn hn').mp
  rw [mul_pow,div_pow,Real.sq_sqrt (mul_nonneg (spin_positive hp).le (spin_minus_one_positive hp).le),
    div_pow,mul_pow,mul_pow,transitionOverlap_sq hp]
  have hc : criticalField p^2=(p:ℝ)*((p:ℝ)-2) := by
    exact Real.sq_sqrt (mul_nonneg (spin_positive hp).le (spin_minus_two_positive hp).le)
  rw [hc]
  unfold transitionPlateau
  field_simp [(spin_positive hp).ne',(spin_minus_one_positive hp).ne']

 theorem low_overlap_matching_field {p : ℕ} (hp : 3≤p) {a : ℝ}
    (ha : a∈Icc 0 (transitionOverlap p)) :
    algorithmicField p (criticalField p*(a/transitionOverlap p)^(p-1))-
      criticalField p*(a/transitionOverlap p)^(p-1)*a=thresholdEnergy p-betaD p*a^p := by
  let b : ℝ := a/transitionOverlap p
  have hr := transitionOverlap_positive hp
  have hb : b∈Icc 0 1 := ⟨div_nonneg ha.1 hr.le,(div_le_one hr).mpr ha.2⟩
  have ha' : a=transitionOverlap p*b := by dsimp [b];field_simp
  have hsr : criticalField p=(p:ℝ)*betaD p*transitionOverlap p^(p-1) := by
    have hs := slopeCoefficient_eq hp
    unfold slopeCoefficient at hs
    exact (div_eq_iff (pow_ne_zero _ hr.ne')).mp hs
  have hα : criticalField p*transitionOverlap p/(p:ℝ)=betaD p*transitionOverlap p^p := by
    rw [hsr,PlateauAlgebra.pow_relation hp]
    field_simp
  have hc : (elementaryPenalty p)*b^p+criticalField p*b^(p-1)*(a-b)=betaD p*a^p := by
    calc
      _ = criticalField p*transitionOverlap p/(p:ℝ)*b^p := by
        rw [ha']
        unfold elementaryPenalty
        rw [fieldCoefficient_eq hp,PlateauAlgebra.pow_relation hp b]
        field_simp [(spin_positive hp).ne']
        ring
      _ = betaD p*transitionOverlap p^p*b^p := by rw [hα]
      _ = betaD p*a^p := by rw [ha',mul_pow];ring
  have hh := matched_field_cost hp hb
  change algorithmicField p (criticalField p*b^(p-1))-criticalField p*b^(p-1)*a=_
  linarith

 theorem thresholdEnergy_eq {p : ℕ} (hp : 3≤p) :
    thresholdEnergy p=2*Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(p:ℝ) := by
  have hn : 0≤thresholdEnergy p := by unfold thresholdEnergy;positivity
  have hn' : 0≤2*Real.sqrt ((p:ℝ)*((p:ℝ)-1))/(p:ℝ) :=
    div_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _)) (spin_positive hp).le
  apply (sq_eq_sq₀ hn hn').mp
  unfold thresholdEnergy
  rw [mul_pow,Real.sq_sqrt (div_nonneg (spin_minus_one_positive hp).le (spin_positive hp).le),
    div_pow,mul_pow,Real.sq_sqrt (mul_nonneg (spin_positive hp).le (spin_minus_one_positive hp).le)]
  field_simp [(spin_positive hp).ne']

 theorem betaD_transition_power {p : ℕ} (hp : 3≤p) :
    betaD p*transitionOverlap p^p=criticalField p*transitionOverlap p/(p:ℝ) := by
  have hs := slopeCoefficient_eq hp
  unfold slopeCoefficient at hs
  have he := (div_eq_iff (pow_ne_zero _ (transitionOverlap_positive hp).ne')).mp hs
  rw [he,PlateauAlgebra.pow_relation hp]
  field_simp

@[expose]  def highCeiling (p : ℕ) (a : ℝ) : ℝ := Real.sqrt (p:ℝ)*Real.sqrt (1-a^2)+betaD p*a^p

 theorem highCeiling_at_transition {p : ℕ} (hp : 3≤p) :
    highCeiling p (transitionOverlap p)=thresholdEnergy p := by
  let S : ℝ := Real.sqrt ((p:ℝ)*((p:ℝ)-1))
  have hs : Real.sqrt (p:ℝ)*Real.sqrt (1-transitionOverlap p^2)=S/((p:ℝ)-1) := by
    apply (sq_eq_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (div_nonneg (Real.sqrt_nonneg _) (spin_minus_one_positive hp).le)).mp
    rw [mul_pow,Real.sq_sqrt (spin_positive hp).le,transitionOverlap_sq hp,
      Real.sq_sqrt (sub_nonneg.mpr (transition_plateau_lt_one hp).le),div_pow]
    rw [Real.sq_sqrt (mul_nonneg (spin_positive hp).le (spin_minus_one_positive hp).le)]
    unfold transitionPlateau
    field_simp [(spin_minus_one_positive hp).ne']
    ring
  have hc : criticalField p*transitionOverlap p=((p:ℝ)-2)*S/((p:ℝ)-1) := by
    have hh := fieldCoefficient_eq hp
    change ((p:ℝ)-2)/(p:ℝ)*S=criticalField p*transitionOverlap p*((p:ℝ)-1)/(p:ℝ) at hh
    apply (eq_div_iff (spin_minus_one_positive hp).ne').mpr
    have hmul := congrArg (fun z : ℝ => z*(p:ℝ)) hh
    field_simp [(spin_positive hp).ne'] at hmul
    linarith
  unfold highCeiling
  rw [hs,betaD_transition_power hp,hc,thresholdEnergy_eq hp]
  change S/((p:ℝ)-1)+(((p:ℝ)-2)*S/((p:ℝ)-1))/(p:ℝ)=2*S/(p:ℝ)
  field_simp [(spin_positive hp).ne',(spin_minus_one_positive hp).ne']
  ring

 theorem highCeiling_hasDerivAt {p : ℕ} (hp : 3≤p) {a : ℝ} (ha : a∈Ioo (0:ℝ) 1) :
    HasDerivAt (highCeiling p)
      (-(Real.sqrt (p:ℝ)*a/Real.sqrt (1-a^2))+betaD p*(p:ℝ)*a^(p-1)) a := by
  have ht : 0<1-a^2 := by have ha0:=ha.1;have ha1:=ha.2;nlinarith
  have hh := (((hasDerivAt_const a (1:ℝ)).sub (hasDerivAt_pow 2 a)).sqrt ht.ne').const_mul
    (Real.sqrt (p:ℝ))
  have hg := (hasDerivAt_pow p a).const_mul (betaD p)
  convert hh.add hg using 1
  · ext x;unfold highCeiling;rfl
  · simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,Pi.sub_apply]
    change -(Real.sqrt (p:ℝ)*a/Real.sqrt (1-a^2))+betaD p*(p:ℝ)*a^(p-1)=
      Real.sqrt (p:ℝ)*((0-2*a)/(2*Real.sqrt (1-a^2)))+betaD p*((p:ℝ)*a^(p-1))
    ring

 theorem highCeiling_deriv_nonpos {p : ℕ} (hp : 3≤p) {a : ℝ} (ha : a∈Ioo (0:ℝ) 1) :
    deriv (highCeiling p) a≤0 := by
  have ht : 0<1-a^2 := by have ha0:=ha.1;have ha1:=ha.2;nlinarith
  have hr : 0<Real.sqrt (1-a^2) := Real.sqrt_pos.mpr ht
  have hb := betaD_oneSidedPolynomial_le_one hp (q:=a^2) ⟨sq_nonneg _,by nlinarith [ha.1,ha.2]⟩
  have hu : ((p:ℝ)*betaD p*a^(p-2)*Real.sqrt (1-a^2))^2≤(Real.sqrt (p:ℝ))^2 := by
    rw [Real.sq_sqrt (spin_positive hp).le]
    have hh := mul_le_mul_of_nonneg_left hb (spin_positive hp).le
    unfold oneSidedPolynomial at hh
    rw [mul_pow,mul_pow,mul_pow,Real.sq_sqrt ht.le]
    have he : (a^(p-2))^2=(a^2)^(p-2) := by rw [←pow_mul,Nat.mul_comm,pow_mul]
    rw [he]
    convert hh using 1 <;> ring
  have hn : 0≤(p:ℝ)*betaD p*a^(p-2)*Real.sqrt (1-a^2) := by
    exact mul_nonneg (mul_nonneg (mul_nonneg (spin_positive hp).le (betaD_positive hp).le)
      (pow_nonneg ha.1.le _)) (Real.sqrt_nonneg _)
  have hu' := (sq_le_sq₀ hn (Real.sqrt_nonneg _)).mp hu
  have hm := mul_le_mul_of_nonneg_right hu' ha.1.le
  have hpow := PlateauAlgebra.pow_pred_relation hp a
  have hx : betaD p*(p:ℝ)*a^(p-1)≤Real.sqrt (p:ℝ)*a/Real.sqrt (1-a^2) := by
    apply (le_div_iff₀ hr).mpr
    rw [hpow]
    convert hm using 1 <;> ring
  rw [(highCeiling_hasDerivAt hp ha).deriv]
  linarith

 theorem highCeiling_antitoneOn {p : ℕ} (hp : 3≤p) :
    AntitoneOn (highCeiling p) (Icc (transitionOverlap p) 1) := by
  have hc : Continuous (highCeiling p) :=
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).const_mul _).add
      ((continuous_id.pow p).const_mul _)
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hc.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (highCeiling_hasDerivAt hp ⟨(transitionOverlap_positive hp).trans hx.1,hx.2⟩).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    exact highCeiling_deriv_nonpos hp ⟨(transitionOverlap_positive hp).trans hx.1,hx.2⟩

 theorem highCeiling_le_threshold {p : ℕ} (hp : 3≤p) {a : ℝ} (ha : a∈Icc (transitionOverlap p) 1) :
    highCeiling p a≤thresholdEnergy p := by
  rw [←highCeiling_at_transition hp]
  exact highCeiling_antitoneOn hp ⟨le_rfl,transitionOverlap_le_one hp⟩ ha ha.1

 theorem betaD_le_threshold {p : ℕ} (hp : 3≤p) : betaD p≤thresholdEnergy p := by
  have hh := highCeiling_le_threshold hp ⟨transitionOverlap_le_one hp,le_rfl⟩
  simpa only [highCeiling,one_pow,sub_self,Real.sqrt_zero,mul_zero,zero_add,mul_one] using hh

 theorem algorithmicField_high {p : ℕ} (hp : 3≤p) {κ : ℝ}
    (hκ : (p:ℝ)*((p:ℝ)-2)≤κ^2) : algorithmicField p κ=Real.sqrt ((p:ℝ)+κ^2) := by
  by_cases hh : κ^2≤(p:ℝ)*((p:ℝ)-2)
  · have he := le_antisymm hh hκ
    have hq : fieldOrder p κ=1 := by
      unfold fieldOrder
      rw [he,div_self (mul_pos (spin_positive hp) (spin_minus_two_positive hp)).ne',Real.one_rpow]
    unfold algorithmicField
    rw [if_pos hh,hq,Real.one_rpow,he,thresholdEnergy_eq hp]
    have hs : (p:ℝ)+(p:ℝ)*((p:ℝ)-2)=(p:ℝ)*((p:ℝ)-1) := by ring
    rw [hs]
    field_simp [(spin_positive hp).ne']
    ring
  · exact if_neg hh

 theorem high_overlap_matching_field {p : ℕ} (hp : 3≤p) {a : ℝ}
    (ha : a∈Ico (transitionOverlap p) 1) :
    let κ := Real.sqrt (p:ℝ)*a/Real.sqrt (1-a^2)
    0≤κ ∧ algorithmicField p κ-κ*a+betaD p*a^p≤thresholdEnergy p := by
  have ha0 : 0≤a := (transitionOverlap_positive hp).le.trans ha.1
  have ht : 0<1-a^2 := by nlinarith [ha.2]
  have hr : 0<Real.sqrt (1-a^2) := Real.sqrt_pos.mpr ht
  let κ := Real.sqrt (p:ℝ)*a/Real.sqrt (1-a^2)
  have hk0 : 0≤κ := div_nonneg (mul_nonneg (Real.sqrt_nonneg _) ha0) hr.le
  have hk : (p:ℝ)*((p:ℝ)-2)≤κ^2 := by
    have hqa : transitionPlateau p≤a^2 := by
      rw [←transitionOverlap_sq hp]
      exact pow_le_pow_left₀ (transitionOverlap_positive hp).le ha.1 2
    have hm := (div_le_iff₀ (spin_minus_one_positive hp)).mp hqa
    dsimp [κ]
    rw [div_pow,mul_pow,Real.sq_sqrt (spin_positive hp).le,Real.sq_sqrt ht.le]
    apply (le_div_iff₀ ht).mpr
    have hh := mul_le_mul_of_nonneg_left hm (spin_positive hp).le
    nlinarith
  have hs : Real.sqrt ((p:ℝ)+κ^2)=Real.sqrt (p:ℝ)/Real.sqrt (1-a^2) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (div_nonneg (Real.sqrt_nonneg _) hr.le)).mp
    rw [Real.sq_sqrt (by positivity)]
    simp only [κ,div_pow,mul_pow,Real.sq_sqrt (spin_positive hp).le,Real.sq_sqrt ht.le]
    field_simp [ht.ne']
    ring
  refine ⟨hk0,?_⟩
  have he : algorithmicField p κ-κ*a=Real.sqrt (p:ℝ)*Real.sqrt (1-a^2) := by
    rw [algorithmicField_high hp hk,hs]
    dsimp [κ]
    field_simp [hr.ne']
    nlinarith [Real.sq_sqrt ht.le]
  rw [he]
  exact highCeiling_le_threshold hp ⟨ha.1,ha.2.le⟩

 theorem sharp_field_approximation {p : ℕ} (hp : 3≤p) {ε : ℝ} (hε : 0<ε)
    {a : ℝ} (ha : a∈Icc 0 1) :
    ∃κ≥0,algorithmicField p κ-κ*a+betaD p*a^p<thresholdEnergy p+ε := by
  by_cases hl : a≤transitionOverlap p
  · refine ⟨criticalField p*(a/transitionOverlap p)^(p-1),
      mul_nonneg (criticalField_positive hp).le (pow_nonneg
        (div_nonneg ha.1 (transitionOverlap_positive hp).le) _),?_⟩
    rw [low_overlap_matching_field hp ⟨ha.1,hl⟩]
    linarith
  by_cases h1 : a<1
  · obtain ⟨hk,hc⟩ := high_overlap_matching_field hp ⟨(le_of_not_ge hl),h1⟩
    exact ⟨_,hk,hc.trans_lt (by linarith)⟩
  · have he : a=1 := le_antisymm ha.2 (le_of_not_gt h1)
    subst a
    let κ : ℝ := criticalField p+(p:ℝ)/ε+1
    have hk0 : 0≤κ := by
      dsimp [κ]
      exact add_nonneg (add_nonneg (criticalField_positive hp).le
        (div_nonneg (spin_positive hp).le hε.le)) (by norm_num)
    have hk : (p:ℝ)*((p:ℝ)-2)≤κ^2 := by
      have hx : criticalField p≤κ := by dsimp [κ];linarith [div_nonneg (spin_positive hp).le hε.le]
      have hs : criticalField p^2=(p:ℝ)*((p:ℝ)-2) :=
        Real.sq_sqrt (mul_nonneg (spin_positive hp).le (spin_minus_two_positive hp).le)
      rw [←hs]
      exact pow_le_pow_left₀ (criticalField_positive hp).le hx 2
    have hm : (p:ℝ)≤κ*ε := by
      have hx : (p:ℝ)/ε≤κ := by dsimp [κ];linarith [(criticalField_positive hp).le]
      exact (div_le_iff₀ hε).mp hx
    have hs : Real.sqrt ((p:ℝ)+κ^2)≤κ+ε/2 := by
      apply Real.sqrt_le_iff.mpr
      refine ⟨by linarith,?_⟩
      nlinarith [sq_nonneg (ε/2)]
    refine ⟨κ,hk0,?_⟩
    rw [algorithmicField_high hp hk,one_pow,mul_one]
    have hb := betaD_le_threshold hp
    linarith

end SphericalAging.ExternalFieldSharpScalar
