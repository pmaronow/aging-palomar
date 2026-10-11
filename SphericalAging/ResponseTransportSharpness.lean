module

public import SphericalAging.ResponseTransport
public import Mathlib.Analysis.Normed.MulAction

public section

/-! The literal two-stage extremizing family for Remark 12.5. Its regularity,
weighted budget and positive-defect integrals are calculated from the curve. -/
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ResponseTransportSharpness
open Set Filter MeasureTheory ResponseTransport
open scoped Topology

@[expose]  def firstSlope (z0 a ε : ℝ) : ℝ := (a-z0)/ε
@[expose]  def secondSlope (a z1 u v ε : ℝ) : ℝ := (z1-a)/(v-u-ε)
@[expose]  def curve (z0 a z1 u v ε t : ℝ) : ℝ :=
   z0+firstSlope z0 a ε*min (t-u) ε+secondSlope a z1 u v ε*max (t-u-ε) 0
@[expose]  def response (z0 a u ε t : ℝ) : ℝ := if t≤u+ε then firstSlope z0 a ε else 0

 theorem curve_of_le (z0 a z1 u v ε t : ℝ) (ht : t≤u+ε) :
     curve z0 a z1 u v ε t=z0+firstSlope z0 a ε*(t-u) := by
   unfold curve
   rw [min_eq_left (by linarith),max_eq_right (by linarith)]
   ring

 theorem curve_of_ge (z0 a z1 u v ε t : ℝ) (hε : ε≠0) (ht : u+ε≤t) :
     curve z0 a z1 u v ε t=a+secondSlope a z1 u v ε*(t-(u+ε)) := by
   unfold curve firstSlope
   rw [min_eq_right (by linarith),max_eq_left (by linarith)]
   field_simp
   ring

 theorem curve_start (z0 a z1 u v ε : ℝ) (hε : 0≤ε) :
     curve z0 a z1 u v ε u=z0 := by
   rw [curve_of_le _ _ _ _ _ _ _ (by linarith)]
   simp

 theorem curve_end (z0 a z1 u v ε : ℝ) (hε : 0<ε) (hεv : ε<v-u) :
     curve z0 a z1 u v ε v=z1 := by
   rw [curve_of_ge _ _ _ _ _ _ _ hε.ne' (by linarith)]
   unfold secondSlope
   rw [show v-(u+ε)=v-u-ε by ring,div_mul_cancel₀ _ (ne_of_gt (by linarith : 0<v-u-ε))]
   ring

 theorem curve_absolutelyContinuous (z0 a z1 u v ε : ℝ) :
     AbsolutelyContinuousOnInterval (curve z0 a z1 u v ε) u v := by
   have ht : LipschitzWith 1 (fun t : ℝ => t-u) := by
     apply LipschitzWith.of_dist_le_mul
     intro s t
     simp [dist_eq_norm]
   have hs : LipschitzWith 1 (fun t : ℝ => t-u-ε) := by
     apply LipschitzWith.of_dist_le_mul
     intro s t
     simp [dist_eq_norm]
   have hc := ((LipschitzWith.const z0).add
     ((lipschitzWith_smul (firstSlope z0 a ε)).comp (ht.min_const ε))).add
     ((lipschitzWith_smul (secondSlope a z1 u v ε)).comp (hs.max_const 0))
   have hc' : LipschitzWith (‖firstSlope z0 a ε‖₊+‖secondSlope a z1 u v ε‖₊)
       (curve z0 a z1 u v ε) := by
     apply LipschitzWith.of_dist_le_mul
     intro s t
     simpa only [curve,smul_eq_mul,Function.comp_def,dist_eq_norm,zero_add,mul_one] using hc.dist_le_mul s t
   exact (hc'.lipschitzOnWith (s:=uIcc u v)).absolutelyContinuousOnInterval

 theorem curve_nonnegative {z0 a z1 u v ε : ℝ} (hz0 : 0≤z0) (ha : z0≤a)
     (ha1 : a<z1) (hε : 0<ε) (hεv : ε<v-u) {t : ℝ} (ht : t∈Icc u v) :
     0≤curve z0 a z1 u v ε t := by
   unfold curve firstSlope secondSlope
   exact add_nonneg (add_nonneg hz0
     (mul_nonneg (div_nonneg (sub_nonneg.mpr ha) hε.le)
       (le_min (sub_nonneg.mpr ht.1) hε.le)))
     (mul_nonneg (div_nonneg (sub_nonneg.mpr ha1.le) (by linarith)) (le_max_right _ _))

 theorem curve_deriv_left (z0 a z1 u v ε t : ℝ) (ht : t<u+ε) :
     deriv (curve z0 a z1 u v ε) t=firstSlope z0 a ε := by
   have hh : HasDerivAt (fun s : ℝ => z0+firstSlope z0 a ε*(s-u)) (firstSlope z0 a ε) t := by
     simpa using (((hasDerivAt_id t).sub_const u).const_mul (firstSlope z0 a ε)).const_add z0
   exact (hh.congr_of_eventuallyEq ((gt_mem_nhds ht).mono
     (fun s hs => curve_of_le z0 a z1 u v ε s hs.le))).deriv

 theorem curve_deriv_right (z0 a z1 u v ε t : ℝ) (hε : ε≠0) (ht : u+ε<t) :
     deriv (curve z0 a z1 u v ε) t=secondSlope a z1 u v ε := by
   have hh : HasDerivAt (fun s : ℝ => a+secondSlope a z1 u v ε*(s-(u+ε)))
       (secondSlope a z1 u v ε) t := by
     simpa using (((hasDerivAt_id t).sub_const (u+ε)).const_mul (secondSlope a z1 u v ε)).const_add a
   exact (hh.congr_of_eventuallyEq ((lt_mem_nhds ht).mono
     (fun s hs => curve_of_ge z0 a z1 u v ε s hε hs.le))).deriv

 theorem response_intervalIntegrable (z0 a u v ε : ℝ) (hε : 0<ε) (hεv : ε<v-u) :
     IntervalIntegrable (response z0 a u ε) volume u v := by
   have hl : IntervalIntegrable (response z0 a u ε) volume u (u+ε) :=
     (intervalIntegrable_const (c:=firstSlope z0 a ε)).congr_uIoo (by
       intro t ht
       rw [uIoo_of_lt (by linarith : u<u+ε)] at ht
       simp [response,ht.2.le])
   have hr : IntervalIntegrable (response z0 a u ε) volume (u+ε) v :=
     (intervalIntegrable_const (c:=(0:ℝ))).congr_uIoo (by
       intro t ht
       rw [uIoo_of_lt (by linarith : u+ε<v)] at ht
       simp [response,not_le.mpr ht.1])
   exact hl.trans hr

 theorem response_nonnegative {z0 a u ε t : ℝ} (ha : z0≤a) (hε : 0<ε) :
     0≤response z0 a u ε t := by
   unfold response firstSlope
   split_ifs
   · exact div_nonneg (sub_nonneg.mpr ha) hε.le
   · exact le_rfl

 theorem positiveDefect_left (z0 a z1 u v ε t : ℝ) (ht : t<u+ε) :
     positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t=0 := by
   unfold positiveDefect
   rw [curve_deriv_left _ _ _ _ _ _ _ ht]
   simp [response,ht.le]

 theorem positiveDefect_right {z0 a z1 u v ε t : ℝ}
     (ha1 : a<z1) (hε : 0<ε) (hεv : ε<v-u) (ht : u+ε<t) :
     positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t=secondSlope a z1 u v ε := by
   unfold positiveDefect
   rw [curve_deriv_right _ _ _ _ _ _ _ hε.ne' ht]
   simp only [response,if_neg (not_le.mpr ht),sub_zero]
   exact max_eq_left (div_nonneg (sub_nonneg.mpr ha1.le) (by linarith))

 theorem weightedBudget_eq {p : ℕ} (hp : 3≤p) (z0 a z1 u v ε : ℝ)
     (hε : 0<ε) (hεv : ε<v-u) :
     weightedBudget p (curve z0 a z1 u v ε) (response z0 a u ε) u v=(a^p-z0^p)/(p:ℝ) := by
   have hn : (p:ℝ)≠0 := Nat.cast_ne_zero.mpr (by omega)
   have hs : z0+firstSlope z0 a ε*((u+ε)-u)=a := by
     unfold firstSlope
     field_simp
     ring
   have hdc (t : ℝ) : HasDerivAt (fun s : ℝ => (z0+firstSlope z0 a ε*(s-u))^p)
       ((p:ℝ)*(z0+firstSlope z0 a ε*(t-u))^(p-1)*firstSlope z0 a ε) t := by
     have hlin : HasDerivAt (fun s : ℝ => z0+firstSlope z0 a ε*(s-u)) (firstSlope z0 a ε) t := by
       simpa using (((hasDerivAt_id t).sub_const u).const_mul (firstSlope z0 a ε)).const_add z0
     convert hlin.pow p using 1 <;> simp only [Pi.pow_apply]
   have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
     (fun t _ => hdc t) ((by fun_prop : Continuous
       (fun t : ℝ => (p:ℝ)*(z0+firstSlope z0 a ε*(t-u))^(p-1)*firstSlope z0 a ε)).intervalIntegrable u (u+ε))
   have hprod : (fun t : ℝ => (p:ℝ)*(z0+firstSlope z0 a ε*(t-u))^(p-1)*firstSlope z0 a ε)=
       fun t => (p:ℝ)*((z0+firstSlope z0 a ε*(t-u))^(p-1)*firstSlope z0 a ε) := by funext t;ring
   rw [hprod,intervalIntegral.integral_const_mul,hs] at hFTC
   simp only [sub_self,mul_zero,add_zero] at hFTC
   have hleft : (∫t in u..u+ε,(curve z0 a z1 u v ε t)^(p-1)*response z0 a u ε t)=
       (a^p-z0^p)/(p:ℝ) := by
     calc
       _ = ∫t in u..u+ε,(z0+firstSlope z0 a ε*(t-u))^(p-1)*firstSlope z0 a ε := by
         apply intervalIntegral.integral_congr
         intro t ht
         rw [uIcc_of_le (by linarith : u≤u+ε)] at ht
         dsimp only
         rw [curve_of_le _ _ _ _ _ _ _ ht.2]
         simp [response,ht.2]
       _ = _ := (eq_div_iff hn).mpr (by nlinarith [hFTC])
   have hright : (∫t in u+ε..v,(curve z0 a z1 u v ε t)^(p-1)*response z0 a u ε t)=0 := by
     calc
       _ = ∫_t in u+ε..v,(0:ℝ) := by
         apply intervalIntegral.integral_congr_uIoo
         intro t ht
         rw [uIoo_of_lt (by linarith : u+ε<v)] at ht
         simp [response,not_le.mpr ht.1]
       _ = 0 := by simp
   have hi := weightedBudget_intervalIntegrable (p:=p) (curve_absolutelyContinuous z0 a z1 u v ε)
     (response_intervalIntegrable z0 a u v ε hε hεv)
   have hil : IntervalIntegrable (fun t => curve z0 a z1 u v ε t^(p-1)*response z0 a u ε t) volume u (u+ε) :=
     hi.mono_set (by rw [uIcc_of_le (by linarith : u≤v),uIcc_of_le (by linarith : u≤u+ε)]; exact Icc_subset_Icc le_rfl (by linarith))
   have hir : IntervalIntegrable (fun t => curve z0 a z1 u v ε t^(p-1)*response z0 a u ε t) volume (u+ε) v :=
     hi.mono_set (by rw [uIcc_of_le (by linarith : u≤v),uIcc_of_le (by linarith : u+ε≤v)]; exact Icc_subset_Icc (by linarith) le_rfl)
   have hsum := intervalIntegral.integral_add_adjacent_intervals hil hir
   unfold weightedBudget
   rw [←hsum,hleft,hright,add_zero]

 theorem positiveDefect_power_integral {z0 a z1 u v ε : ℝ} (ha1 : a<z1)
     (hε : 0<ε) (hεv : ε<v-u) (n : ℕ) (hn : 0<n) :
     (∫t in u..v,(positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^n)=
       (v-u-ε)*(secondSlope a z1 u v ε)^n := by
   have hl : EqOn (fun _t : ℝ => (0:ℝ))
       (fun t => (positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^n)
       (uIoo u (u+ε)) := by
     intro t ht
     rw [uIoo_of_lt (by linarith : u<u+ε)] at ht
     dsimp only
     rw [positiveDefect_left _ _ _ _ _ _ _ ht.2,zero_pow (by omega)]
   have hr : EqOn (fun _t : ℝ => (secondSlope a z1 u v ε)^n)
       (fun t => (positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^n)
       (uIoo (u+ε) v) := by
     intro t ht
     rw [uIoo_of_lt (by linarith : u+ε<v)] at ht
     dsimp only
     rw [positiveDefect_right ha1 hε hεv ht.1]
   have hli := (intervalIntegrable_const (μ:=volume) (c:=(0:ℝ))).congr_uIoo hl
   have hri := (intervalIntegrable_const (μ:=volume) (c:=(secondSlope a z1 u v ε)^n)).congr_uIoo hr
   rw [←intervalIntegral.integral_add_adjacent_intervals hli hri,
     ←intervalIntegral.integral_congr_uIoo hl,←intervalIntegral.integral_congr_uIoo hr]
   simp only [intervalIntegral.integral_zero,intervalIntegral.integral_const,smul_eq_mul,zero_add]
   congr 1
   ring

 theorem positiveDefect_L1_eq {z0 a z1 u v ε : ℝ} (ha1 : a<z1)
     (hε : 0<ε) (hεv : ε<v-u) :
     (∫t in u..v,positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)=z1-a := by
   have hh := positiveDefect_power_integral (z0:=z0) ha1 hε hεv 1 (by omega)
   simp only [pow_one,secondSlope] at hh
   rw [hh]
   exact mul_div_cancel₀ _ (ne_of_gt (by linarith : 0<v-u-ε))

 theorem positiveDefect_L2_eq {z0 a z1 u v ε : ℝ} (ha1 : a<z1)
     (hε : 0<ε) (hεv : ε<v-u) :
     (v-u)*(∫t in u..v,(positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^2)=
       (v-u)/(v-u-ε)*(z1-a)^2 := by
   rw [positiveDefect_power_integral ha1 hε hεv 2 (by omega),secondSlope]
   field_simp
   <;> ring

 theorem positiveDefect_L2_tendsto {z0 a z1 u v : ℝ} (ha1 : a<z1) (huv : u<v) :
     Tendsto (fun ε : ℝ => (v-u)*(∫t in u..v,
       (positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^2))
       (𝓝[>] (0:ℝ)) (𝓝 ((z1-a)^2)) := by
   have hd : v-u≠0 := ne_of_gt (sub_pos.mpr huv)
   have hc : ContinuousAt (fun ε : ℝ => (v-u)/(v-u-ε)*(z1-a)^2) 0 := by
     apply ContinuousAt.mul
     · exact continuousAt_const.div (continuousAt_const.sub continuousAt_id) (by simpa using hd)
     · exact continuousAt_const
   have ht : Tendsto (fun ε : ℝ => (v-u)/(v-u-ε)*(z1-a)^2)
       (𝓝[>] (0:ℝ)) (𝓝 ((v-u)/(v-u-0)*(z1-a)^2)) := hc.tendsto.mono_left nhdsWithin_le_nhds
   simp only [sub_zero,div_self hd,one_mul] at ht
   apply ht.congr'
   have hs : ∀ᶠε : ℝ in 𝓝[>] (0:ℝ),0<ε ∧ ε<v-u := by
     filter_upwards [self_mem_nhdsWithin,
       (gt_mem_nhds (sub_pos.mpr huv)).filter_mono nhdsWithin_le_nhds] with ε h0 hv
     exact ⟨h0,hv⟩
   exact hs.mono (fun ε hε => (positiveDefect_L2_eq (z0:=z0) ha1 hε.1 hε.2).symm)

 /-- The prescribed-budget extremizer in the exact normalization of Remark 12.5. -/
 theorem actual_source12_5 {p : ℕ} (hp : 3≤p) {z0 z1 J u v : ℝ}
     (hz0 : 0≤z0) (hJ : 0≤J) (huv : u<v)
     (hbar : (z0^p+(p:ℝ)*J)^(1/(p:ℝ))<z1) :
     let a := (z0^p+(p:ℝ)*J)^(1/(p:ℝ));
     (∀ε : ℝ,0<ε→ε<v-u→
       AbsolutelyContinuousOnInterval (curve z0 a z1 u v ε) u v ∧
       curve z0 a z1 u v ε u=z0 ∧ curve z0 a z1 u v ε v=z1 ∧
       (∀t∈Icc u v,0≤curve z0 a z1 u v ε t) ∧
       IntervalIntegrable (response z0 a u ε) volume u v ∧
       (∀t,0≤response z0 a u ε t) ∧
       weightedBudget p (curve z0 a z1 u v ε) (response z0 a u ε) u v=J ∧
       transportDeficit p (curve z0 a z1 u v ε) (response z0 a u ε) u v=z1-a ∧
       (∫t in u..v,positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)=z1-a ∧
       (v-u)*(∫t in u..v,(positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^2)=
         (v-u)/(v-u-ε)*(z1-a)^2) ∧
     Tendsto (fun ε : ℝ => (v-u)*(∫t in u..v,
       (positiveDefect (curve z0 a z1 u v ε) (response z0 a u ε) t)^2))
       (𝓝[>] (0:ℝ)) (𝓝 ((z1-a)^2)) := by
   dsimp only
   let a := (z0^p+(p:ℝ)*J)^(1/(p:ℝ))
   have ha0 : 0≤a := Real.rpow_nonneg (add_nonneg (pow_nonneg hz0 _)
     (mul_nonneg (Nat.cast_nonneg p) hJ)) _
   have hap : a^p=z0^p+(p:ℝ)*J := by
     unfold a
     rw [one_div]
     exact Real.rpow_inv_natCast_pow (add_nonneg (pow_nonneg hz0 _)
       (mul_nonneg (Nat.cast_nonneg p) hJ)) (by omega)
   have hza : z0≤a := le_of_pow_le_pow_left₀ (by omega : p≠0) ha0
     (by rw [hap];exact le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg p) hJ))
   constructor
   · intro ε hε hεv
     have hbudget : weightedBudget p (curve z0 a z1 u v ε) (response z0 a u ε) u v=J := by
       rw [weightedBudget_eq hp z0 a z1 u v ε hε hεv,hap]
       field_simp
       <;> ring
     refine ⟨curve_absolutelyContinuous z0 a z1 u v ε,curve_start z0 a z1 u v ε hε.le,
       curve_end z0 a z1 u v ε hε hεv,fun t ht => curve_nonnegative hz0 hza hbar hε hεv ht,
       response_intervalIntegrable z0 a u v ε hε hεv,fun t => response_nonnegative hza hε,
       hbudget,?_,positiveDefect_L1_eq hbar hε hεv,positiveDefect_L2_eq hbar hε hεv⟩
     unfold transportDeficit budgetRoot
     rw [curve_end z0 a z1 u v ε hε hεv,curve_start z0 a z1 u v ε hε.le,hbudget]
     exact max_eq_left (sub_nonneg.mpr hbar.le)
   · exact positiveDefect_L2_tendsto hbar huv

end SphericalAging.ResponseTransportSharpness
