module

public import SphericalAging.CausalStripDistance

public section

/-! A genuine positive-row averaging limit: bounded profile errors on a fixed
initial interval vanish with its response mass, and the tail is controlled by
the actual total response mass. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.PositiveRowAverage

 theorem weighted_interval_error_bound {D K T m δ : ℝ} (hDK : D≤K) (hKT : K≤T)
    {w f : ℝ→ℝ} (hw : ContinuousOn w (Icc D T)) (hf : ContinuousOn f (Icc D T))
    (hw0 : ∀u∈Icc D T,0≤w u) (hf01 : ∀u∈Icc D T,f u∈Icc (0:ℝ) 1)
    (hm : m∈Icc (0:ℝ) 1) (hδ : 0≤δ)
    (htail : ∀u∈Icc K T,|f u-m|≤δ) :
    |(∫u in D..T,w u*f u)-m*(∫u in D..T,w u)|≤
      (∫u in D..K,w u)+δ*(∫u in D..T,w u) := by
  have hDT := hDK.trans hKT
  have hiw := hw.intervalIntegrable_of_Icc (μ:=volume) hDT
  have hig : IntervalIntegrable (fun u => w u*(f u-m)) volume D T := (hw.mul (hf.sub (continuousOn_const (c:=m)))).intervalIntegrable_of_Icc (μ:=volume) hDT
  have he : (∫u in D..T,w u*f u)-m*(∫u in D..T,w u)=∫u in D..T,w u*(f u-m) := by
    rw [←intervalIntegral.integral_const_mul]
    have hif : IntervalIntegrable (fun u => w u*f u) volume D T := (hw.mul hf).intervalIntegrable_of_Icc hDT
    rw [←intervalIntegral.integral_sub hif (hiw.const_mul m)]
    apply intervalIntegral.integral_congr
    intro u hu
    dsimp only
    ring
  have hgD : IntervalIntegrable (fun u => w u*(f u-m)) volume D K := hig.mono_set (by rw [uIcc_of_le hDT,uIcc_of_le hDK]; exact Icc_subset_Icc le_rfl hKT)
  have hgK : IntervalIntegrable (fun u => w u*(f u-m)) volume K T := hig.mono_set (by rw [uIcc_of_le hDT,uIcc_of_le hKT]; exact Icc_subset_Icc hDK le_rfl)
  have hwD := (hw.mono (Icc_subset_Icc le_rfl hKT)).intervalIntegrable_of_Icc (μ:=volume) hDK
  have hwK := (hw.mono (Icc_subset_Icc hDK le_rfl)).intervalIntegrable_of_Icc (μ:=volume) hKT
  have hbD : ‖∫u in D..K,w u*(f u-m)‖≤∫u in D..K,w u := by
    apply (intervalIntegral.norm_integral_le_integral_norm hDK).trans
    apply intervalIntegral.integral_mono_on hDK hgD.norm hwD
    intro u hu
    have huT := Icc_subset_Icc le_rfl hKT hu
    have h01 := hf01 u huT
    have hb : |f u-m|≤1 := abs_le.mpr (by constructor <;> linarith [h01.1,h01.2,hm.1,hm.2])
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw0 u huT)]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hb (hw0 u huT)
  have hbK : ‖∫u in K..T,w u*(f u-m)‖≤δ*(∫u in K..T,w u) := by
    rw [←intervalIntegral.integral_const_mul]
    apply (intervalIntegral.norm_integral_le_integral_norm hKT).trans
    apply intervalIntegral.integral_mono_on hKT hgK.norm (hwK.const_mul δ)
    intro u hu
    have huT := Icc_subset_Icc hDK le_rfl hu
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (hw0 u huT),mul_comm δ]
    exact mul_le_mul_of_nonneg_left (htail u hu) (hw0 u huT)
  have hμK : (∫u in K..T,w u)≤∫u in D..T,w u := by
    rw [←intervalIntegral.integral_add_adjacent_intervals hwD hwK]
    have hμD : 0≤∫u in D..K,w u := intervalIntegral.integral_nonneg hDK (fun u hu => hw0 u (Icc_subset_Icc le_rfl hKT hu))
    linarith
  rw [he,←Real.norm_eq_abs,←intervalIntegral.integral_add_adjacent_intervals hgD hgK]
  exact (norm_add_le _ _).trans ((add_le_add hbD hbK).trans
    (add_le_add_right (mul_le_mul_of_nonneg_left hμK hδ) _))

 theorem positive_row_average_tendsto {α : Type*} {l : Filter α} [NeBot l]
    {D m M : ℝ} {T : α→ℝ} {w : α→ℝ→ℝ} {f : ℝ→ℝ}
    (hT : Tendsto T l atTop) (hDT : ∀n,D≤T n)
    (hw : ∀n,ContinuousOn (w n) (Icc D (T n)))
    (hw0 : ∀n,∀u∈Icc D (T n),0≤w n u)
    (hf : ContinuousOn f (Ici D)) (hf01 : ∀u∈Ici D,f u∈Icc (0:ℝ) 1)
    (hm : m∈Icc (0:ℝ) 1) (hflim : Tendsto f atTop (𝓝 m))
    (hmass : Tendsto (fun n => ∫u in D..T n,w n u) l (𝓝 M))
    (hearly : ∀K,D≤K → Tendsto (fun n => ∫u in D..K,w n u) l (𝓝 0)) :
    Tendsto (fun n => ∫u in D..T n,w n u*f u) l (𝓝 (m*M)) := by
  have herr : Tendsto (fun n => (∫u in D..T n,w n u*f u)-m*(∫u in D..T n,w n u)) l (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    let δ := ε/(2*(|M|+2))
    have hδ : 0<δ := by dsimp [δ]; positivity
    have ht := hflim.eventually (Metric.ball_mem_nhds m hδ)
    obtain ⟨K0,hK0⟩ := eventually_atTop.mp ht
    let K := max D K0
    have hDK : D≤K := le_max_left _ _
    have htail : ∀u,K≤u → |f u-m|≤δ := by
      intro u hu
      exact (hK0 u ((le_max_right _ _).trans hu)).le
    have hmasslt := hmass.eventually (gt_mem_nhds (show M < |M|+1 from lt_of_le_of_lt (le_abs_self M) (by linarith)))
    have hearlylt := (hearly K hDK).eventually (gt_mem_nhds (show (0:ℝ)<ε/2 by positivity))
    filter_upwards [hT.eventually (eventually_ge_atTop K),hmasslt,hearlylt] with n hn hmn hen
    rw [dist_zero_right,Real.norm_eq_abs]
    have hb := weighted_interval_error_bound hDK hn (hw n)
      (hf.mono (fun u hu => hu.1)) (hw0 n) (fun u hu => hf01 u hu.1) hm hδ.le
      (fun u hu => htail u hu.1)
    have hμ : 0≤∫u in D..T n,w n u := intervalIntegral.integral_nonneg (hDT n) (hw0 n)
    have hδμ : δ*(∫u in D..T n,w n u)<ε/2 := by
      calc
        _ < δ*(|M|+2) := mul_lt_mul_of_pos_left (by linarith) hδ
        _ = ε/2 := by dsimp [δ]; field_simp
    linarith
  have hp := (hmass.const_mul m).add herr
  simpa only [mul_zero,add_zero,add_sub_cancel] using hp

end SphericalAging.PositiveRowAverage
