module

public import SphericalAging.TranslatedProfileFDT
public import Mathlib.Topology.Order.MonotoneConvergence

public section

/-! Plateau, strict q<1 and response mass follow from continuous FDT
profiles and their physical bounds; none is a cluster input here. -/
noncomputable section
set_option maxHeartbeats 1500000
namespace SphericalAging.StationaryFDTPlateau
open Set Filter MeasureTheory
open scoped Topology

theorem plateau_and_response_mass {c r : ℝ → ℝ}
    (hc : Continuous c) (hr : Continuous r) (hc0 : c 0=1) (hr0 : r 0=1)
    (hcn : ∀ t,0≤t → 0≤c t) (hrn : ∀ t,0≤t → 0≤r t)
    (hfdt : ∀ t,0≤t → HasDerivWithinAt c (-r t) (Ici 0) t) :
    ∃ q : ℝ,0≤q ∧ q<1 ∧ Tendsto c atTop (𝓝 q) ∧
      IntegrableOn r (Ioi 0) ∧ (∫ t in Ioi 0,r t)=1-q := by
  have ha : AntitoneOn c (Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) hc.continuousOn
    · intro t ht
      rw [interior_Ici] at ht ⊢
      exact (hfdt t ht.le).mono Ioi_subset_Ici_self
    · intro t ht
      rw [interior_Ici] at ht
      exact neg_nonpos.mpr (hrn t ht.le)
  let f : ℝ → ℝ := fun t => c (max 0 t)
  have ham : Antitone f := by
    intro s t hst
    change c (max 0 t)≤c (max 0 s)
    exact ha (show max 0 s∈Ici (0:ℝ) from le_max_left 0 s)
      (show max 0 t∈Ici (0:ℝ) from le_max_left 0 t) (max_le_max le_rfl hst)
  have hb : BddBelow (range f) := by
    refine ⟨0,?_⟩
    rintro _ ⟨t,rfl⟩
    exact hcn _ (le_max_left _ _)
  let q : ℝ := ⨅ t,f t
  have hf : Tendsto f atTop (𝓝 q) := tendsto_atTop_ciInf ham hb
  have ht : Tendsto c atTop (𝓝 q) := hf.congr' (by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact congrArg c (max_eq_right ht))
  have hq : 0≤q := ge_of_tendsto ht ((eventually_ge_atTop (0:ℝ)).mono fun t ht => hcn t ht)
  have he : ∀ᶠ t in 𝓝 (0:ℝ),(1/2:ℝ)<r t := hr.continuousAt.eventually
    (lt_mem_nhds (by rw [hr0];norm_num : (1/2:ℝ)<r 0))
  obtain ⟨l,u,h0,hlu⟩ := he.exists_Ioo_subset
  let δ : ℝ := u/2
  have hδ : 0<δ := by dsimp [δ];linarith [h0.2]
  have hlower (t : ℝ) (ht : t∈Icc 0 δ) : (1/2:ℝ)≤r t :=
    (hlu ⟨by linarith [h0.1,ht.1],by dsimp [δ] at ht;linarith [h0.2,ht.2]⟩).le
  have hd t (ht : t∈Ioo 0 δ) : HasDerivAt c (-r t) t :=
    (hfdt t ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hδ.le hc.continuousOn hd
    (hr.neg.intervalIntegrable 0 δ)
  rw [intervalIntegral.integral_neg,hc0] at hFTC
  have hlow := intervalIntegral.integral_mono_on (μ := volume) hδ.le
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (1/2:ℝ)) volume 0 δ)
    (hr.intervalIntegrable 0 δ) hlower
  rw [intervalIntegral.integral_const] at hlow
  simp only [sub_zero,smul_eq_mul] at hlow
  have hqδ : q≤c δ := le_of_tendsto ht ((eventually_ge_atTop δ).mono fun t ht =>
    ha hδ.le (hδ.le.trans ht) ht)
  have hq1 : q<1 := by linarith only [hFTC,hlow,hqδ,hδ]
  have hder t (ht : t∈Ioi 0) : HasDerivAt c (-r t) t :=
    (hfdt t ht.le).hasDerivAt (Ici_mem_nhds ht)
  have hneg t (ht : t∈Ioi 0) : -r t≤0 := neg_nonpos.mpr (hrn t ht.le)
  have hi : IntegrableOn (fun t => -r t) (Ioi 0) :=
    integrableOn_Ioi_deriv_of_nonpos hc.continuousWithinAt hder hneg ht
  have hmass := integral_Ioi_of_hasDerivAt_of_nonpos hc.continuousWithinAt hder hneg ht
  rw [integral_neg,hc0] at hmass
  have hir : IntegrableOn r (Ioi 0) := by
    convert hi.neg using 1
    funext t
    exact (neg_neg (r t)).symm
  exact ⟨q,hq,hq1,ht,hir,by linarith only [hmass]⟩

end SphericalAging.StationaryFDTPlateau
