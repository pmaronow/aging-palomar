module

public import SphericalAging.TwoMomentL2Transfer

public section

/-! Literal lag-window supremum and dimension-limsup passage used in the
source10.3 fork overlap convergence. -/
noncomputable section
set_option maxHeartbeats 1300000
namespace SphericalAging.ForkOverlapSupLimit
open Set Filter
open scoped Topology

@[expose] def window (L : ℝ) : Set (ℝ×ℝ) := Icc 0 L×ˢIcc 0 L
@[expose] def windowSup (f : ℕ→ℕ→ℝ×ℝ→ℝ) (L : ℝ) (n j : ℕ) : ℝ :=
  sSup (f n j ''window L)

theorem window_nonempty {L : ℝ} (hL : 0≤L) : (window L).Nonempty :=
  ⟨(0,0),⟨⟨le_rfl,hL⟩,⟨le_rfl,hL⟩⟩⟩

theorem windowSup_bounds {f : ℕ→ℕ→ℝ×ℝ→ℝ} {L M : ℝ} (hL : 0≤L)
    (hn : ∀n j z,z∈window L→0≤f n j z)
    (hb : ∀n j z,z∈window L→f n j z≤M) (n j : ℕ) :
    0≤windowSup f L n j ∧ windowSup f L n j≤M := by
  have hB : BddAbove (f n j ''window L) := ⟨M,by rintro _ ⟨z,hz,rfl⟩;exact hb n j z hz⟩
  obtain ⟨z,hz⟩ := window_nonempty hL
  exact ⟨(hn n j z hz).trans (le_csSup hB (mem_image_of_mem _ hz)),
    csSup_le ((window_nonempty hL).image _) (by rintro _ ⟨z,hz,rfl⟩;exact hb n j z hz)⟩

theorem ordered_uniform_limsup {f : ℕ→ℕ→ℝ×ℝ→ℝ} {L M : ℝ} (hL : 0≤L)
    (hn : ∀n j z,z∈window L→0≤f n j z)
    (hb : ∀n j z,z∈window L→f n j z≤M)
    (hs : ∀ε>0,∀ᶠn in atTop,∀ᶠj in atTop,∀z∈window L,f n j z<ε) :
    Tendsto (fun n => limsup (windowSup f L n) atTop) atTop (𝓝 0) := by
  have h0 n j := (windowSup_bounds hL hn hb n j).1
  have hM n j := (windowSup_bounds hL hn hb n j).2
  have hnlim n : 0≤limsup (windowSup f L n) atTop := by
    apply le_limsup_of_le (isBoundedUnder_of_eventually_le (Eventually.of_forall (hM n)))
    intro b hb'
    obtain ⟨j,hj⟩ := hb'.exists
    exact (h0 n j).trans hj
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hs (ε/2) (by positivity)] with n hnε
  have hinner : ∀ᶠj in atTop,windowSup f L n j≤ε/2 := by
    filter_upwards [hnε] with j hjε
    exact csSup_le ((window_nonempty hL).image _) (by
      rintro _ ⟨z,hz,rfl⟩
      exact (hjε z hz).le)
  have hh := limsup_le_of_le (isCoboundedUnder_le_of_le atTop (h0 n)) hinner
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (hnlim n)]
  linarith

end SphericalAging.ForkOverlapSupLimit
