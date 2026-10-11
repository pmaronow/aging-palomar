module

public import SphericalAging.LastCrossing
public import SphericalAging.PersistentDefectTheorem

public section

/-! Literal finite, attained, positive first-passage lags of the actual CK
correlation, and their divergence below the selected plateau. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology
namespace SphericalAging.ActualFirstPassage
open CKSpecification CKPhysicalConsequences GreenCovariance

@[expose] def passageSet (d : CKData) (level s : ℝ) : Set ℝ :=
  {u | 0≤u ∧ d.C (s+u) s≤level}
@[expose] def firstPassage (d : CKData) (level s : ℝ) : ℝ := sInf (passageSet d level s)

theorem passageSet_bddBelow (d : CKData) (level s : ℝ) : BddBelow (passageSet d level s) :=
  ⟨0,fun _ hu => hu.1⟩

theorem passageSet_nonempty {d : CKData} {level s : ℝ} (hl : 0<level)
    (hf : Tendsto (fun t => d.C t s) atTop (𝓝 0)) : (passageSet d level s).Nonempty := by
  have hh := hf.comp (tendsto_atTop_add_const_left atTop s (tendsto_id : Tendsto (id : ℝ → ℝ) atTop atTop))
  obtain ⟨u,hu,he⟩ := ((eventually_ge_atTop (0:ℝ)).and (hh.eventually (gt_mem_nhds hl))).exists
  exact ⟨u,hu,he.le⟩

theorem passageSet_closed {p : ℕ} {β level s : ℝ} {d : CKData}
    (h : CKEquations p β d) (hs : 0≤s) : IsClosed (passageSet d level s) := by
  have hc : Continuous (fun u : ℝ => clampedCorrelation d (s+u) s) :=
    (clampedCorrelation_continuous h).comp ((continuous_const.add continuous_id).prodMk continuous_const)
  have he : passageSet d level s=Ici 0∩{u : ℝ | clampedCorrelation d (s+u) s≤level} := by
    ext u
    constructor
    · intro hu
      exact ⟨hu.1,by change clampedCorrelation d (s+u) s≤level; rw [clampedCorrelation_eq (add_nonneg hs hu.1) hs]; exact hu.2⟩
    · intro hu
      exact ⟨hu.1,by have hh:=hu.2; change clampedCorrelation d (s+u) s≤level at hh; rwa [clampedCorrelation_eq (add_nonneg hs hu.1) hs] at hh⟩
  rw [he]
  exact isClosed_Ici.inter (isClosed_le hc continuous_const)

theorem firstPassage_spec {p : ℕ} {β level s : ℝ} {d : CKData}
    (h : CKEquations p β d) (hs : 0≤s) (hl : 0<level) (hl1 : level<1)
    (hf : Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    0<firstPassage d level s ∧ d.C (s+firstPassage d level s) s=level ∧
      ∀u : ℝ,0≤u → u<firstPassage d level s → level<d.C (s+u) s := by
  have hn := passageSet_nonempty hl hf
  have hb := passageSet_bddBelow d level s
  have hm := (passageSet_closed h hs).csInf_mem hn hb
  change 0≤firstPassage d level s ∧ d.C (s+firstPassage d level s) s≤level at hm
  have hp : 0<firstPassage d level s := by
    by_contra hh
    have he : firstPassage d level s=0 := le_antisymm (le_of_not_gt hh) hm.1
    rw [he,add_zero,h.correlation_diagonal s hs] at hm
    linarith [hm.2]
  have hbefore u (hu : 0≤u) (hup : u<firstPassage d level s) : level<d.C (s+u) s := by
    by_contra hh
    have he := csInf_le hb (show u∈passageSet d level s from ⟨hu,le_of_not_gt hh⟩)
    exact not_le_of_gt hup he
  refine ⟨hp,le_antisymm hm.2 ?_,hbefore⟩
  by_contra hh
  have hc : Continuous (fun u : ℝ => clampedCorrelation d (s+u) s) :=
    (clampedCorrelation_continuous h).comp ((continuous_const.add continuous_id).prodMk continuous_const)
  let θ := firstPassage d level s
  have hgap : 0<level-clampedCorrelation d (s+θ) s := by
    rw [clampedCorrelation_eq (add_nonneg hs hp.le) hs]
    exact sub_pos.mpr (lt_of_not_ge hh)
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x:=θ))
    (level-clampedCorrelation d (s+θ) s) hgap
  let ε := min θ δ/2
  have he0 : 0<ε := div_pos (lt_min hp hδ) (by norm_num)
  have heθ : ε<θ := by have hh:=min_le_left θ δ; dsimp only [ε]; linarith
  have heδ : ε<δ := by have hh:=min_le_right θ δ; dsimp only [ε]; linarith
  have hn : 0≤θ-ε := sub_nonneg.mpr heθ.le
  have hd : dist (θ-ε) θ<δ := by rw [Real.dist_eq,sub_sub_cancel_left,abs_neg,abs_of_pos he0]; exact heδ
  have hnear := hclose hd
  rw [Real.dist_eq] at hnear
  have he : clampedCorrelation d (s+(θ-ε)) s<level := by
    linarith [le_abs_self (clampedCorrelation d (s+(θ-ε)) s-clampedCorrelation d (s+θ) s)]
  rw [clampedCorrelation_eq (add_nonneg hs hn) hs] at he
  have hb := hbefore (θ-ε) hn (by change θ-ε<θ; linarith)
  linarith

theorem firstPassage_tendsto {p : ℕ} {β level q : ℝ} {d : CKData}
    (h : CKEquations p β d) (hl : 0<level) (hlq : level<q) (hq : q<1)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {c : ℝ → ℝ} (hbound : ∀u : ℝ,0≤u → q≤c u)
    (hw : ∀A : ℝ,0≤A → TendstoUniformlyOn
      (fun s u => d.C (s+u) s) c atTop (Icc 0 A)) :
    Tendsto (firstPassage d level) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  let A := max b 1
  have hA : 0≤A := (by norm_num : (0:ℝ)≤1).trans (le_max_right _ _)
  have hu := Metric.tendstoUniformlyOn_iff.mp (hw A hA) (q-level) (sub_pos.mpr hlq)
  filter_upwards [eventually_ge_atTop (0:ℝ),hu] with s hs hsu
  have hp := firstPassage_spec h hs hl (hlq.trans hq) (hf s hs)
  by_contra hh
  have hb : firstPassage d level s≤A := (le_of_not_ge hh).trans (le_max_left _ _)
  have he := hsu (firstPassage d level s) ⟨hp.1.le,hb⟩
  rw [Real.dist_eq,hp.2.1] at he
  have hcp := hbound (firstPassage d level s) hp.1.le
  linarith [le_abs_self (c (firstPassage d level s)-level)]

end SphericalAging.ActualFirstPassage
