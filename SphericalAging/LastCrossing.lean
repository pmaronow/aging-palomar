module

public import SphericalAging.ActualCorrelationProductSup
public import Mathlib.Topology.Order.Monotone

public section

/-! Literal last-crossing times of the actual CK correlation. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology
namespace SphericalAging.LastCrossing
open CKSpecification GreenCovariance CKPhysicalConsequences

@[expose] def crossingSet (d : CKData) (level s : ℝ) : Set ℝ :=
  {t | s≤t ∧ level≤d.C t s}
@[expose] def lastCrossing (d : CKData) (level s : ℝ) : ℝ := sSup (crossingSet d level s)

theorem crossingSet_bddAbove {d : CKData} {level s : ℝ} (hl : 0<level)
    (hforget : Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    BddAbove (crossingSet d level s) := by
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hforget.eventually (gt_mem_nhds hl))
  refine ⟨U,?_⟩
  intro t ht
  by_contra hh
  have he := hU t (le_of_not_ge hh)
  exact (not_lt_of_ge ht.2) he

theorem crossingSet_nonempty {p : ℕ} {β level s : ℝ} {d : CKData}
    (h : CKEquations p β d) (hs : 0≤s) (hl : level≤1) :
    (crossingSet d level s).Nonempty :=
  ⟨s,le_rfl,by simpa only [h.correlation_diagonal s hs] using hl⟩

theorem crossingSet_closed {p : ℕ} {β level s : ℝ} {d : CKData}
    (h : CKEquations p β d) (hs : 0≤s) : IsClosed (crossingSet d level s) := by
  have hc : Continuous (fun t : ℝ => clampedCorrelation d t s) :=
    (clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
  have he : crossingSet d level s=Ici s∩{t : ℝ | level≤clampedCorrelation d t s} := by
    ext t
    constructor
    · intro ht
      refine ⟨ht.1,?_⟩
      change level≤clampedCorrelation d t s
      rw [clampedCorrelation_eq (hs.trans ht.1) hs]
      exact ht.2
    · intro ht
      refine ⟨ht.1,?_⟩
      have hh := ht.2
      change level≤clampedCorrelation d t s at hh
      rwa [clampedCorrelation_eq (hs.trans ht.1) hs] at hh
  rw [he]
  exact isClosed_Ici.inter (isClosed_le continuous_const hc)

/-- The literal last-crossing supremum exists as a finite real time, lies
after s, and its actual correlation equals the level exactly. -/
theorem lastCrossing_spec {p : ℕ} {β level s : ℝ} {d : CKData}
    (h : CKEquations p β d) (hs : 0≤s) (hl : 0<level) (hl1 : level≤1)
    (hforget : Tendsto (fun t => d.C t s) atTop (𝓝 0)) :
    s≤lastCrossing d level s ∧ d.C (lastCrossing d level s) s=level := by
  have hb := crossingSet_bddAbove hl hforget
  have hn := crossingSet_nonempty h hs hl1
  have hm := (crossingSet_closed h hs).csSup_mem hn hb
  change s≤lastCrossing d level s ∧ level≤d.C (lastCrossing d level s) s at hm
  refine ⟨hm.1,le_antisymm ?_ hm.2⟩
  by_contra hlt
  have hc : Continuous (fun t : ℝ => clampedCorrelation d t s) :=
    (clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
  let θ := lastCrossing d level s
  have hθ : 0≤θ := hs.trans hm.1
  have hgap : 0<clampedCorrelation d θ s-level := by
    rw [clampedCorrelation_eq hθ hs]
    dsimp only [θ]
    linarith
  obtain ⟨δ,hδ,hclose⟩ := Metric.continuousAt_iff.mp (hc.continuousAt (x:=θ))
    (clampedCorrelation d θ s-level) hgap
  have hnear : dist (θ+δ/2) θ<δ := by rw [Real.dist_eq]; simp only [add_sub_cancel_left]; rw [abs_of_pos (by positivity : 0<δ/2)]; linarith
  have hv := hclose hnear
  rw [Real.dist_eq] at hv
  have hmore : level≤clampedCorrelation d (θ+δ/2) s := by
    linarith [neg_le_abs (clampedCorrelation d (θ+δ/2) s-clampedCorrelation d θ s)]
  have hmem : θ+δ/2∈crossingSet d level s := by
    refine ⟨by dsimp only [θ]; linarith [hm.1],?_⟩
    rwa [clampedCorrelation_eq (by linarith) hs] at hmore
  have he : θ+δ/2≤θ := le_csSup hb hmem
  linarith

/-- Every fixed stationary lag has correlation above a subplateau level;
therefore the literal last-crossing lag tends to infinity. -/
theorem lastCrossing_lag_tendsto {p : ℕ} {β level q : ℝ} {d : CKData}
    (h : CKEquations p β d) (hl : 0<level) (hlq : level<q)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {c : ℝ→ℝ} (hprofile : ∀W : ℝ,0≤W→q≤c W)
    (hwindow : ∀W : ℝ,0≤W→Tendsto (fun s => d.C (s+W) s) atTop (𝓝 (c W))) :
    Tendsto (fun s => lastCrossing d level s-s) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  let W := max b 1
  have hW : 0≤W := by dsimp [W]; positivity
  have hlev : level<c W := hlq.trans_le (hprofile W hW)
  filter_upwards [eventually_ge_atTop (0:ℝ),
    (hwindow W hW).eventually (lt_mem_nhds hlev)] with s hs hCs
  have hmem : s+W∈crossingSet d level s := ⟨by linarith,hCs.le⟩
  have he := le_csSup (crossingSet_bddAbove hl (hforget s hs)) hmem
  change s+W≤lastCrossing d level s at he
  have hWb : b≤W := le_max_left _ _
  linarith

end SphericalAging.LastCrossing
