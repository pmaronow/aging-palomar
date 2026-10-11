module

public import SphericalAging.BackwardStrongTheorem
public import SphericalAging.LateTriangleSup

public section

/-! Literal late-triangle suprema and limsups of source Corollary 11.6.
Response uniform localization and the uniform late Fisher majorant are the
explicit preceding source inputs; the remote derivative conclusion is proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.RemoteEarlierTheorem
open CKSpecification EarlierCovariance GreenCovariance StrongBackwardDefect
  EarlierSmoothing LateTriangleSup

@[expose] def pointQuantity (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  d.R t s+|earlierSlope p β d t s|

/-- Genuine pointwise Fisher comparison on every open causal point. -/
theorem remote_point_bound {p : ℕ} {β : ℝ} {d : CKData}
    (hb : PhysicalBounds d) {a : ℝ→ℝ} (ha : FisherMajorant p β d a)
    {r : ℝ→ℝ} (hmono : AntitoneOn r (Ici 0))
    (hresp : ∀ε : ℝ,0<ε→∀ᶠt : ℝ in atTop,∀s : ℝ,0≤s→s≤t→
      |d.R t s-r (t-s)|≤ε)
    (hlate : ∀ε : ℝ,0<ε→∀ᶠS : ℝ in atTop,∀s : ℝ,S≤s→a s≤ε)
    {D ε : ℝ} (hD : 0<D) (hε : 0<ε) :
    ∀ᶠS : ℝ in atTop,∀t s : ℝ,S≤s→s+D≤t→
      pointQuantity p β d t s≤2*r D+ε := by
  let δ := ε/4
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨U,hU⟩ := eventually_atTop.mp (hresp δ hδ)
  filter_upwards [eventually_ge_atTop (max U 1),hlate (δ^2) (by positivity)] with S hS hA
  intro t s hs ht
  have hs0 : 0<s := by linarith [le_max_right U 1]
  have hst : s<t := by linarith
  have hRt := hb.2 t s hs0.le hst.le
  have hR := hU t (by linarith [le_max_left U 1]) s hs0.le hst.le
  have hdef := (ha.dominates t s hs0 hst).trans (hA s hs)
  have he : |earlierSlope p β d t s-d.R t s|≤δ := by
    dsimp only [backwardDefect] at hdef
    nlinarith [sq_abs (earlierSlope p β d t s-d.R t s),
      abs_nonneg (earlierSlope p β d t s-d.R t s)]
  have hRup : d.R t s≤r D+δ := by
    have hlag : D≤t-s := by linarith
    have hr := hmono hD.le (hD.le.trans hlag) hlag
    linarith [le_abs_self (d.R t s-r (t-s))]
  have hab := abs_sub_le (earlierSlope p β d t s) (d.R t s) 0
  simp only [sub_zero,abs_of_nonneg hRt] at hab
  dsimp only [pointQuantity,δ] at *
  linarith

theorem pointSup_eventually_nonneg {p : ℕ} {β D : ℝ} {d : CKData}
    (hb : PhysicalBounds d) (hD : 0≤D) :
    ∀ᶠS : ℝ in atTop,0≤lateSup (pointQuantity p β d) D S := by
  filter_upwards [eventually_ge_atTop (0:ℝ)] with S hS
  apply lateSup_nonneg
  exact add_nonneg (hb.2 (S+D) S hS (by linarith)) (abs_nonneg _)

/-- Literal source pointwise ordered limit: lim_D limsup_S sup_{late triangle}=0. -/
theorem remote_earlier_limit {p : ℕ} {β : ℝ} {d : CKData}
    (hb : PhysicalBounds d) {a : ℝ→ℝ} (ha : FisherMajorant p β d a)
    {r : ℝ→ℝ} (hmono : AntitoneOn r (Ici 0))
    (hrzero : Tendsto r atTop (𝓝 0))
    (hresp : ∀ε : ℝ,0<ε→∀ᶠt : ℝ in atTop,∀s : ℝ,0≤s→s≤t→
      |d.R t s-r (t-s)|≤ε)
    (hlate : ∀ε : ℝ,0<ε→∀ᶠS : ℝ in atTop,∀s : ℝ,S≤s→a s≤ε) :
    Tendsto (fun D : ℝ => limsup (lateSup (pointQuantity p β d) D) atTop)
      atTop (𝓝 0) := by
  have hup (D : ℝ) (hD : 0<D) :
      limsup (lateSup (pointQuantity p β d) D) atTop≤2*r D :=
    lateSup_limsup_le (pointSup_eventually_nonneg hb hD.le)
      (fun _ hε => remote_point_bound hb ha hmono hresp hlate hD hε)
  apply squeeze_zero' _ _ (by simpa using hrzero.const_mul 2)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
    have hn := pointSup_eventually_nonneg (p:=p) (β:=β) hb hD.le
    have hbnd : IsBoundedUnder (·≤·) atTop (lateSup (pointQuantity p β d) D) :=
      isBoundedUnder_of_eventually_le
        ((remote_point_bound hb ha hmono hresp hlate hD (by norm_num : (0:ℝ)<1)).mono
          (fun _ hS => lateSup_le hS))
    apply le_limsup_of_le hbnd
    intro b hbb
    obtain ⟨S,hS⟩ := (hn.and hbb).exists
    exact hS.1.trans hS.2
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with D hD
    exact hup D hD

@[expose] def windowQuantity (p : ℕ) (β : ℝ) (d : CKData) (D t s : ℝ) : ℝ :=
  ∫u in s-D..s,|earlierSlope p β d t u|

/-- Literal fixed-D limsup of the actual integral suprema in source 11.6. -/
theorem earlier_smoothing_limsup {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d)
    (hforget : ∀s : ℝ,0≤s→Tendsto (fun t => d.C t s) atTop (𝓝 0))
    {a : ℝ→ℝ} (ha : FisherMajorant p β d a) {r : ℝ→ℝ}
    (hr : ContinuousOn r (Ici 0))
    (hrow : Tendsto (responseErrorEnergy d r) atTop (𝓝 0))
    {D : ℝ} (hD : 0<D) (hri : IntegrableOn (fun v => (r v)^2) (Ici D)) :
    limsup (fun S : ℝ => lateSup (windowQuantity p β d D) D (S+D)) atTop≤
      Real.sqrt D*Real.sqrt (responseTail r D) := by
  have hn (S : ℝ) : 0≤lateSup (windowQuantity p β d D) D (S+D) := by
    apply lateSup_nonneg
    exact intervalIntegral.integral_nonneg (by linarith : S+D-D≤S+D)
      (fun _ _ => abs_nonneg _)
  apply le_of_forall_pos_le_add
  intro ε hε
  apply limsup_le_of_le (isCoboundedUnder_le_of_le atTop hn)
  filter_upwards [earlier_smoothing h hb hforget ha hr hrow hD hri hε] with S hS
  exact lateSup_le (fun t s hs ht => hS s t hs ht)

end SphericalAging.RemoteEarlierTheorem
