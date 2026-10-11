module

public import SphericalAging.CenterThresholdSelection
public import SphericalAging.TreeThresholdProduct
public import SphericalAging.AgingCenterGramSup

public section

/-! Actual three-time CK correlation product from actual positive normalized
centers, proved Gram approximation, and the derived selected-center deficit. -/
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open Set Filter
open scoped Topology InnerProductSpace
namespace SphericalAging.ActualCorrelationProduct
open CKSpecification CKPhysicalConsequences CausalTree CausalTreePositivity CenterNormalization
open CenterThresholdSelection TreeCeilings TreePairDeficit TreeThresholdProduct ProductTransfer

/-- All actual normalized center height overlaps are nonnegative. -/
theorem center_cross_nonnegative {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {s t D : ℝ} (hs : 0≤s) (ht : 0≤t) (j : ℕ) :
    0≤crossMass (normalizedCenter h s D) (normalizedCenter h t D) j :=
  CausalTreePositivity.inner_nonnegative
    (heightProjection_nonnegative (normalizedCenter_nonnegative h hs) j)
    (heightProjection_nonnegative (normalizedCenter_nonnegative h ht) j)

theorem scaled_gram_error {q e C g : ℝ} (hq : 0<q) (he : |g-C/q|≤e) :
    |C-q*g|≤q*e := by
  have heq : C-q*g=-(q*(g-C/q)) := by field_simp [hq.ne']; ring
  rw [heq,abs_neg,abs_mul,abs_of_pos hq]
  exact mul_le_mul_of_nonneg_left he hq.le

/-- The quantitative three-cyclic product transfer is instantiated on the
actual CK tree centers. Its finite hypotheses are actual proved deficit and
Gram bounds; the final uniform theorem below constructs all of them. -/
theorem actual_triple_bound {β : ℝ} {d : CKData} (h : CKEquations 3 β d)
    {q D δ e u s t : ℝ} (hq : 0<q) (hδ : 0<δ) (hδ1 : δ≤1) (he : 0≤e)
    (hu : 0≤u) (hs : 0≤s) (ht : 0≤t)
    (hnu : ‖normalizedCenter h u D‖=1) (hns : ‖normalizedCenter h s D‖=1)
    (hnt : ‖normalizedCenter h t D‖=1)
    (hdu : cubicCeiling-functional (normalizedCenter h u D)≤δ)
    (hds : cubicCeiling-functional (normalizedCenter h s D)≤δ)
    (hdt : cubicCeiling-functional (normalizedCenter h t D)≤δ)
    (hgu : |inner ℝ (normalizedCenter h t D) (normalizedCenter h u D)-d.C t u/q|≤e)
    (hgs : |inner ℝ (normalizedCenter h t D) (normalizedCenter h s D)-d.C t s/q|≤e)
    (hgsu : |inner ℝ (normalizedCenter h s D) (normalizedCenter h u D)-d.C s u/q|≤e) :
    positivePart (d.C t s*d.C s u-q*d.C t u)≤q^2*(thresholdModulus δ+3*e+e^2) ∧
    positivePart (d.C t u*d.C s u-q*d.C t s)≤q^2*(thresholdModulus δ+3*e+e^2) ∧
    positivePart (d.C t u*d.C t s-q*d.C s u)≤q^2*(thresholdModulus δ+3*e+e^2) := by
  let U := normalizedCenter h u D
  let S := normalizedCenter h s D
  let T := normalizedCenter h t D
  have hTU : ∀ j,0≤crossMass T U j := center_cross_nonnegative h ht hu
  have hTS : ∀ j,0≤crossMass T S j := center_cross_nonnegative h ht hs
  have hUS : ∀ j,0≤crossMass U S j := center_cross_nonnegative h hu hs
  have hSU : ∀ j,0≤crossMass S U j := center_cross_nonnegative h hs hu
  have hUT : ∀ j,0≤crossMass U T j := center_cross_nonnegative h hu ht
  have hST : ∀ j,0≤crossMass S T j := center_cross_nonnegative h hs ht
  have hprod1 := threshold_product T U S hnt hnu hns hTU hTS hUS hδ hδ1 hdt hdu hds
  have hprod2 := threshold_product T S U hnt hns hnu hTS hTU hSU hδ hδ1 hdt hds hdu
  have hprod3 := threshold_product U S T hnu hns hnt hUS hUT hST hδ hδ1 hdu hds hdt
  have raw (x : ℝ) {b : ℝ} (hb : positivePart x≤b) : x≤b := (le_max_left x 0).trans hb
  have hgSU := scaled_gram_error hq hgsu
  change |d.C s u-q*inner ℝ S U|≤q*e at hgSU
  rw [real_inner_comm U S] at hgSU
  have hz (V W : Space 2) (hVW : ∀ j,0≤crossMass V W j) (hnV : ‖V‖=1) (hnW : ‖W‖=1) :
      inner ℝ V W∈Icc (0:ℝ) 1 :=
    ⟨TreeGradeSelection.inner_nonneg V W hVW,TreeGradeSelection.inner_le_one V W hnV hnW⟩
  let a : ApproximateTriple q e (thresholdModulus δ) := {
    c12:=d.C t u,c13:=d.C t s,c23:=d.C s u,
    g12:=inner ℝ T U,g13:=inner ℝ T S,g23:=inner ℝ U S,
    correlations_nonneg:=⟨((physical_bounds_of_equations h).1 t u ht hu).1,
      ((physical_bounds_of_equations h).1 t s ht hs).1,
      ((physical_bounds_of_equations h).1 s u hs hu).1⟩,
    overlaps_unit:=⟨hz T U hTU hnt hnu,hz T S hTS hnt hns,hz U S hUS hnu hns⟩,
    approximations:=⟨scaled_gram_error hq hgu,scaled_gram_error hq hgs,hgSU⟩,
    products:=⟨raw _ hprod1,by
      have hh := raw _ hprod2
      rw [real_inner_comm U S] at hh
      exact hh,by
      have hh := raw _ hprod3
      rw [real_inner_comm T U,real_inner_comm T S] at hh
      exact hh⟩ }
  exact all_three_transfers hq.le he (thresholdModulus_nonneg δ) a

@[expose] def productError (q τ : ℝ) : ℝ := q^2*(thresholdModulus τ+3*τ+τ^2)

theorem productError_tendsto (q : ℝ) : Tendsto (productError q) (nhds 0) (nhds 0) := by
  have hl := (((thresholdModulus_tendsto.add (tendsto_id.const_mul 3)).add (tendsto_id.pow 2)).const_mul (q^2))
  unfold productError
  simpa only [mul_zero,zero_pow (by decide : (2:ℕ)≠0),zero_add,add_zero,id_eq] using hl

/-- Full source actual-correlation product, all three cyclic inequalities,
in the equivalent nested uniform epsilon formulation. -/
theorem actual_three_time_product {β : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : Inputs h c r q) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ D : ℝ in atTop,0<D ∧ ∀ᶠ S : ℝ in atTop,∀ u s t : ℝ,
      S+D≤u → u+2*D≤s → s+2*D≤t →
      positivePart (d.C t s*d.C s u-q*d.C t u)≤ε ∧
      positivePart (d.C t u*d.C s u-q*d.C t s)≤ε ∧
      positivePart (d.C t u*d.C t s-q*d.C s u)≤ε := by
  have hτlim : Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsmall := ((productError_tendsto q).comp hτlim).eventually (gt_mem_nhds hε)
  obtain ⟨n,hn⟩ := hsmall.exists
  let τ : ℝ := 1/((n:ℝ)+1)
  have hτ : 0<τ := by dsimp only [τ]; positivity
  have hτ1 : τ≤1 := by
    dsimp only [τ]
    exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have hG := AgingCenterGram.aging_center_gram H.toInputs hτ
  have hE := centers_approach_threshold H hτ
  filter_upwards [hG,hE] with D hG hE
  have hDpos := hG.1
  refine ⟨hDpos,?_⟩
  filter_upwards [hG.2,hE.2,eventually_ge_atTop (0:ℝ)] with S hG hE hS
  intro u s t hu hs ht
  have hsS : S+D≤s := by linarith [hDpos]
  have htS : S+D≤t := by linarith [hDpos]
  have hu0 : 0≤u := by linarith [hDpos]
  have hs0 : 0≤s := by linarith [hDpos]
  have ht0 : 0≤t := by linarith [hDpos]
  have hut : u+2*D≤t := by linarith [hDpos]
  have hgu := (hG u t hu hut).2.2.2.2
  have hgs := (hG s t hsS ht).2.2.2.2
  have hgsu := (hG u s hu hs).2.2.2.2
  have heU := hE u hu
  have heS := hE s hsS
  have heT := hE t htS
  have hb := actual_triple_bound h H.q_positive hτ hτ1 hτ.le hu0 hs0 ht0
    heU.1 heS.1 heT.1 heU.2 heS.2 heT.2 hgu hgs hgsu
  exact ⟨hb.1.trans hn.le,hb.2.1.trans hn.le,hb.2.2.trans hn.le⟩

end SphericalAging.ActualCorrelationProduct
