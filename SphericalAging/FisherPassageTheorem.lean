module

public import SphericalAging.FisherObstructionTheorem
public import SphericalAging.FisherSmallWindows
public import SphericalAging.FirstPassageFisherTail

public section

/-! Complete local source15.1 from the actual cubic selected profile,
preceding Fisher majorant and genuine source15.3 obstruction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace SphericalAging.FisherPassageTheorem
open CKSpecification StrongBackwardDefect GeneralCenterDeficit ActualFirstPassage
  FirstPassageSelected FirstPassageFisherWindow FirstPassageFisherTail FisherSmallWindows
  FisherPhysicalWindow FisherCost FisherObstructionTheorem

theorem selected_inputs {β q : ℝ} {d : CKData} {h : CKEquations 3 β d} {c r : ℝ → ℝ}
    (H : CubicResponseLocalization.Inputs h c r q) : SelectedInputs h c r q :=
  ⟨H.q_positive,H.plateau_lt_one,H.correlation_continuous,H.correlation_initial,
    H.correlation_bounds,H.plateau_limit,H.response_continuous,H.response_integrable,H.fdt,
    H.multiplier_limit,H.translated_correlation,H.translated_response,H.reflected_prefix⟩

@[expose] def Conclusions (β q : ℝ) (d : CKData) (a : ℝ → ℝ) : Prop :=
  (∀s τ : ℕ → ℝ,Tendsto s atTop atTop → Tendsto τ atTop atTop →
    Tendsto (fun n => τ n*(∫ u in (s n)..(s n+τ n),a u)) atTop (𝓝 0) →
    Tendsto (fun n => d.C (s n+τ n) (s n)) atTop (𝓝 q) ∧
    Tendsto (fun n => susceptibility d (s n+τ n) (s n)) atTop (𝓝 (1-q))) ∧
  (∀level : ℝ,level∈Ioo 0 q →
    (∀s : ℝ,0≤s → 0<firstPassage d level s ∧
      d.C (s+firstPassage d level s) s=level ∧
      ∀u : ℝ,0≤u → u<firstPassage d level s → level<d.C (s+u) s) ∧
    Tendsto (firstPassage d level) atTop atTop ∧
    0<fisherCost (β^2) q level (PlateauAlgebra.multiplier 3 β q) ∧
    ENNReal.ofReal (fisherCost (β^2) q level (PlateauAlgebra.multiplier 3 β q))≤
      liminf (fun s : ℝ => ENNReal.ofReal (firstPassage d level s*(∫u in s..(s+firstPassage d level s),a u))) atTop ∧
    ENNReal.ofReal (fisherCost (β^2) q level (PlateauAlgebra.multiplier 3 β q))≤
      liminf (fun s : ℝ => ENNReal.ofReal (firstPassage d level s*(∫u in Ioi s,a u))) atTop)

theorem source15_1 {β q : ℝ} {d : CKData} {h : CKEquations 3 β d} {c r a : ℝ → ℝ}
    (H : CubicResponseLocalization.Inputs h c r q) (hq : 1/2<q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (ha : FisherMajorant 3 β d a) : Conclusions β q d a := by
  have HS := selected_inputs H
  have hcal : 6*β^2*q*(1-q)^2=1 := by
    have hh := H.marginality
    norm_num [PlateauAlgebra.marginalityPolynomial] at hh
    nlinarith [hh]
  have hmult : PlateauAlgebra.multiplier 3 β q=1/(1-q)+3*β^2*(1-q^2) := by
    norm_num only [PlateauAlgebra.multiplier,Nat.cast_ofNat,Nat.reduceSub]
    ring
  have hell := multiplier_pos (β^2) q (PlateauAlgebra.multiplier 3 β q)
    (sq_nonneg β) H.q_positive.le H.plateau_lt_one hmult
  constructor
  · intro s τ hs hτ hc
    have hgap : Tendsto (fun n => s n+τ n-s n) atTop atTop := by simpa only [add_sub_cancel_left] using hτ
    have hcost : Tendsto (fun n => fisherWindow a (s n) (s n+τ n)) atTop (𝓝 0) := by
      simpa only [fisherWindow,add_sub_cancel_left] using hc
    have hobs (s t : ℕ → ℝ) (hs : Tendsto s atTop atTop)
        (ht : Tendsto (fun n => t n-s n) atTop atTop) (z : ℝ) (hz : z∈Ioo 0 q)
        (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z))
        (he : Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 0)) : margin (β^2) q z≤0 := by
      have hh := source15_3 H hf ha hs ht hC he hz (by norm_num : (0:ℝ)≤1)
      simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using hh
    have hen (s t : ℕ → ℝ) (hs : Tendsto s atTop atTop)
        (ht : Tendsto (fun n => t n-s n) atTop atTop) (ε : ℝ) (hε : 0<ε) := AgingCenterGram.remote_covariance_envelope
      (ActualProductFromSelected.center_gram_inputs H hf ⟨a,ha⟩) hs ht hε
    have hC := correlation_limit_from_zero_obstruction HS ha hq hf hobs hen hs hgap hcost
    exact ⟨hC,susceptibility_limit_of_small_window h ha hs hgap hcost hC⟩
  · intro level hl
    have hp := actual_first_passages HS hl hf
    have hlocal := local_cost_from_sequential_obstruction HS ha hl hq hell hf
      (fun s t hs ht hC ε hε he => source15_3 H hf ha hs ht hC he hl hε.2)
    refine ⟨hp.1,hp.2,fisherCost_pos (β^2) q level (PlateauAlgebra.multiplier 3 β q)
      hq H.plateau_lt_one hl.1 hl.2 hcal hmult,?_,?_⟩
    · simpa only [fisherWindow,add_sub_cancel_left] using hlocal
    · exact hlocal.trans (local_liminf_le_tail_liminf HS ha hl hf)

end SphericalAging.FisherPassageTheorem
