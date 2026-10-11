module

public import SphericalAging.NestedUniformSup

public section

/-! Exact causal-row suprema from uniform eventual estimates. -/
noncomputable section
open Set Filter
open scoped Topology
namespace SphericalAging.CausalRowSup

@[expose] def rowValues (f : ℝ→ℝ→ℝ) (L t : ℝ) : Set ℝ :=
  {x | x=0 ∨ ∃ s : ℝ,0≤s ∧ s≤t-L ∧ x=|f t s|}
@[expose] def rowSup (f : ℝ→ℝ→ℝ) (L t : ℝ) : ℝ := sSup (rowValues f L t)

theorem rowSup_nonnegative (f : ℝ→ℝ→ℝ) (L t : ℝ) : 0≤rowSup f L t := by
  by_cases hb : BddAbove (rowValues f L t)
  · exact le_csSup hb (Or.inl rfl)
  · simp only [rowSup,csSup_of_not_bddAbove hb,Real.sSup_empty]
    exact le_rfl

theorem rowSup_le {f : ℝ→ℝ→ℝ} {L t B : ℝ} (hB : 0≤B)
    (hb : ∀s : ℝ,0≤s→s≤t-L→|f t s|≤B) : rowSup f L t≤B := by
  apply csSup_le (show (rowValues f L t).Nonempty from ⟨0,Or.inl rfl⟩)
  rintro x (hx | ⟨s,hs,hst,rfl⟩)
  · simpa only [hx] using hB
  · exact hb s hs hst

theorem rowSup_tendsto_zero {f : ℝ→ℝ→ℝ} {L : ℝ}
    (hsmall : ∀ε : ℝ,0<ε→∀ᶠ t : ℝ in atTop,∀s : ℝ,0≤s→s≤t-L→|f t s|≤ε) :
    Tendsto (rowSup f L) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hsmall (ε/2) (by positivity)] with t ht
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (rowSup_nonnegative f L t)]
  have he := rowSup_le (by positivity : 0≤ε/2) ht
  linarith

theorem rowSup_limsup_le {f : ℝ→ℝ→ℝ} {L B : ℝ} (hB : 0≤B)
    (hsmall : ∀ε : ℝ,0<ε→∀ᶠ t : ℝ in atTop,∀s : ℝ,0≤s→s≤t-L→|f t s|≤B+ε) :
    limsup (rowSup f L) atTop≤B := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have he : ∀ᶠ t : ℝ in atTop,rowSup f L t≤B+ε := by
    filter_upwards [hsmall ε hε] with t ht
    exact rowSup_le (by positivity) ht
  exact limsup_le_of_le
    (isCoboundedUnder_le_of_le atTop (rowSup_nonnegative f L)) he

/-- At every nonempty causal row, adjoining zero leaves the literal supremum
unchanged, even when the image is unbounded. -/
theorem rowSup_eq_literal (f : ℝ→ℝ→ℝ) {L t : ℝ} (ht : L≤t) :
    rowSup f L t=sSup ((fun s => |f t s|) '' Icc 0 (t-L)) := by
  let V := (fun s => |f t s|) '' Icc 0 (t-L)
  have hz : |f t 0|∈V := mem_image_of_mem _ ⟨le_rfl,sub_nonneg.mpr ht⟩
  have hne : V.Nonempty := ⟨_,hz⟩
  have hsubset : V⊆rowValues f L t := by
    rintro x ⟨s,hs,rfl⟩
    exact Or.inr ⟨s,hs.1,hs.2,rfl⟩
  by_cases hb : BddAbove V
  · have h0 : 0≤sSup V := (abs_nonneg _).trans (le_csSup hb hz)
    have hv : ∀x∈rowValues f L t,x≤sSup V := by
      rintro x (hx | ⟨s,hs,hst,rfl⟩)
      · simpa only [hx] using h0
      · exact le_csSup hb (mem_image_of_mem _ ⟨hs,hst⟩)
    have hbrow : BddAbove (rowValues f L t) := ⟨sSup V,hv⟩
    apply le_antisymm
    · exact csSup_le ⟨0,Or.inl rfl⟩ hv
    · exact csSup_le hne (fun x hx => le_csSup hbrow (hsubset hx))
  · have hbrow : ¬BddAbove (rowValues f L t) := fun hh => hb (hh.mono hsubset)
    rw [rowSup,csSup_of_not_bddAbove hbrow,csSup_of_not_bddAbove hb]

@[expose] def literalRowSup (f : ℝ→ℝ→ℝ) (L t : ℝ) : ℝ :=
  sSup ((fun s => |f t s|) '' Icc 0 (t-L))

theorem rowSup_eventuallyEq_literal (f : ℝ→ℝ→ℝ) (L : ℝ) :
    rowSup f L =ᶠ[atTop] literalRowSup f L := by
  filter_upwards [eventually_ge_atTop L] with t ht
  exact rowSup_eq_literal f ht

end SphericalAging.CausalRowSup
