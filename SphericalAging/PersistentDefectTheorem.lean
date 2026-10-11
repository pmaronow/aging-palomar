module

public import SphericalAging.StrictSlowRatio

public section

/-! Complete local manuscript Theorem12.4 for the actual CK positive defect.
Only the exact preceding selected profile, energy, forgetting, scalar sector
and Fisher majorant inputs are supplied; no defect budget or rate limit is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.PersistentDefectTheorem
open CKSpecification GeneralCenterDeficit PlateauAlgebra StrongBackwardDefect
  WeightedSlowRatioTheorem SlowDefectConstants SlowDefectProfile ActualDefectTransport
  PersistentDefectLimits StrictSlowRatio

theorem source12_4 {p : ℕ} {β : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q)
    (hE : Tendsto (energy p β d) atTop (𝓝 (selectedEnergy p β q)))
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hqd : transitionPlateau p≤q) (hm : β^2*marginalityPolynomial p q=1)
    (hβ : transitionBetaSquared p<β^2) {a : ℝ → ℝ} (ha : FisherMajorant p β d a) :
    (0<slowRatio p q ∧ slowRatio p q<1) ∧
    (∀ L : ℝ,0≤L → 0<c L^p-defectBudget p q ∧ 0<mass p q c L) ∧
    MonotoneOn (mass p q c) (Ici 0) ∧
    Tendsto (mass p q c) atTop (𝓝 (limitingMass p q)) ∧
    0<limitingMass p q ∧
    (∀ S L : ℝ,0≤S → 0<L →
      ENNReal.ofReal (mass p q c L)≤
        liminf (fun t : ℝ => ENNReal.ofReal (∫ u in S..t-L,positive p β d t u)) atTop ∧
      ENNReal.ofReal (mass p q c L^2)≤
        liminf (fun t : ℝ => ENNReal.ofReal ((t-L-S)*(∫ u in S..t-L,positive p β d t u^2))) atTop) ∧
    Tendsto (fun t : ℝ => ∫ u in (0:ℝ)..t,positive p β d t u^2) atTop (𝓝 0) ∧
    ENNReal.ofReal (limitingMass p q^2)≤
      liminf (fun t : ℝ => ENNReal.ofReal (t*(∫ u in (0:ℝ)..t,positive p β d t u^2))) atTop ∧
    0<limitingMass p q^2 := by
  have hx := slowRatio_bounds h.spin_ge_three H.q_positive H.plateau_lt_one
    (plateau_strict h.spin_ge_three hqd hm hβ)
  have hpos := limitingMass_positive H hx.1 hx.2
  exact ⟨hx,fun L hL => ⟨profile_radicand_positive H hL hx.1,mass_positive H hL hx.1 hx.2⟩,
    mass_monotone H hx.1 hx.2,mass_tendsto H hx.1,hpos,
    fun S L hS hL => remote_liminf H hS hL hE hf hx.1 hx.2,
    whole_positive_square_tendsto h hf ha,whole_rate_liminf H hE hf hx.1 hx.2,
    sq_pos_of_pos hpos⟩

end SphericalAging.PersistentDefectTheorem
