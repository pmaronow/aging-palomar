module

public import SphericalAging.FisherMemoryLower
public import SphericalAging.FisherMemoryCompactness

public section

/-! Complete local source15.3, assembled from genuine actual response and
memory estimates. No response/memory obstruction is a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.FisherObstructionTheorem
open CKSpecification StrongBackwardDefect FisherPhysicalWindow FisherPhysicalMemory
  FisherResponseLimit FisherMemoryCompactness FisherMemoryLower FisherCost

theorem source15_3 {β q z ε : ℝ} {d : CKData} {h : CKEquations 3 β d}
    {c r a : ℝ → ℝ} (H : CubicResponseLocalization.Inputs h c r q)
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (ha : FisherMajorant 3 β d a) {s t : ℕ → ℝ}
    (hs : Tendsto s atTop atTop) (hgap : Tendsto (fun n => t n-s n) atTop atTop)
    (hC : Tendsto (fun n => d.C (t n) (s n)) atTop (𝓝 z))
    (he : Tendsto (fun n => windowError a (s n) (t n)) atTop (𝓝 ε))
    (hz : z∈Ioo 0 q) (_hε : ε≤1) :
    margin (β^2) q z≤(PlateauAlgebra.multiplier 3 β q+9*β^2)*ε+6*β^2*ε^2 := by
  have hε0 : 0≤ε := ge_of_tendsto' he (fun _ => Real.sqrt_nonneg _)
  obtain ⟨I,_hI,φ,hφ,hIlim⟩ := memory_convergent_subsequence h ha hs hgap he
  have hs' := hs.comp hφ.tendsto_atTop
  have hgap' := hgap.comp hφ.tendsto_atTop
  have hC' := hC.comp hφ.tendsto_atTop
  have he' := he.comp hφ.tendsto_atTop
  have hmem := memory_limit_lower H hf ha hs' hgap' hC' he' hz hIlim
  have hresponse := response_limit_upper H hf ha hs' hgap' hC' he' hε0 hIlim
  have hcal : 6*β^2*q*(1-q)^2=1 := by
    have hh := H.marginality
    norm_num [PlateauAlgebra.marginalityPolynomial] at hh
    nlinarith [hh]
  have hmult : PlateauAlgebra.multiplier 3 β q=1/(1-q)+3*β^2*(1-q^2) := by
    norm_num only [PlateauAlgebra.multiplier,Nat.cast_ofNat,Nat.reduceSub]
    ring
  exact obstruction_of_memory_and_response (β^2) q z (PlateauAlgebra.multiplier 3 β q) ε I
    (sq_nonneg β) H.plateau_lt_one hcal hmult hmem hresponse

end SphericalAging.FisherObstructionTheorem
