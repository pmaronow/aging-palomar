module

public import SphericalAging.RemoteWeightedBudget
public import SphericalAging.SlowDefectConstants

public section

/-! Actual CK-row positive defect transport, and its genuine limiting distance. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology
namespace SphericalAging.ActualDefectTransport
open CKSpecification CKPhysicalConsequences EarlierCovariance WeightedResponseIdentities
  RecentWeightedResponseLimit WeightedSlowRatioTheorem RemoteWeightedBudget
  GeneralCenterDeficit StrongBackwardDefect ResponseTransport SlowDefectConstants

@[expose] def positive (p : ℕ) (β : ℝ) (d : CKData) (t u : ℝ) : ℝ :=
  max (backwardDefect p β d t u) 0

@[expose] def distance (p : ℕ) (d : CKData) (S L t : ℝ) : ℝ :=
  transportDeficit p (d.C t) (d.R t) S (t-L)

theorem positive_row_continuous {p : ℕ} {β t : ℝ} {d : CKData}
    (h : CKEquations p β d) : ContinuousOn (positive p β d t) (Icc 0 t) :=
  ((slope_row_continuous h).sub (response_row_continuous h)).sup continuousOn_const

theorem distance_bounds {p : ℕ} {β S L t : ℝ} {d : CKData}
    (h : CKEquations p β d) (hS : 0≤S) (hL : 0<L) (ht : S+L<t) :
    distance p d S L t≤(∫ u in S..t-L,positive p β d t u) ∧
      distance p d S L t^2≤(t-L-S)*(∫ u in S..t-L,(positive p β d t u)^2) := by
  have ht0 : 0≤t := by linarith
  have huv : S<t-L := by linarith
  have hsubset : uIcc S (t-L)⊆uIcc 0 t := by
    rw [uIcc_of_le huv.le,uIcc_of_le ht0]
    exact Icc_subset_Icc hS (by linarith)
  have hac := (correlation_row_ac h ht0).mono hsubset
  have hb := physical_bounds_of_equations h
  have hz u (hu : u∈uIcc S (t-L)) : 0≤d.C t u := by
    have hu' := hsubset hu
    rw [uIcc_of_le ht0] at hu'
    exact (hb.1 t u ht0 hu'.1).1
  have hr : IntervalIntegrable (d.R t) volume S (t-L) :=
    ((response_row_continuous h).mono (by
      rw [uIcc_of_le huv.le] at hsubset
      simpa only [uIcc_of_le ht0] using hsubset)).intervalIntegrable_of_Icc huv.le
  have hrn u (hu : u∈uIcc S (t-L)) : 0≤d.R t u := by
    have hu' := hsubset hu
    rw [uIcc_of_le ht0] at hu'
    exact hb.2 t u hu'.1 hu'.2
  have he u (hu : u∈uIoc S (t-L)) : positiveDefect (d.C t) (d.R t) u=positive p β d t u := by
    rw [uIoc_of_le huv.le] at hu
    unfold positiveDefect positive backwardDefect
    rw [(correlation_earlier_hasDerivAt h (by linarith [hu.1]) (by linarith [hu.2])).deriv]
  have hc := (positive_row_continuous h).mono (Icc_subset_Icc hS (by linarith : t-L≤t))
  have hsq : IntervalIntegrable (fun u => positiveDefect (d.C t) (d.R t) u^2) volume S (t-L) := by
    apply (hc.pow 2 |>.intervalIntegrable_of_Icc (μ:=volume) huv.le).congr
    intro u hu
    change positive p β d t u^2=positiveDefect (d.C t) (d.R t) u^2
    rw [he u hu]
  have h1 := response_transport_L1 h.spin_ge_three huv hac hz hr hrn
  have h2 := response_transport_L2_finite h.spin_ge_three huv hac hz hr hrn hsq
  have hEq : (∫ u in S..t-L,positiveDefect (d.C t) (d.R t) u)=
      ∫ u in S..t-L,positive p β d t u :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun u hu => he u hu))
  have hEq2 : (∫ u in S..t-L,positiveDefect (d.C t) (d.R t) u^2)=
      ∫ u in S..t-L,positive p β d t u^2 :=
    intervalIntegral.integral_congr_ae (ae_of_all _ (fun u hu => congrArg (fun x : ℝ => x^2) (he u hu)))
  rw [hEq] at h1
  rw [hEq2] at h2
  exact ⟨h1,h2⟩

theorem distance_tendsto {p : ℕ} {β S L : ℝ} {d : CKData} {h : CKEquations p β d}
    {c r : ℝ → ℝ} {q : ℝ} (H : SelectedInputs h c r q) (hS : 0≤S) (hL : 0≤L)
    (hE : Tendsto (energy p β d) atTop (𝓝 (PlateauAlgebra.selectedEnergy p β q)))
    (hf : ∀s : ℝ,0≤s → Tendsto (fun t => d.C t s) atTop (𝓝 0))
    (hm : 0≤mass p q c L) :
    Tendsto (distance p d S L) atTop (𝓝 (mass p q c L)) := by
  have hp : p≠0 := by have hg:=h.spin_ge_three; omega
  have hb := ((hf S hS).pow p).add (remote_weighted_budget_tendsto H hS hL hE hf)
  simp only [zero_pow hp,zero_add] at hb
  have hroot := hb.rpow_const (Or.inr (inv_nonneg.mpr (Nat.cast_nonneg p)))
  have hc := (recent_coefficients H hL ⟨hL,le_rfl⟩).1
  have hh := (hc.sub hroot).max (tendsto_const_nhds (x:=(0:ℝ)))
  have hh' : Tendsto (distance p d S L) atTop (𝓝 (max (mass p q c L) 0)) := by
    change Tendsto (fun t => distance p d S L t) atTop (𝓝 (max (mass p q c L) 0))
    simpa only [distance,transportDeficit,budgetRoot,weightedBudget,mass,gap,root,one_div] using hh
  rw [max_eq_left hm] at hh'
  exact hh'

end SphericalAging.ActualDefectTransport
