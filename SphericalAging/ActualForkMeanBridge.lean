module

public import SphericalAging.ActualOverlapConcentration
public import SphericalAging.StationaryClusterInputs

public section

/-! The exact preceding source3.3 mean bridge, combined with the actual
translated CK cluster convergence on a fixed fork lag window. -/
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.ActualForkMeanBridge
open Set Filter MeasureTheory FiniteModel CKSpecification StationaryClusterInputs
open ActualModelOverlapVariance PrefixRectangleStability
open scoped Topology NNReal

@[expose] def actualMean {N p : ℕ} (β R : ℝ≥0) (hR : 0<(R:ℝ)) (s t : ℝ) : ℝ :=
  ∫z,actualOverlap (p:=p) β R hR s.toNNReal t.toNNReal z ∂AnnealedModelLaw.law N p

/-- This is the preceding source3.3 mean identification, with no fork
moment, overlap concentration, or late-time conclusion in the premise. -/
@[expose] def MeanBridge {p : ℕ} (β : ℝ≥0) (dim : ℕ→ℕ) (R : ℕ→ℝ≥0)
    (hR : ∀j,0<(R j:ℝ)) (d : CKData) : Prop :=
  ∀A : ℝ,0≤A→TendstoUniformlyOn
    (fun j (z : ℝ×ℝ) => actualMean (N:=dim j) (p:=p) β (R j) (hR j) z.1 z.2)
    (fun z => d.C z.1 z.2) atTop (square A)

theorem actualMean_ordered_uniform_profile {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (R : ℕ→ℝ≥0) (hR : ∀j,0<(R j:ℝ))
    (hbridge : MeanBridge (p:=p) β dim R hR d) {L : ℝ} (hL : 0≤L)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠn in atTop,∀ᶠj in atTop,∀a∈Icc 0 L,∀b∈Icc 0 L,
      |actualMean (N:=dim j) (p:=p) β (R j) (hR j) (T n+a) (T n+2*a+b)-c (a+b)|<ε := by
  have hc := Metric.tendstoUniformlyOn_iff.mp (H.correlation (3*L) (by positivity))
    (ε/2) (by positivity)
  filter_upwards [hc] with n hn
  have hA : 0≤T n+3*L+1 := by linarith [hT n]
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (hbridge (T n+3*L+1) hA)
    (ε/2) (by positivity)] with j hj
  intro a ha b hb
  have hz : (a,2*a+b)∈square (3*L) := by
    exact ⟨⟨ha.1,by linarith [ha.2]⟩,⟨by linarith [ha.1,hb.1],by linarith [ha.2,hb.2]⟩⟩
  have hz' : (T n+a,T n+2*a+b)∈square (T n+3*L+1) := by
    exact ⟨⟨by linarith [hT n,ha.1],by linarith [ha.2]⟩,
      ⟨by linarith [hT n,ha.1,hb.1],by linarith [ha.2,hb.2]⟩⟩
  have he : |a-(2*a+b)|=a+b := by
    rw [abs_of_nonpos (by linarith [ha.1,hb.1])]
    ring
  have h1 := hj (T n+a,T n+2*a+b) hz'
  have h2 := hn (a,2*a+b) hz
  simp only [Real.dist_eq] at h1 h2
  rw [abs_sub_comm] at h1 h2
  simp only [he] at h2
  have hsum := abs_sub_le (actualMean (N:=dim j) (p:=p) β (R j) (hR j) (T n+a) (T n+2*a+b))
    (d.C (T n+a) (T n+2*a+b)) (c (a+b))
  have he' : T n+(2*a+b)=T n+2*a+b := by ring
  rw [he'] at h2
  linarith

theorem toNNReal_fork_times {T a b : ℝ} (hT : 0≤T) (ha : 0≤a) (hb : 0≤b) :
    T.toNNReal+a.toNNReal=(T+a).toNNReal ∧
      (T.toNNReal+a.toNNReal)+(a.toNNReal+b.toNNReal)=(T+2*a+b).toNNReal := by
  constructor <;> apply NNReal.eq
  · simp only [NNReal.coe_add,Real.coe_toNNReal T hT,Real.coe_toNNReal a ha,
      Real.coe_toNNReal _ (by positivity : 0≤T+a)]
  · simp only [NNReal.coe_add,Real.coe_toNNReal T hT,Real.coe_toNNReal a ha,
      Real.coe_toNNReal b hb,Real.coe_toNNReal _ (by positivity : 0≤T+2*a+b)]
    ring

end SphericalAging.ActualForkMeanBridge
