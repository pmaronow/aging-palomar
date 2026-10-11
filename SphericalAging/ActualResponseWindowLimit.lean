module

public import SphericalAging.CanonicalAnnealedResponseRepresentative
public import SphericalAging.SignedResponseWindowConvergence

public section

/-! The actual canonical response, along an arbitrary sequence of dimensions,
has every continuous weighted fixed-window limit from precisely the
preceding uniform response primitive bridge. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000
namespace SphericalAging.ActualResponseWindowLimit
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter Topology FiniteModel
  HardSphereDynamics TwoTimeResponseTimeParameter ActualResponseKernel
  ActualEnergyDimensionLimit ActualEnergyUniformBridge WeightedPrimitiveConvergence
  CanonicalAnnealedResponseRepresentative SignedResponseWindowConvergence
  AnnealedHamiltonianEnergyStein AnnealedResponseMatrixContraction
open scoped NNReal ENNReal
variable {p : ℕ}

@[expose] def dimensionResponseRow (hp : 2≤p) (β : ℝ≥0) (dim : ℕ→ℕ) (j : ℕ) : ℝ→ℝ→ℝ :=
  responseRow hp β (dim j-1)

theorem dimensionResponseRow_eq_actual (hp : 2≤p) (β H : ℝ≥0)
    (dim : ℕ→ℕ) (j : ℕ) (hDim : 1≤dim j) (s : WaitingTime H) :
    dimensionResponseRow hp β dim j H s=
      annealedResponse (p:=p) (by omega : dim j≠0) β (dim j+1)
        (modelRadius_pos (dim j)) (modelRadius_sq (dim j)) H s := by
  have hd : dim j-1+1=dim j := Nat.sub_add_cancel hDim
  simpa only [dimensionResponseRow,hd,NNReal.coe_add,NNReal.coe_natCast,NNReal.coe_one] using
    responseRow_eq_annealedResponse hp β H (dim j-1) s

theorem dimensionResponseRow_variation (hp : 2≤p) (β H : ℝ≥0)
    (dim : ℕ→ℕ) (j : ℕ) {t : ℝ} (ht : t∈Icc 0 (H:ℝ)) :
    (∫u in (0:ℝ)..t,|dimensionResponseRow hp β dim j t u|)≤
      (H:ℝ)*Real.sqrt (1+annealedFourthConstant p β H) :=
  responseRow_variation hp β H (dim j-1) ht

/-- Exactly the uniform signed prefix primitive clause of preceding3.3,
expressed using the actual canonical response rows. -/
@[expose] def ResponsePrimitiveBridge (hp : 2≤p) (β : ℝ≥0) (dim : ℕ→ℕ)
    (d : CKSpecification.CKData) : Prop :=
  ∀H : ℝ≥0,TendstoUniformlyOn
    (fun j (q : ℝ×ℝ) => ∫u in (0:ℝ)..q.2,dimensionResponseRow hp β dim j q.1 u-d.R q.1 u)
    (fun _ => 0) atTop (compactTriangle H)

theorem actual_continuous_weighted_window_limit (hp : 2≤p) (β : ℝ≥0)
    (dim : ℕ→ℕ) (d : CKSpecification.CKData) (h : CKSpecification.CKEquations p β d)
    (hprimitive : ResponsePrimitiveBridge hp β dim d) (T L : ℝ≥0)
    (w : ℝ→ℝ) (hw : Continuous w) :
    Tendsto (fun j => ∫u in (T:ℝ)..((T+L:ℝ≥0):ℝ),w (((T+L:ℝ≥0):ℝ)-u)*
      (dimensionResponseRow hp β dim j (T+L) u-d.R (T+L) u)) atTop (nhds 0) := by
  have hh := ck_continuous_weighted_window_limit h T.coe_nonneg L.coe_nonneg
    (le_refl ((T:ℝ)+(L:ℝ)))
    (by positivity : 0≤((T:ℝ)+(L:ℝ))*Real.sqrt (1+annealedFourthConstant p β (T+L)))
    (dimensionResponseRow hp β dim)
    (fun j t ht => responseRow_integrable hp β (dim j-1) ht.1)
    (fun j t ht => by
      simpa only [NNReal.coe_add] using dimensionResponseRow_variation hp β (T+L) dim j ht)
    (by simpa only [NNReal.coe_add] using hprimitive (T+L)) w hw
  simpa only [NNReal.coe_add] using hh

end SphericalAging.ActualResponseWindowLimit
