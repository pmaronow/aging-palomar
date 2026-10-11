module

public import SphericalAging.SphereEulerQuerySpan

public section

/-! The Euler algorithm is literally a measurable function of its initial
vector, Brownian increments and observed gradient vectors. -/
noncomputable section
open MeasureTheory Set
open scoped InnerProductSpace
namespace SphericalAging.SphereEulerQueryData
open HardSphereDynamics SphereEulerCoefficients
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
variable {N p : ℕ}

@[expose] def stepFromGradient (β h : ℝ) (y increment observedGradient : State N) : State N :=
  y+h • (β • projection (clip y) observedGradient-kappa N • clip y)+
    Real.sqrt 2 • projection (clip y) increment

@[expose] def stateFromData (β h : ℝ) (x : State N) (increments gradients : ℕ→State N) : ℕ→State N
  | 0 => x
  | k+1 => stepFromGradient β h (stateFromData β h x increments gradients k) (increments k) (gradients k)

@[expose] def gradientData (β h : ℝ) (J : FiniteModel.Disorder N p) (x : State N)
    (increments : ℕ→State N) (k : ℕ) : State N :=
  hamiltonianGradient J (SphereEulerQuerySpan.query β h J x increments k)

theorem state_eq_stateFromData (β h : ℝ) (J : FiniteModel.Disorder N p) (x : State N)
    (increments : ℕ→State N) (k : ℕ) :
    SphereEulerQuerySpan.state β h J x increments k=
      stateFromData β h x increments (gradientData β h J x increments) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change SphereEulerQuerySpan.step β h J (SphereEulerQuerySpan.state β h J x increments k) (increments k)=
      stepFromGradient β h (stateFromData β h x increments (gradientData β h J x increments) k)
        (increments k) (gradientData β h J x increments k)
    rw [←ih]
    rfl

theorem stateFromData_measurable {Ω : Type*} [MeasurableSpace Ω]
    (β h : ℝ) (x : Ω→State N) (increments gradients : ℕ→Ω→State N) (k : ℕ)
    (hx : Measurable x) (hb : ∀j,j<k → Measurable (increments j))
    (hg : ∀j,j<k → Measurable (gradients j)) :
    Measurable (fun omega => stateFromData β h (x omega) (fun j => increments j omega)
      (fun j => gradients j omega) k) := by
  induction k with
  | zero => exact hx
  | succ k ih =>
    have hi := ih (fun j hj => hb j (Nat.lt_trans hj (Nat.lt_succ_self k)))
      (fun j hj => hg j (Nat.lt_trans hj (Nat.lt_succ_self k)))
    have hc := clip_lipschitz.continuous.measurable.comp hi
    have hbk := hb k (Nat.lt_succ_self k)
    have hgk := hg k (Nat.lt_succ_self k)
    exact (hi.add (((hgk.sub ((hc.inner hgk).div_const (N:ℝ) |>.smul hc)).const_smul β).sub
      (hc.const_smul (kappa N)) |>.const_smul h)).add
        ((hbk.sub ((hc.inner hbk).div_const (N:ℝ) |>.smul hc)).const_smul (Real.sqrt 2))

/-- Any sigma algebra containing the literal previous observations contains
the next Euler state, without needing measurability of undisclosed disorder. -/
theorem state_measurable_from_queries {Ω : Type*} [MeasurableSpace Ω]
    (β h : ℝ) (J : Ω→FiniteModel.Disorder N p) (x : Ω→State N)
    (increments : ℕ→Ω→State N) (k : ℕ) (hx : Measurable x)
    (hb : ∀j,j<k → Measurable (increments j))
    (hg : ∀j,j<k → Measurable (fun omega => gradientData β h (J omega) (x omega)
      (fun r => increments r omega) j)) :
    Measurable (fun omega => SphereEulerQuerySpan.state β h (J omega) (x omega)
      (fun j => increments j omega) k) := by
  have hh := stateFromData_measurable β h x increments
    (fun j omega => gradientData β h (J omega) (x omega) (fun r => increments r omega) j)
    k hx hb hg
  convert hh using 1
  funext omega
  exact state_eq_stateFromData β h (J omega) (x omega) (fun j => increments j omega) k
end SphericalAging.SphereEulerQueryData
