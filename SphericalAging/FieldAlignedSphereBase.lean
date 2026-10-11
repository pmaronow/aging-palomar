module

public import SphericalAging.HamiltonianTreeEnergy

public section

/-! A constructed sphere point attaining the support functional of the
actual deterministic external field, including the zero-field case. -/
noncomputable section
set_option maxHeartbeats 1000000
namespace SphericalAging.FieldAlignedSphereBase
open FiniteModel HamiltonianTreeEnergy
open scoped InnerProductSpace
variable {N : ℕ}

@[expose] def fieldSize (N : ℕ) (h : Vector N) : ℝ := ‖h‖/Real.sqrt N

@[expose] def alignedBase (N : ℕ) (hN : 0<N) (r : ℝ) (h : Vector N) : Vector N :=
  if h=0 then referenceBase N hN r else (Real.sqrt ((N:ℝ)*r)/‖h‖)•h

theorem fieldSize_nonneg (h : Vector N) : 0≤fieldSize N h := by
  unfold fieldSize
  positivity

theorem field_norm (hN : 0<N) (h : Vector N) : ‖h‖=Real.sqrt N*fieldSize N h := by
  have hs : Real.sqrt (N:ℝ)≠0 := (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)).ne'
  unfold fieldSize
  exact (mul_div_cancel₀ _ hs).symm

theorem alignedBase_norm (hN : 0<N) (r : ℝ) (hr : 0≤r) (h : Vector N) :
    ‖alignedBase N hN r h‖^2=(N:ℝ)*r := by
  by_cases hh : h=0
  · simpa only [alignedBase,if_pos hh] using referenceBase_norm hN r hr
  · have hn : 0<‖h‖ := norm_pos_iff.mpr hh
    simp only [alignedBase,if_neg hh,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (Real.sqrt_nonneg _) hn.le),div_mul_cancel₀ _ hn.ne']
    exact Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg N) hr)

theorem alignedBase_pairing (hN : 0<N) (r : ℝ) (hr : 0≤r) (h : Vector N) :
    ⟪h,alignedBase N hN r h⟫_ℝ/(N:ℝ)=fieldSize N h*Real.sqrt r := by
  by_cases hh : h=0
  · simp [alignedBase,hh,fieldSize]
  · have hn : 0<‖h‖ := norm_pos_iff.mpr hh
    have hdim : 0<(N:ℝ) := Nat.cast_pos.mpr hN
    have hs : 0<Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr hdim
    simp only [alignedBase,if_neg hh,inner_smul_right,real_inner_self_eq_norm_sq,fieldSize]
    rw [Real.sqrt_mul hdim.le]
    field_simp [hn.ne',hdim.ne',hs.ne']
    rw [Real.sq_sqrt hdim.le]
    ring

end SphericalAging.FieldAlignedSphereBase
