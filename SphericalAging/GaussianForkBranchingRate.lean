module

public import SphericalAging.HamiltonianTreeLocalEvents

public section

/-! Exponential absorption of the actual orthogonal-fork net bound on a
fixed-depth branching tree. The required branching threshold is constructed
from the actual mesh and concentration constants. -/
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.GaussianForkBranchingRate
open MeasureTheory GaussianForkUniformConcentration HamiltonianTreeLocalEvents BranchingTreeLocalEvents
open GaussianLandscape
variable {N p K : ℕ}

@[expose] def netCost (p : ℕ) (δ ε : ℝ) : ℝ := Real.log (1+2/mesh p δ ε)
@[expose] def rate (ε : ℝ) : ℝ := ε^2/(8*(Real.pi/2)^2)

theorem mesh_positive (hp : 1≤p) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    0<mesh p δ ε := by
  have hp0 : 0<(p:ℝ) := Nat.cast_pos.mpr (by omega)
  have hc : 0<landscapeCeiling p := by
    unfold landscapeCeiling
    linarith [landscapeThreshold_pos p]
  unfold mesh
  positivity

theorem rate_positive (ε : ℝ) (hε : 0<ε) : 0<rate ε := by
  unfold rate
  positivity

theorem exists_branching_threshold (hp : 1≤p) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε) :
    ∃K0 : ℕ,0<K0 ∧ ∀K≥K0,netCost p δ ε+1≤(K:ℝ)*rate ε := by
  have hr := rate_positive ε hε
  obtain ⟨k,hk⟩ := exists_nat_gt ((netCost p δ ε+1)/rate ε)
  refine ⟨k+1,by omega,?_⟩
  intro K hK
  have hkr : (k:ℝ)≤(K:ℝ) := by exact_mod_cast (show k≤K by omega)
  have hh := (div_lt_iff₀ hr).mp hk
  exact hh.le.trans (mul_le_mul_of_nonneg_right hkr hr.le)

theorem actual_localFailure_le_exp (hp : 1≤p) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hK : netCost p δ ε+1≤(K:ℝ)*rate ε) :
    localFailure N p K δ ε≤((K:ℝ)+3)*Real.exp (-(N:ℝ)) := by
  have hmesh := mesh_positive hp δ ε hδ hε
  have hA : 0<1+2/mesh p δ ε := by positivity
  have hpow : (1+2/mesh p δ ε)^N=Real.exp ((N:ℝ)*netCost p δ ε) := by
    rw [Real.exp_nat_mul,netCost,Real.exp_log hA]
  have hexp : (1+2/mesh p δ ε)^N*
      Real.exp (-((K:ℝ)*N)*ε^2/(8*(Real.pi/2)^2))=
      Real.exp ((N:ℝ)*(netCost p δ ε-(K:ℝ)*rate ε)) := by
    rw [hpow,←Real.exp_add]
    congr 1
    unfold rate
    ring
  have he : Real.exp ((N:ℝ)*(netCost p δ ε-(K:ℝ)*rate ε))≤Real.exp (-(N:ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left (show netCost p δ ε-(K:ℝ)*rate ε≤-1 by linarith)
      (Nat.cast_nonneg N : 0≤(N:ℝ))
    simpa only [mul_neg_one] using hh
  unfold localFailure
  have hh := add_le_add (mul_le_mul_of_nonneg_left (hexp.le.trans he) (by norm_num : 0≤(2:ℝ)))
    (le_refl (((K:ℝ)+1)*Real.exp (-(N:ℝ))))
  have hrhs : 2*Real.exp (-(N:ℝ))+((K:ℝ)+1)*Real.exp (-(N:ℝ))=
      ((K:ℝ)+3)*Real.exp (-(N:ℝ)) := by ring
  convert hh.trans_eq hrhs using 1 <;> ring

theorem failureBudget_nonneg (b : ℕ→ℝ) (hb : ∀j,0≤b j) (d : ℕ) : 0≤failureBudget K b d := by
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact add_nonneg (hb d) (mul_nonneg (Nat.cast_nonneg K) ih)

theorem failureBudget_mul (b : ℕ→ℝ) (c : ℝ) (d : ℕ) :
    failureBudget K (fun j => b j*c) d=failureBudget K b d*c := by
  induction d with
  | zero => simp [failureBudget]
  | succ d ih => rw [failureBudget,failureBudget,ih];ring

theorem actual_tree_failure_eventually_exp (hp : 1≤p) (δ ε : ℝ) (hδ : 0<δ) (hε : 0<ε)
    (hK : netCost p δ ε+1≤(K:ℝ)*rate ε) (d : ℕ) :
    ∃N0 : ℕ,∀N≥N0,failureBudget K (fun _ => localFailure N p K δ ε) d≤Real.exp (-(N:ℝ)/2) := by
  let C := failureBudget K (fun _ => (K:ℝ)+3) d
  have hC : 0≤C := failureBudget_nonneg _ (fun _ => by positivity) d
  have hC1 : 0<C+1 := by linarith
  obtain ⟨N0,hN0⟩ := exists_nat_gt (2*Real.log (C+1))
  refine ⟨N0,?_⟩
  intro N hN
  have hNN : (N0:ℝ)≤(N:ℝ) := by exact_mod_cast hN
  have hlog : Real.log (C+1)≤(N:ℝ)/2 := by linarith
  have hCe : C≤Real.exp ((N:ℝ)/2) :=
    (by linarith : C≤C+1).trans ((Real.exp_log hC1).symm.trans_le (Real.exp_le_exp.mpr hlog))
  have hb := failureBudget_mono (K:=K) _ (fun _ => ((K:ℝ)+3)*Real.exp (-(N:ℝ)))
    (fun _ => actual_localFailure_le_exp hp δ ε hδ hε hK) d
  rw [failureBudget_mul] at hb
  calc
    _≤C*Real.exp (-(N:ℝ)) := hb
    _≤Real.exp ((N:ℝ)/2)*Real.exp (-(N:ℝ)) := mul_le_mul_of_nonneg_right hCe (Real.exp_nonneg _)
    _=Real.exp (-(N:ℝ)/2) := by rw [←Real.exp_add];congr 1;ring

end SphericalAging.GaussianForkBranchingRate
