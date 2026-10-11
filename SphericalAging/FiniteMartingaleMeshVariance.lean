module

public import SphericalAging.FiniteMartingaleVariance
public import StochasticCalculus.UniformPartitionSums

public section

/-! A genuine local mean-square martingale increment estimate yields its
sharp variance bound by finite partitions and the vanishing uniform mesh. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal BigOperators
namespace SphericalAging.FiniteMartingaleMeshVariance
open FiniteMartingaleVariance
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
variable {Ω : Type*} [m : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {F : Filtration ℝ≥0 m} {M : ℝ≥0→Ω→ℝ}

@[expose] def meshSize (S : ℝ≥0) (n : ℕ) : ℝ := (S : ℝ)/((n+1 : ℕ) : ℝ)

theorem meshSize_tendsto_zero (S : ℝ≥0) :
    Tendsto (meshSize S) atTop (𝓝 0) :=
  (tendsto_add_atTop_iff_nat 1).2 (tendsto_const_div_atTop_nhds_zero_nat (S : ℝ))

/-- Exact finite-mesh variance bound, before passing to the mesh limit. -/
theorem finite_grid_variance_bound (hM : Martingale M F P) (hM2 : ∀r,MemLp (M r) 2 P)
    (S : ℝ≥0) (A B : ℝ) (n : ℕ)
    (hstep : ∀i,i<n+1 →
      (∫ ω,(M (uniformPartitionTime S (n+1) (i+1)) ω-M (uniformPartitionTime S (n+1) i) ω)^2 ∂P)≤
        A*meshSize S n+B*(meshSize S n)^2) :
    variance (M S) P-variance (M 0) P≤A*(S : ℝ)+B*(S : ℝ)^2/((n+1 : ℕ) : ℝ) := by
  have hh := partition_variance hM hM2 (uniformPartitionTime S (n+1))
    (monotone_uniformPartitionTime S (n+1)) (n+1)
  have hn : ((n+1 : ℕ) : ℝ≥0)≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have hzero : uniformPartitionTime S (n+1) 0=0 := by simp [uniformPartitionTime]
  have hlast : uniformPartitionTime S (n+1) (n+1)=S := by simp [uniformPartitionTime,hn]
  rw [hzero,hlast] at hh
  have hsum : (∑i∈Finset.range (n+1),
      ∫ ω,(M (uniformPartitionTime S (n+1) (i+1)) ω-M (uniformPartitionTime S (n+1) i) ω)^2 ∂P)≤
      ∑i∈Finset.range (n+1),(A*meshSize S n+B*(meshSize S n)^2) :=
    Finset.sum_le_sum (fun i hi => hstep i (Finset.mem_range.mp hi))
  have hr : ((n+1 : ℕ) : ℝ)≠0 := by exact_mod_cast (Nat.succ_ne_zero n)
  have he : (∑i∈Finset.range (n+1),(A*meshSize S n+B*(meshSize S n)^2))=
      A*(S : ℝ)+B*(S : ℝ)^2/((n+1 : ℕ) : ℝ) := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,meshSize]
    field_simp
    <;> ring
  rw [he] at hsum
  linarith only [hh,hsum]

/-- Local increment bounds are needed only for sufficiently fine grids. -/
theorem variance_le_of_eventually_grid_increment_bound (hM : Martingale M F P)
    (hM2 : ∀r,MemLp (M r) 2 P) (S : ℝ≥0) (A B : ℝ)
    (hstep : ∀ᶠ n in atTop,∀i,i<n+1 →
      (∫ ω,(M (uniformPartitionTime S (n+1) (i+1)) ω-M (uniformPartitionTime S (n+1) i) ω)^2 ∂P)≤
        A*meshSize S n+B*(meshSize S n)^2) :
    variance (M S) P-variance (M 0) P≤A*(S : ℝ) := by
  have hlim : Tendsto (fun n : ℕ => A*(S : ℝ)+B*(S : ℝ)^2/((n+1 : ℕ) : ℝ)) atTop (𝓝 (A*(S : ℝ))) := by
    have hd := (tendsto_add_atTop_iff_nat 1).2
      (tendsto_const_div_atTop_nhds_zero_nat (B*(S : ℝ)^2))
    simpa only [add_zero] using tendsto_const_nhds.add hd
  apply ge_of_tendsto hlim
  exact hstep.mono (fun n hn => finite_grid_variance_bound hM hM2 S A B n hn)

theorem variance_le_of_grid_increment_bound (hM : Martingale M F P)
    (hM2 : ∀r,MemLp (M r) 2 P) (S : ℝ≥0) (A B : ℝ)
    (hstep : ∀n i,i<n+1 →
      (∫ ω,(M (uniformPartitionTime S (n+1) (i+1)) ω-M (uniformPartitionTime S (n+1) i) ω)^2 ∂P)≤
        A*meshSize S n+B*(meshSize S n)^2) :
    variance (M S) P-variance (M 0) P≤A*(S : ℝ) :=
  variance_le_of_eventually_grid_increment_bound hM hM2 S A B (.of_forall hstep)

/-- Remove an arbitrarily small multiplicative loss in the leading local
increment constant; each loss may have its own quadratic error constant. -/
theorem variance_le_of_arbitrarily_small_loss (hM : Martingale M F P)
    (hM2 : ∀r,MemLp (M r) 2 P) (S : ℝ≥0) (A : ℝ) (hA : 0≤A)
    (hstep : ∀η : ℝ,0<η → ∃B : ℝ,0≤B ∧
      ∀ᶠ n in atTop,∀i,i<n+1 →
        (∫ ω,(M (uniformPartitionTime S (n+1) (i+1)) ω-M (uniformPartitionTime S (n+1) i) ω)^2 ∂P)≤
          ((1+η)*A)*meshSize S n+B*(meshSize S n)^2) :
    variance (M S) P-variance (M 0) P≤A*(S : ℝ) := by
  have hv (η : ℝ) (hη : 0<η) : variance (M S) P-variance (M 0) P≤((1+η)*A)*(S : ℝ) := by
    obtain ⟨B,hB,hbounds⟩ := hstep η hη
    exact variance_le_of_eventually_grid_increment_bound hM hM2 S ((1+η)*A) B hbounds
  apply le_of_forall_pos_le_add
  intro ε hε
  have hAS : 0≤A*(S : ℝ) := mul_nonneg hA S.coe_nonneg
  let η := ε/(A*(S : ℝ)+1)
  have hη : 0<η := div_pos hε (by linarith)
  have he : η*(A*(S : ℝ)+1)=ε := by dsimp only [η];field_simp
  have hh := hv η hη
  nlinarith only [hh,he,hη.le]

end SphericalAging.FiniteMartingaleMeshVariance
