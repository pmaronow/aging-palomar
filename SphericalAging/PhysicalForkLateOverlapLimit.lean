module

public import SphericalAging.PhysicalForkOverlapAggregation
public import SphericalAging.ForkOverlapSupLimit

public section

/-! Literal source10.4 Step4 window supremum, dimension limsup, then
stationary-time limit, for the actual finite-fork mean and branch. -/
noncomputable section
set_option maxHeartbeats 1700000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PhysicalForkLateOverlapLimit
open MeasureTheory ProbabilityTheory Filter Set FiniteModel HardSphereDynamics
open PhysicalForkConstruction PhysicalForkOverlapAggregation WienerForkTransfer ForkParameterBounds
open AnnealedHamiltonianEnergyStein CKSpecification StationaryClusterInputs ActualForkMeanBridge
open SphereFisherHelly ActualSphereForkEndpoints
open scoped NNReal ENNReal Topology InnerProductSpace BigOperators
variable {N p K : ℕ}

lemma pairOverlap_abs_le_one (hN : 0<N) (β : ℝ) (T L v : ℝ≥0) (b k : Fin K) :
    ∀ᵐz ∂forkLaw N p K,|pairOverlap (N:=N) (p:=p) β T L v b k z|≤1 := by
  filter_upwards [branch_norm_sq (fork_joint_law (N:=N) (p:=p) (K:=K) β (T+L) T) k,
    branch_norm_sq (fork_joint_law (N:=N) (p:=p) (K:=K) β (T+v) T) b] with z hy hz
  exact FiniteCorrelationIto.overlap_abs_le_one hN
    ((onSphere_iff_norm_sq _).mpr hy) ((onSphere_iff_norm_sq _).mpr hz)

lemma meanOverlap_memLp (hN : 0<N) (β : ℝ) (T L v : ℝ≥0) (b : Fin K) :
    MemLp (meanOverlap (N:=N) (p:=p) β T L v b) 2 (forkLaw N p K) := by
  have hh := (memLp_finsetSum Finset.univ (fun k _ => pairOverlap_memLp (p:=p) hN β T L v b k)).const_mul (K:ℝ)⁻¹
  have he : meanOverlap (N:=N) (p:=p) β T L v b=
      fun z => (K:ℝ)⁻¹*∑k,pairOverlap β T L v b k z :=
    funext (fun z => meanOverlap_eq_average β T L v b z)
  rw [he]
  exact hh

lemma meanOverlap_abs_le_one (hN : 0<N) (hK : 0<K) (β : ℝ) (T L v : ℝ≥0) (b : Fin K) :
    ∀ᵐz ∂forkLaw N p K,|meanOverlap (N:=N) (p:=p) β T L v b z|≤1 := by
  have hh := ae_all_iff.mpr (fun k : Fin K => pairOverlap_abs_le_one (p:=p) hN β T L v b k)
  filter_upwards [hh] with z hz
  rw [meanOverlap_eq_average,abs_mul,abs_of_nonneg (by positivity : 0≤(K:ℝ)⁻¹)]
  calc
    _≤(K:ℝ)⁻¹*∑k,|pairOverlap β T L v b k z| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _≤(K:ℝ)⁻¹*∑_k : Fin K,(1:ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun k _ => hz k)) (by positivity)
    _=1 := by simp [ne_of_gt (Nat.cast_pos.mpr hK : (0:ℝ)<K)]

lemma centered_square_bound {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {f : Ω→ℝ} (hf : MemLp f 2 μ)
    (hb : ∀ᵐz ∂μ,|f z|≤1) {a : ℝ} (ha : |a|≤1) :
    (∫z,(f z-a)^2 ∂μ)≤4 := by
  have hd : ∀ᵐz ∂μ,(f z-a)^2≤4 := hb.mono (fun z hz => by
    have hh : |f z-a|≤2 := (abs_sub _ _).trans (by linarith)
    nlinarith [abs_nonneg (f z-a),sq_abs (f z-a)])
  have hi : Integrable (fun z => (f z-a)^2) μ := by simpa only [Pi.sub_apply] using (hf.sub (memLp_const a)).integrable_sq
  simpa only [integral_const,probReal_univ,one_smul] using integral_mono_ae hi (integrable_const (4:ℝ)) hd

@[expose] def lateOverlapError (β : ℝ) (T L : ℝ≥0) (c : ℝ→ℝ) (b : Fin K) (v : ℝ) : ℝ :=
  (∫z : ForkSpace N p K,(pairOverlap β T L v.toNNReal b b z-c ((L:ℝ)-v))^2 ∂forkLaw N p K)+
    ∫z : ForkSpace N p K,(meanOverlap β T L v.toNNReal b z-mixedOverlap c K L ((L:ℝ)-v))^2 ∂forkLaw N p K

lemma lateOverlapError_bounds (hN : 0<N) (hK : 0<K) (β : ℝ) (T L : ℝ≥0)
    {c r : ℝ→ℝ} {q : ℝ} (H : ProfileCenterEnergy.Profile c r q)
    (b : Fin K) {v : ℝ} (hv : v∈Icc (0:ℝ) L) :
    0≤lateOverlapError (N:=N) (p:=p) β T L c b v ∧ lateOverlapError (N:=N) (p:=p) β T L c b v≤8 := by
  have ha := H.bounds ((L:ℝ)-v) (by linarith [hv.2])
  have hτ : ((L:ℝ)-v)∈Icc (0:ℝ) L := ⟨by linarith [hv.2],by linarith [hv.1]⟩
  have hm := mixed_overlap_bounds H (by omega : 1≤K) L.coe_nonneg hτ
  have hd := centered_square_bound (pairOverlap_memLp (p:=p) hN β T L v.toNNReal b b)
    (pairOverlap_abs_le_one hN β T L v.toNNReal b b) (by rw [abs_of_nonneg ha.1];exact ha.2)
  have hb := centered_square_bound (meanOverlap_memLp (p:=p) hN β T L v.toNNReal b)
    (meanOverlap_abs_le_one hN hK β T L v.toNNReal b) (by rw [abs_of_nonneg hm.1];exact hm.2.1)
  exact ⟨add_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (integral_nonneg (fun _ => sq_nonneg _)),by dsimp only [lateOverlapError];linarith⟩

/-- Exact printed source10.4 Step4: the complete closed-window
supremum, dimension limsup first, then stationary-cluster time. -/
theorem actual_late_overlap_concentration {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,2≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hK : 0<K) (L : ℝ≥0) (b : Fin K) :
    Tendsto (fun n => limsup (fun j => sSup
      ((lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b) ''Icc (0:ℝ) L)) atTop)
      atTop (𝓝 0) := by
  have hh : Tendsto (fun n => limsup (fun j => ForkOverlapSupLimit.windowSup
      (fun n j (z : ℝ×ℝ) => lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b z.1)
        L n j) atTop) atTop (𝓝 0) := by
    apply ForkOverlapSupLimit.ordered_uniform_limsup (M:=8) L.coe_nonneg
    · intro n j z hz
      exact (lateOverlapError_bounds (by have hx:=hDim j;omega) hK β (T n).toNNReal L H.profile b hz.1).1
    · intro n j z hz
      exact (lateOverlapError_bounds (by have hx:=hDim j;omega) hK β (T n).toNNReal L H.profile b hz.1).2
    · intro ε hε
      have hu := actual_late_overlap_ordered_uniform H hT dim hDim hTop E hLaw hbridge hi hn hL1 hK L hε
      filter_upwards [hu] with n hnu
      filter_upwards [hnu] with j hju
      intro z hz
      exact hju z.1 hz.1 b
  have he (n j : ℕ) : ForkOverlapSupLimit.windowSup
      (fun n j (z : ℝ×ℝ) => lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b z.1) L n j=
      sSup ((lateOverlapError (N:=dim j) (p:=p) β (T n).toNNReal L c b) ''Icc (0:ℝ) L) := by
    unfold ForkOverlapSupLimit.windowSup ForkOverlapSupLimit.window
    apply congrArg sSup
    ext a
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨z.1,hz.1,rfl⟩
    · rintro ⟨v,hv,rfl⟩
      exact ⟨(v,0),⟨hv,⟨le_rfl,L.coe_nonneg⟩⟩,rfl⟩
  simpa only [he] using hh

end SphericalAging.PhysicalForkLateOverlapLimit
