module

public import SphericalAging.DirichletKernel
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.MeasureTheory.Measure.Continuity

public section

/-! Uniform compact-increment decay from the actual logarithmic Dirichlet energy. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal
namespace SphericalAging.DirichletIncrement

@[expose] def energyDensity (a : ℝ) (D : ℝ → ℝ) (q : ℝ×ℝ) : ℝ :=
  (D q.1-D q.2)^2/(2*Real.cosh ((q.1-q.2)/2))^(2-2*a)

@[expose] def energyMeasure (a : ℝ) (D : ℝ → ℝ) : Measure (ℝ×ℝ) :=
  (volume.prod volume).withDensity (fun q => ENNReal.ofReal (energyDensity a D q))

theorem energyDensity_measurable {D : ℝ → ℝ} (hD : Measurable D) (a : ℝ) :
    Measurable (energyDensity a D) := by
  unfold energyDensity
  fun_prop

theorem finite_energyMeasure {a : ℝ} {D : ℝ → ℝ} (hD : Measurable D)
    (hfinite : (∫⁻ q : ℝ×ℝ, ENNReal.ofReal (energyDensity a D q)
      ∂(volume.prod volume))<∞) : IsFiniteMeasure (energyMeasure a D) := by
  constructor
  rw [energyMeasure,withDensity_apply _ MeasurableSet.univ]
  simpa only [Measure.restrict_univ] using hfinite

theorem finite_measure_second_tail {μ : Measure (ℝ×ℝ)} [IsFiniteMeasure μ]
    {ε : ℝ≥0∞} (hε : 0<ε) : ∃ n : ℕ, μ {q : ℝ×ℝ | (n:ℝ)≤q.2}<ε := by
  let S : ℕ → Set (ℝ×ℝ) := fun n => {q | (n:ℝ)≤q.2}
  have hm : Antitone S := by
    intro n m hnm q hq
    have hqm : (m:ℝ)≤q.2 := hq
    exact le_trans (show (n:ℝ)≤(m:ℝ) by exact_mod_cast hnm) hqm
  have he : (⋂ n,S n)=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro q hq
    obtain ⟨n,hn⟩ := exists_nat_gt q.2
    have hh := mem_iInter.mp hq n
    exact not_le.mpr hn hh
  have hlim := tendsto_measure_iInter_atTop (μ := μ)
    (fun n => (show MeasurableSet (S n) from
      measurableSet_le measurable_const measurable_snd).nullMeasurableSet) hm
    ⟨0,measure_ne_top _ _⟩
  rw [he,measure_empty] at hlim
  exact (hlim.eventually (Iio_mem_nhds hε)).exists

theorem energyDensity_box_lower {a : ℝ} (ha : a<1) {D : ℝ → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D) {R ε δ x h : ℝ} (hR : 0≤R) (hε : 0<ε)
    (hδ : 0<δ) (hδ1 : δ≤1) (hsmall : 2*(L:ℝ)*δ≤ε/2)
    (hh : |h|≤R) (hbad : ε≤|D (x+h)-D x|) (q : ℝ×ℝ)
    (hq : q∈Icc (x+h-δ) (x+h+δ) ×ˢ Icc (x-δ) (x+δ)) :
    (ε/2)^2/(2*Real.cosh ((R+2)/2))^(2-2*a)≤energyDensity a D q := by
  have hu : |q.1-(x+h)|≤δ := abs_le.mpr ⟨by linarith [hq.1.1],by linarith [hq.1.2]⟩
  have hv : |q.2-x|≤δ := abs_le.mpr ⟨by linarith [hq.2.1],by linarith [hq.2.2]⟩
  have hdu : |D (x+h)-D q.1|≤(L:ℝ)*δ := by
    have hl := hD.dist_le_mul (x+h) q.1
    rw [Real.dist_eq,Real.dist_eq,abs_sub_comm (x+h) q.1] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hu L.coe_nonneg)
  have hdv : |D q.2-D x|≤(L:ℝ)*δ := by
    have hl := hD.dist_le_mul q.2 x
    rw [Real.dist_eq,Real.dist_eq] at hl
    exact hl.trans (mul_le_mul_of_nonneg_left hv L.coe_nonneg)
  have htri := abs_sub_le (D (x+h)) (D q.1) (D x)
  have htri' := abs_sub_le (D q.1) (D q.2) (D x)
  have hd : ε/2≤|D q.1-D q.2| := by linarith
  have hsq : (ε/2)^2≤(D q.1-D q.2)^2 := by
    nlinarith [sq_abs (D q.1-D q.2)]
  have hp := abs_sub_le q.1 (x+h) q.2
  have hp' := abs_sub_le (x+h) x q.2
  have hv' : |x-q.2|≤δ := by simpa only [abs_sub_comm] using hv
  have hh' : |(x+h)-x|≤R := by simpa using hh
  have hdist : |q.1-q.2|≤R+2 := by linarith
  have hcosh : Real.cosh ((q.1-q.2)/2)≤Real.cosh ((R+2)/2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div,abs_of_pos (by norm_num : (0:ℝ)<2),abs_of_nonneg (by linarith : 0≤(R+2)/2)]
    exact div_le_div_of_nonneg_right hdist (by norm_num)
  have hpow : (2*Real.cosh ((q.1-q.2)/2))^(2-2*a)≤
      (2*Real.cosh ((R+2)/2))^(2-2*a) := by
    apply Real.rpow_le_rpow
    · positivity
    · linarith
    · linarith
  have hden : 0<(2*Real.cosh ((q.1-q.2)/2))^(2-2*a) := by positivity
  have hden' : 0<(2*Real.cosh ((R+2)/2))^(2-2*a) := by positivity
  unfold energyDensity
  exact (div_le_div_of_nonneg_right hsq hden'.le).trans
    (div_le_div_of_nonneg_left (sq_nonneg _) hden hpow)

theorem energyMeasure_box_lower {a : ℝ} {D : ℝ → ℝ} {c δ x h : ℝ}
    (hbound : ∀ q∈Icc (x+h-δ) (x+h+δ) ×ˢ Icc (x-δ) (x+δ),c≤energyDensity a D q) :
    ENNReal.ofReal c*ENNReal.ofReal (2*δ)*ENNReal.ofReal (2*δ)≤
      energyMeasure a D (Icc (x+h-δ) (x+h+δ) ×ˢ Icc (x-δ) (x+δ)) := by
  let B := Icc (x+h-δ) (x+h+δ) ×ˢ Icc (x-δ) (x+δ)
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hmass : (volume.prod volume) B=ENNReal.ofReal (2*δ)*ENNReal.ofReal (2*δ) := by
    dsimp [B]
    rw [Measure.prod_prod,Real.volume_Icc,Real.volume_Icc]
    congr 2 <;> ring
  change ENNReal.ofReal c*ENNReal.ofReal (2*δ)*ENNReal.ofReal (2*δ)≤energyMeasure a D B
  rw [energyMeasure,withDensity_apply _ hB]
  calc
    _ = ENNReal.ofReal c*(volume.prod volume) B := by rw [hmass]; ring
    _ = ∫⁻ q in B,ENNReal.ofReal c ∂(volume.prod volume) := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hB] with q hq
      exact ENNReal.ofReal_le_ofReal (hbound q hq)

/-- Finite actual logarithmic Dirichlet energy forbids any fixed-sized
increment arbitrarily far along the ray. The conclusion is uniform in h. -/
theorem compact_increment_decay {a : ℝ} (ha : a<1) {D : ℝ → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D)
    (hfinite : (∫⁻ q : ℝ×ℝ, ENNReal.ofReal (energyDensity a D q)
      ∂(volume.prod volume))<∞) :
    ∀ R : ℝ,0≤R → ∀ ε : ℝ,0<ε → ∃ T : ℝ,∀ x≥T,∀ h : ℝ,
      |h|≤R → |D (x+h)-D x|<ε := by
  intro R hR ε hε
  let δ := min 1 (ε/(4*((L:ℝ)+1)))
  have hL : 0≤(L:ℝ) := L.coe_nonneg
  have hδ : 0<δ := lt_min (by norm_num) (div_pos hε (by positivity))
  have hδ1 : δ≤1 := min_le_left _ _
  have hδsmall : 2*(L:ℝ)*δ≤ε/2 := by
    have hh := (le_div_iff₀ (by positivity : 0<4*((L:ℝ)+1))).mp (min_le_right 1 (ε/(4*((L:ℝ)+1))))
    change δ*(4*((L:ℝ)+1))≤ε at hh
    nlinarith
  let c := (ε/2)^2/(2*Real.cosh ((R+2)/2))^(2-2*a)
  have hc : 0<c := by dsimp [c]; positivity
  let μ := energyMeasure a D
  letI : IsFiniteMeasure μ := finite_energyMeasure hD.continuous.measurable hfinite
  have hm : 0<ENNReal.ofReal c*ENNReal.ofReal (2*δ)*ENNReal.ofReal (2*δ) := by positivity
  obtain ⟨n,hn⟩ := finite_measure_second_tail (μ := μ) hm
  refine ⟨(n:ℝ)+δ,?_⟩
  intro x hx h hh
  by_contra hbad
  have hbad' : ε≤|D (x+h)-D x| := le_of_not_gt hbad
  have hbox := energyMeasure_box_lower (fun q hq =>
    energyDensity_box_lower ha hD hR hε hδ hδ1 hδsmall hh hbad' q hq)
  have hsub : Icc (x+h-δ) (x+h+δ) ×ˢ Icc (x-δ) (x+δ) ⊆
      {q : ℝ×ℝ | (n:ℝ)≤q.2} := by
    intro q hq
    change (n:ℝ)≤q.2
    exact (show (n:ℝ)≤x-δ by linarith).trans hq.2.1
  have hmono := measure_mono (μ := μ) hsub
  exact not_le.mpr hn (hbox.trans hmono)

theorem fixed_increment_tendsto_zero {a : ℝ} (ha : a<1) {D : ℝ → ℝ} {L : ℝ≥0}
    (hD : LipschitzWith L D)
    (hfinite : (∫⁻ q : ℝ×ℝ, ENNReal.ofReal (energyDensity a D q)
      ∂(volume.prod volume))<∞) (h : ℝ) :
    Tendsto (fun x : ℝ => D (x+h)-D x) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨T,hT⟩ := compact_increment_decay ha hD hfinite |h| (abs_nonneg _) ε hε
  filter_upwards [eventually_ge_atTop T] with x hx
  simpa only [Real.dist_eq,sub_zero] using hT x hx h le_rfl

end SphericalAging.DirichletIncrement
