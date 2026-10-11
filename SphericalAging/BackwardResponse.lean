module

public import SphericalAging.GreenCovarianceClosure

public section

/-! Actual backward response and correlation comparison from the CK equations.
The reverse resolvent representation is derived by row uniqueness, avoiding
any assumed backward derivative or response representation. -/
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace SphericalAging.BackwardResponse
open CKSpecification GreenCovariance GreenCovarianceClosure

theorem fixed_integral_hasDerivAt_of_lipschitz_from
    {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {a t : ℝ} {U : Set ℝ} {M : ℝ≥0}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous D) (ht : a ≤ t)
    (hU : U ∈ 𝓝 t)
    (hLip : ∀ u ∈ Icc a t, LipschitzOnWith M (fun x => F x u) U)
    (hDiff : ∀ u ∈ Ico a t, HasDerivAt (fun x => F x u) (D u) t) :
    HasDerivAt (fun x => ∫ u in a..t, F x u) (∫ u in a..t, D u) t := by
  have hrow (x : ℝ) : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hder := hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := volume.restrict (Ioc a t)) (F := F) (F' := D) (bound := fun _ => (M : ℝ)) hU
    (Filter.Eventually.of_forall fun x => (hrow x).aestronglyMeasurable)
    ((hrow t).integrableOn_Icc.mono_set Ioc_subset_Icc_self) hD.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Ioc).mpr (ae_of_all _ (fun u hu => by
      simpa using hLip u (Ioc_subset_Icc_self hu))))
    (integrable_const (M : ℝ)) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc,
        ae_restrict_of_ae (show ∀ᵐ u ∂volume, u ≠ t from by simp [ae_iff])] with u hu hne
      exact hDiff u ⟨hu.1.le, lt_of_le_of_ne hu.2 hne⟩)
  simpa only [intervalIntegral.integral_of_le ht] using hder.2

/-- Moving-upper-limit Leibniz rule with pointwise causal derivative and
uniform local Lipschitz hypotheses, proved using the two preceding lemmas. -/
theorem moving_integral_hasDerivAt_of_lipschitz_from
    {F : ℝ → ℝ → ℝ} {D : ℝ → ℝ} {a t : ℝ} {U : Set ℝ} {M : ℝ≥0}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous D) (ht : a ≤ t)
    (hU : U ∈ 𝓝 t)
    (hLip : ∀ u ∈ Icc a t, LipschitzOnWith M (fun x => F x u) U)
    (hDiff : ∀ u ∈ Ico a t, HasDerivAt (fun x => F x u) (D u) t) :
    HasDerivAt (fun x => ∫ u in a..x, F x u)
      ((∫ u in a..t, D u) + F t t) t := by
  have ha := fixed_integral_hasDerivAt_of_lipschitz_from hF hD ht hU hLip hDiff
  have hb := moving_boundary_hasDerivAt hF t
  apply (ha.add hb).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro x
  exact (intervalIntegral.integral_add_adjacent_intervals
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable a t)
    ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable t x)).symm


theorem weighted_response_from_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {A : ℝ → ℝ} (hA : Continuous A) {a t : ℝ} (ha : 0 ≤ a) (ht : a ≤ t) :
    HasDerivWithinAt (fun x => ∫ u in a..x, d.R x u * A u)
      ((∫ u in a..t, responseSlope p β d t u * A u) + A t) (Ici a) t := by
  let r : ℝ := t+1
  let F : ℝ → ℝ → ℝ := fun x u => clampedResponse d x u * A u
  let G : ℝ → ℝ → ℝ := fun x u => clampedResponseSlope p β d x u * A u
  have hR := clampedResponse_continuous h
  have hD := clampedResponseSlope_continuous h
  have hF : Continuous (Function.uncurry F) := hR.mul (hA.comp continuous_snd)
  have hG : Continuous (Function.uncurry G) := hD.mul (hA.comp continuous_snd)
  obtain ⟨M₀,hM₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) r ×ˢ Icc (0 : ℝ) r) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hG.norm.continuousOn
  let M : ℝ≥0 := ⟨max 0 M₀, le_max_left _ _⟩
  have hLip (u : ℝ) (hu : u ∈ Icc a t) :
      LipschitzOnWith M (fun x => F x u) (Iic r) := by
    have hl := causal_clamp_lipschitzOn (f := fun x => d.R x u * A u)
      (f' := fun x => responseSlope p β d x u * A u)
      (M := M) (a := u) (r := r) (hu.2.trans (by dsimp [r]; linarith))
      (fun x hx => (h.response_derivative x u (ha.trans hu.1) hx.1).mul_const _)
      (fun x hx => by
        have hx0 := (ha.trans hu.1).trans hx.1
        have hur : u ≤ r := hu.2.trans (by dsimp [r]; linarith)
        have hb := hM₀ ⟨(x,u), ⟨⟨hx0,hx.2⟩,⟨ha.trans hu.1,hur⟩⟩,rfl⟩
        have he : G x u = responseSlope p β d x u * A u := by
          dsimp [G]
          rw [clampedResponseSlope_eq (ha.trans hu.1) hx.1]
        change ‖responseSlope p β d x u * A u‖ ≤ max 0 M₀
        rw [← he]
        exact hb.trans (le_max_right _ _))
    simpa only [F,clampedResponse,max_eq_right (ha.trans hu.1)] using hl
  have hDiff (u : ℝ) (hu : u ∈ Ico a t) :
      HasDerivAt (fun x => F x u) (G t u) t :=
    (clampedResponse_hasDerivAt h (ha.trans hu.1) hu.2).mul_const _
  have hd := moving_integral_hasDerivAt_of_lipschitz_from (D := fun u => G t u) hF
    (hG.comp (continuous_const.prodMk continuous_id)) ht
    (show Iic r ∈ 𝓝 t from Iic_mem_nhds (by dsimp [r]; linarith)) hLip hDiff
  have hi : (∫ u in a..t, G t u) =
      ∫ u in a..t, responseSlope p β d t u * A u := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le ht] at hu
    dsimp [G]
    rw [clampedResponseSlope_eq (ha.trans hu.1) hu.2]
  have hdiag : F t t = A t := by
    dsimp [F]
    rw [clampedResponse_eq (ha.trans ht) (le_refl _), h.response_diagonal t (ha.trans ht),one_mul]
  rw [hi,hdiag] at hd
  apply hd.hasDerivWithinAt.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp [F]
    rw [clampedResponse_eq (ha.trans hu.1) hu.2]
  · exact ht


/-- The true triangular Fubini identity with an arbitrary initial time. -/
theorem weighted_memory_from {R K : ℝ → ℝ → ℝ} {A : ℝ → ℝ}
    (hR : Continuous (Function.uncurry R)) (hK : Continuous (Function.uncurry K))
    (hA : Continuous A) {a t : ℝ} (hat : a ≤ t) :
    (∫ u in a..t, A u * (∫ z in u..t, K t z * R z u)) =
      ∫ z in a..t, K t z * (∫ u in a..z, R z u * A u) := by
  let R' : ℝ → ℝ → ℝ := fun x u => R (x+a) (u+a)
  let K' : ℝ → ℝ → ℝ := fun x u => K (x+a) (u+a)
  let A' : ℝ → ℝ := fun u => A (u+a)
  have hR' : Continuous (Function.uncurry R') :=
    hR.comp ((continuous_fst.add continuous_const).prodMk
      (continuous_snd.add continuous_const))
  have hK' : Continuous (Function.uncurry K') :=
    hK.comp ((continuous_fst.add continuous_const).prodMk
      (continuous_snd.add continuous_const))
  have hA' : Continuous A' := hA.comp (continuous_id.add continuous_const)
  have hh := TriangleUniqueness.weighted_triangle_memory_diagonal hR' hK' hA'
    (sub_nonneg.mpr hat)
  have hl : (∫ u in (0 : ℝ)..t-a, A' u *
      (∫ z in u..t-a, K' (t-a) z * R' z u)) =
      ∫ u in a..t, A u * (∫ z in u..t, K t z * R z u) := by
    dsimp [A',K',R']
    have hi (u : ℝ) :
        (∫ z in u..t-a, K (t-a+a) (z+a) * R (z+a) (u+a)) =
          ∫ z in u+a..t, K t z * R z (u+a) := by
      simpa only [sub_add_cancel] using
        (intervalIntegral.integral_comp_add_right
          (fun z => K t z * R z (u+a)) a (a := u) (b := t-a))
    simp_rw [hi]
    simpa only [zero_add,sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right
        (fun u => A u * (∫ z in u..t, K t z * R z u)) a
        (a := 0) (b := t-a))
  have hr : (∫ z in (0 : ℝ)..t-a, K' (t-a) z *
      (∫ u in (0 : ℝ)..z, R' z u * A' u)) =
      ∫ z in a..t, K t z * (∫ u in a..z, R z u * A u) := by
    dsimp [A',K',R']
    have hi (z : ℝ) :
        (∫ u in (0 : ℝ)..z, R (z+a) (u+a) * A (u+a)) =
          ∫ u in a..z+a, R (z+a) u * A u := by
      simpa only [zero_add] using
        (intervalIntegral.integral_comp_add_right
          (fun u => R (z+a) u * A u) a (a := 0) (b := z))
    simp_rw [hi]
    simpa only [zero_add,sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right
        (fun z => K t z * (∫ u in a..z, R z u * A u)) a
        (a := 0) (b := t-a))
  rwa [hl,hr] at hh

/-- Actual inhomogeneous Volterra propagation, after reordering its memory. -/
theorem weighted_response_from_linear_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {A : ℝ → ℝ} (hA : Continuous A)
    {a t : ℝ} (ha : 0 ≤ a) (hat : a ≤ t) :
    HasDerivWithinAt (fun x => ∫ u in a..x, clampedResponse d x u * A u)
      (-d.multiplier t * (∫ u in a..t, clampedResponse d t u * A u) +
        (∫ z in a..t, clampedMemory p β d t z *
          (∫ u in a..z, clampedResponse d z u * A u)) + A t) (Ici a) t := by
  have hd := weighted_response_from_hasDerivWithinAt h hA ha hat
  have hR := clampedResponse_continuous h
  have hK := clampedMemory_continuous h
  have hI : (∫ u in a..t, responseSlope p β d t u * A u) =
      -d.multiplier t * (∫ u in a..t, clampedResponse d t u * A u) +
        ∫ z in a..t, clampedMemory p β d t z *
          (∫ u in a..z, clampedResponse d z u * A u) := by
    have hmem : Continuous (fun u => ∫ z in u..t,
        clampedMemory p β d t z * clampedResponse d z u) := by
      have hc : Continuous (fun u => ∫ z in t..u,
          clampedMemory p β d t z * clampedResponse d z u) :=
        intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          ((hK.comp (continuous_const.prodMk continuous_snd)).mul
            (hR.comp (continuous_snd.prodMk continuous_fst))) continuous_id
      convert hc.neg using 1
      funext u
      exact intervalIntegral.integral_symm (f := fun z =>
        clampedMemory p β d t z * clampedResponse d z u) t u
    calc
      (∫ u in a..t, responseSlope p β d t u * A u) =
          ∫ u in a..t, (-d.multiplier t * clampedResponse d t u +
            ∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) * A u := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le hat] at hu
        dsimp
        rw [responseSlope_linear_memory (ha.trans hu.1) hu.2]
      _ = -d.multiplier t * (∫ u in a..t, clampedResponse d t u * A u) +
          ∫ u in a..t, A u * (∫ z in u..t,
            clampedMemory p β d t z * clampedResponse d z u) := by
        have he : (fun u => (-d.multiplier t * clampedResponse d t u +
            ∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u) * A u) =
            (fun u => -d.multiplier t * (clampedResponse d t u * A u) +
              A u * (∫ z in u..t, clampedMemory p β d t z * clampedResponse d z u)) := by
          funext u; ring
        rw [he,intervalIntegral.integral_add
          (f := fun u => -d.multiplier t * (clampedResponse d t u * A u))
          (g := fun u => A u * (∫ z in u..t,
            clampedMemory p β d t z * clampedResponse d z u))
          ((((hR.comp (continuous_const.prodMk continuous_id)).mul hA).const_mul
            (-d.multiplier t)).intervalIntegrable a t)
          ((hA.mul hmem).intervalIntegrable a t),intervalIntegral.integral_const_mul]
      _ = _ := by rw [weighted_memory_from hR hK hA hat]
  rw [hI] at hd
  apply hd.congr_of_mem
  · intro x hx
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hx] at hu
    dsimp
    rw [clampedResponse_eq (ha.trans hu.1) hu.2]
  · exact hat


/-- Compact-horizon row uniqueness with the actual CK memory kernel. -/
theorem ck_homogeneous_row_zero {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {f f' : ℝ → ℝ} {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (hf : Continuous f) (hzero : f a = 0)
    (hd : ∀ x, a ≤ x → HasDerivWithinAt f (f' x) (Ici a) x)
    (heq : ∀ x, a ≤ x → f' x = -d.multiplier x * f x +
      ∫ u in a..x, clampedMemory p β d x u * f u) : f t = 0 := by
  obtain ⟨L₀,hL₀⟩ := isCompact_Icc.bddAbove_image
    ((h.multiplier_continuous.mono (show Icc 0 t ⊆ Ici 0 from fun _ hx => hx.1)).norm)
  have hK := clampedMemory_continuous h
  obtain ⟨S₀,hS₀⟩ :=
    (show IsCompact (Icc (0 : ℝ) t ×ˢ Icc (0 : ℝ) t) from
      isCompact_Icc.prod isCompact_Icc).bddAbove_image hK.norm.continuousOn
  have hz := VolterraUniqueness.homogeneous_row_eq_zero f f' d.multiplier
    (clampedMemory p β d) a t (max 0 L₀) (max 0 S₀) hat
    (le_max_left _ _) (le_max_left _ _) hf hzero
    (fun x hx => (hd x hx.1).mono (fun _ hu => hx.1.trans hu))
    (fun x hx => heq x hx.1)
    (fun x hx => by
      have hl := hL₀ ⟨x,⟨ha.trans hx.1,hx.2.le⟩,rfl⟩
      exact (show |d.multiplier x| ≤ L₀ by simpa only [Real.norm_eq_abs] using hl).trans
        (le_max_right _ _))
    (fun x _ => (((hK.comp (continuous_const.prodMk continuous_id)).mul hf).intervalIntegrable a x))
    (fun x hx u hu => by
      have hb := hS₀ ⟨(x,u),⟨⟨ha.trans hx.1,hx.2.le⟩,
        ⟨ha.trans hu.1,hu.2.trans hx.2.le⟩⟩,rfl⟩
      exact (show |clampedMemory p β d x u| ≤ S₀ by
        simpa only [Function.uncurry_apply_pair,Real.norm_eq_abs] using hb).trans (le_max_right _ _))
  exact hz t ⟨hat,le_refl t⟩

@[expose] def clampedMultiplier (d : CKData) (t : ℝ) : ℝ := d.multiplier (max 0 t)

theorem clampedMultiplier_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (clampedMultiplier d) :=
  h.multiplier_continuous.comp_continuous (continuous_const.max continuous_id)
    (fun x => by change 0 ≤ max 0 x; exact le_max_left _ _)

@[expose] def freeResponse (d : CKData) (t s : ℝ) : ℝ :=
  Real.exp (-(∫ u in (0 : ℝ)..t, clampedMultiplier d u) +
    ∫ u in (0 : ℝ)..s, clampedMultiplier d u)

theorem multiplier_primitive_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t : ℝ) :
    HasDerivAt (fun x => ∫ u in (0 : ℝ)..x, clampedMultiplier d u)
      (clampedMultiplier d t) t := by
  have hc := clampedMultiplier_continuous h
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem freeResponse_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (freeResponse d)) := by
  have hc : Continuous (fun x => ∫ u in (0 : ℝ)..x, clampedMultiplier d u) :=
    continuous_iff_continuousAt.mpr (fun x => (multiplier_primitive_derivative h x).continuousAt)
  exact Real.continuous_exp.comp ((hc.comp continuous_fst).neg.add (hc.comp continuous_snd))

theorem freeResponse_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    HasDerivAt (fun x => freeResponse d x s)
      (-clampedMultiplier d t * freeResponse d t s) t := by
  convert ((multiplier_primitive_derivative h t).neg.add_const
    (∫ u in (0 : ℝ)..s, clampedMultiplier d u)).exp using 1 <;> first | rfl | (simp only [freeResponse,Pi.neg_apply]; ring)

theorem freeResponse_backward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    HasDerivAt (fun x => freeResponse d t x)
      (clampedMultiplier d s * freeResponse d t s) s := by
  convert ((multiplier_primitive_derivative h s).const_add
    (-(∫ u in (0 : ℝ)..t, clampedMultiplier d u))).exp using 1 <;> first | rfl | (simp only [freeResponse]; ring)

theorem freeResponse_diagonal (d : CKData) (s : ℝ) : freeResponse d s s = 1 := by
  simp [freeResponse]

@[expose] def reversedForcing (p : ℕ) (β : ℝ) (d : CKData) (s u : ℝ) : ℝ :=
  ∫ v in s..u, clampedMemory p β d u v * freeResponse d v s

@[expose] def reversedCandidate (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  freeResponse d t s +
    ∫ u in s..t, clampedResponse d t u * reversedForcing p β d s u

theorem reversedForcing_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) : Continuous (reversedForcing p β d s) := by
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
    ((clampedMemory_continuous h).mul
      ((freeResponse_continuous h).comp (continuous_snd.prodMk continuous_const))) continuous_id

theorem reversedCandidate_row_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) : Continuous (fun t => reversedCandidate p β d t s) := by
  apply Continuous.add
  · exact (freeResponse_continuous h).comp (continuous_id.prodMk continuous_const)
  · exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((clampedResponse_continuous h).mul ((reversedForcing_continuous h s).comp continuous_snd))
      continuous_id

theorem reversedCandidate_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasDerivWithinAt (fun x => reversedCandidate p β d x s)
      (-d.multiplier t * reversedCandidate p β d t s +
        ∫ u in s..t, clampedMemory p β d t u * reversedCandidate p β d u s) (Ici s) t := by
  have hd := (freeResponse_forward_derivative h t s).hasDerivWithinAt.add
    (weighted_response_from_linear_derivative h (reversedForcing_continuous h s) hs hst)
  have hI : (∫ u in s..t, clampedMemory p β d t u * reversedCandidate p β d u s) =
      reversedForcing p β d s t +
        ∫ u in s..t, clampedMemory p β d t u *
          (∫ v in s..u, clampedResponse d u v * reversedForcing p β d s v) := by
    have hKrow : Continuous (fun u => clampedMemory p β d t u) :=
      (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
    have hG : Continuous (fun u => freeResponse d u s) :=
      (freeResponse_continuous h).comp (continuous_id.prodMk continuous_const)
    have hY : Continuous (fun u => ∫ v in s..u,
        clampedResponse d u v * reversedForcing p β d s v) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
        ((clampedResponse_continuous h).mul ((reversedForcing_continuous h s).comp continuous_snd))
        continuous_id
    dsimp [reversedCandidate,reversedForcing]
    simp only [mul_add]
    exact intervalIntegral.integral_add (f := fun u => clampedMemory p β d t u * freeResponse d u s)
      (g := fun u => clampedMemory p β d t u * ∫ v in s..u,
        clampedResponse d u v * reversedForcing p β d s v)
      ((hKrow.mul hG).intervalIntegrable s t) ((hKrow.mul hY).intervalIntegrable s t)
  convert hd using 1
  · rfl
  · rw [hI]
    dsimp [reversedCandidate,clampedMultiplier]
    rw [max_eq_right (hs.trans hst)]
    ring


theorem clampedResponse_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasDerivWithinAt (fun x => clampedResponse d x s)
      (-d.multiplier t * clampedResponse d t s +
        ∫ u in s..t, clampedMemory p β d t u * clampedResponse d u s) (Ici s) t := by
  have hd := h.response_derivative t s hs hst
  rw [responseSlope_linear_memory hs hst] at hd
  apply hd.congr_of_mem
  · intro x hx
    exact clampedResponse_eq hs hx
  · exact hst

/-- Two actual inhomogeneous CK rows with the same forcing and initial value
coincide; the theorem derives its zero difference from the equations. -/
theorem ck_inhomogeneous_rows_eq {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {F G A : ℝ → ℝ} {a t : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (hF : Continuous F) (hG : Continuous G)
    (hzero : F a = G a)
    (hFd : ∀ x, a ≤ x → HasDerivWithinAt F
      (-d.multiplier x * F x + (∫ u in a..x, clampedMemory p β d x u * F u) + A x) (Ici a) x)
    (hGd : ∀ x, a ≤ x → HasDerivWithinAt G
      (-d.multiplier x * G x + (∫ u in a..x, clampedMemory p β d x u * G u) + A x) (Ici a) x) :
    F t = G t := by
  let f : ℝ → ℝ := fun x => F x-G x
  let f' : ℝ → ℝ := fun x => -d.multiplier x * f x +
    ∫ u in a..x, clampedMemory p β d x u * f u
  have hder (x : ℝ) (hx : a ≤ x) : HasDerivWithinAt f (f' x) (Ici a) x := by
    have hk : Continuous (fun u => clampedMemory p β d x u) :=
      (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
    have hi : (∫ u in a..x, clampedMemory p β d x u * f u) =
        (∫ u in a..x, clampedMemory p β d x u * F u) -
          (∫ u in a..x, clampedMemory p β d x u * G u) := by
      simp only [f,mul_sub]
      exact intervalIntegral.integral_sub (f := fun u => clampedMemory p β d x u * F u)
        (g := fun u => clampedMemory p β d x u * G u)
        ((hk.mul hF).intervalIntegrable a x) ((hk.mul hG).intervalIntegrable a x)
    convert (hFd x hx).sub (hGd x hx) using 1
    dsimp [f']
    rw [hi]
    dsimp [f]
    ring
  have hz := ck_homogeneous_row_zero h ha hat (hF.sub hG)
    (show f a = 0 from sub_eq_zero.mpr hzero) hder (fun _ _ => rfl)
  exact sub_eq_zero.mp hz

/-- The reverse resolvent formula follows from the forward CK equation.
No backward derivative, response representation, or reversed-word identity
is a hypothesis. -/
theorem reversed_response_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    clampedResponse d t s = reversedCandidate p β d t s := by
  apply ck_inhomogeneous_rows_eq h (F := fun x => clampedResponse d x s)
    (G := fun x => reversedCandidate p β d x s) hs hst
    ((clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const))
    (reversedCandidate_row_continuous h s)
    (A := fun _ => 0)
  · simp [reversedCandidate,freeResponse_diagonal,clampedResponse_eq hs (le_refl s),
      h.response_diagonal s hs]
  · intro x hx
    simpa only [add_zero] using clampedResponse_forward_derivative h hs hx
  · intro x hx
    simpa only [add_zero] using reversedCandidate_forward_derivative h hs hx


/-- Fixed-domain Leibniz rule for a continuous derivative, with either
orientation of the integration interval. -/
theorem fixed_integral_derivative_all {F D : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ x u, HasDerivAt (fun z => F z u) (D x u) x) (a b x : ℝ) :
    HasDerivAt (fun z => ∫ u in a..b, F z u) (∫ u in a..b, D x u) x := by
  by_cases hab : a ≤ b
  · exact hasDerivAt_intervalIntegral_of_continuous hF hD hab
      (show x ∈ Ioo (x-1) (x+1) by constructor <;> linarith)
      (fun y _ u _ => hd y u)
  · have hh := hasDerivAt_intervalIntegral_of_continuous hF hD (le_of_not_ge hab)
      (show x ∈ Ioo (x-1) (x+1) by constructor <;> linarith)
      (fun y _ u _ => hd y u)
    convert hh.neg using 1
    · funext z
      exact intervalIntegral.integral_symm (f := F z) b a
    · exact intervalIntegral.integral_symm (f := D x) b a

/-- Moving-lower-limit Leibniz rule from the fixed rule and the actual
small-strip derivative. -/
theorem lower_integral_derivative_all {F D : ℝ → ℝ → ℝ}
    (hF : Continuous (Function.uncurry F)) (hD : Continuous (Function.uncurry D))
    (hd : ∀ x u, HasDerivAt (fun z => F z u) (D x u) x) (b x : ℝ) :
    HasDerivAt (fun z => ∫ u in z..b, F z u)
      ((∫ u in x..b, D x u) - F x x) x := by
  have hfixed := fixed_integral_derivative_all hF hD hd x b x
  have hstrip := moving_boundary_hasDerivAt hF x
  apply (hfixed.sub hstrip).congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro z
  have hrow : Continuous (fun u => F z u) :=
    hF.comp (continuous_const.prodMk continuous_id)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hrow.intervalIntegrable x z) (hrow.intervalIntegrable z b)
  dsimp
  linarith

/-- The lower endpoint derivative of the reversed forcing uses continuity
of the self-energy only, never a derivative of that kernel. -/
theorem reversedForcing_backward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s u : ℝ) :
    HasDerivAt (fun x => reversedForcing p β d x u)
      (clampedMultiplier d s * reversedForcing p β d s u - clampedMemory p β d u s) s := by
  let F : ℝ → ℝ → ℝ := fun x v => clampedMemory p β d u v * freeResponse d v x
  let D : ℝ → ℝ → ℝ := fun x v =>
    clampedMemory p β d u v * (clampedMultiplier d x * freeResponse d v x)
  have hK : Continuous (fun v => clampedMemory p β d u v) :=
    (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
  have hG : Continuous (fun z : ℝ × ℝ => freeResponse d z.2 z.1) :=
    (freeResponse_continuous h).comp (continuous_snd.prodMk continuous_fst)
  have hF : Continuous (Function.uncurry F) := (hK.comp continuous_snd).mul hG
  have hD : Continuous (Function.uncurry D) :=
    (hK.comp continuous_snd).mul (((clampedMultiplier_continuous h).comp continuous_fst).mul hG)
  have hh := lower_integral_derivative_all hF hD
    (fun x v => (freeResponse_backward_derivative h v x).const_mul _) u s
  convert hh using 1
  · rfl
  · dsimp [D,F]
    rw [freeResponse_diagonal]
    have hi : (∫ v in s..u, clampedMemory p β d u v *
        (clampedMultiplier d s * freeResponse d v s)) =
        clampedMultiplier d s * reversedForcing p β d s u := by
      unfold reversedForcing
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro v _
      dsimp
      ring
    rw [hi,mul_one]


/-- Joint continuity of an integral with two varying endpoints, proved
by its two fixed-origin primitives. -/
theorem continuous_integral_endpoints {X : Type*} [TopologicalSpace X]
    {F : X → ℝ → ℝ} {a b : X → ℝ}
    (hF : Continuous (Function.uncurry F)) (ha : Continuous a) (hb : Continuous b) :
    Continuous (fun x => ∫ u in a x..b x, F x u) := by
  have hA : Continuous (fun x => ∫ u in (0 : ℝ)..a x, F x u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF ha
  have hB : Continuous (fun x => ∫ u in (0 : ℝ)..b x, F x u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous hF hb
  convert hB.sub hA using 1
  funext x
  have hrow : Continuous (F x) := hF.comp (continuous_const.prodMk continuous_id)
  have hi := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hrow.intervalIntegrable 0 (a x)) (hrow.intervalIntegrable (a x) (b x))
  dsimp
  linarith

theorem reversedForcing_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (reversedForcing p β d)) := by
  apply continuous_integral_endpoints
  · exact ((clampedMemory_continuous h).comp
      (continuous_fst.snd.prodMk continuous_snd)).mul
      ((freeResponse_continuous h).comp (continuous_snd.prodMk continuous_fst.fst))
  · exact continuous_fst
  · exact continuous_snd

theorem reversedCandidate_joint_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (reversedCandidate p β d)) := by
  apply Continuous.add (freeResponse_continuous h)
  apply continuous_integral_endpoints
  · exact ((clampedResponse_continuous h).comp
      (continuous_fst.fst.prodMk continuous_snd)).mul
      ((reversedForcing_joint_continuous h).comp (continuous_fst.snd.prodMk continuous_snd))
  · exact continuous_snd
  · exact continuous_fst

@[expose] def backwardSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  d.multiplier s * d.R t s -
    ∫ u in s..t, d.R t u * (β^2 * xiDoublePrime p (d.C u s) * d.R u s)

@[expose] def clampedBackwardSlope (p : ℕ) (β : ℝ) (d : CKData) (t s : ℝ) : ℝ :=
  clampedMultiplier d s * clampedResponse d t s -
    ∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s

theorem clampedBackwardSlope_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : Continuous (Function.uncurry (clampedBackwardSlope p β d)) := by
  apply Continuous.sub
  · exact ((clampedMultiplier_continuous h).comp continuous_snd).mul
      (clampedResponse_continuous h)
  · apply continuous_integral_endpoints
    · exact ((clampedResponse_continuous h).comp
        (continuous_fst.fst.prodMk continuous_snd)).mul
        ((clampedMemory_continuous h).comp (continuous_snd.prodMk continuous_fst.snd))
    · exact continuous_snd
    · exact continuous_fst

theorem clampedBackwardSlope_eq {p : ℕ} {β : ℝ} {d : CKData} {t s : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    clampedBackwardSlope p β d t s = backwardSlope p β d t s := by
  unfold clampedBackwardSlope backwardSlope clampedMultiplier
  rw [max_eq_right hs,clampedResponse_eq hs hst]
  congr 1
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  dsimp
  rw [clampedResponse_eq (hs.trans hu.1) hu.2,clampedMemory_eq hs hu.1]

/-- The reverse resolvent candidate has an actual second-variable derivative
on the whole plane; causal coincidence with R is proved separately. -/
theorem reversedCandidate_backward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (t s : ℝ) :
    HasDerivAt (fun x => reversedCandidate p β d t x)
      (clampedMultiplier d s * reversedCandidate p β d t s -
        ∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s) s := by
  let F : ℝ → ℝ → ℝ := fun x u => clampedResponse d t u * reversedForcing p β d x u
  let D : ℝ → ℝ → ℝ := fun x u => clampedResponse d t u *
    (clampedMultiplier d x * reversedForcing p β d x u - clampedMemory p β d u x)
  have hR : Continuous (fun u => clampedResponse d t u) :=
    (clampedResponse_continuous h).comp (continuous_const.prodMk continuous_id)
  have hA := reversedForcing_joint_continuous h
  have hK : Continuous (fun z : ℝ × ℝ => clampedMemory p β d z.2 z.1) :=
    (clampedMemory_continuous h).comp (continuous_snd.prodMk continuous_fst)
  have hF : Continuous (Function.uncurry F) := (hR.comp continuous_snd).mul hA
  have hD : Continuous (Function.uncurry D) := (hR.comp continuous_snd).mul
    ((((clampedMultiplier_continuous h).comp continuous_fst).mul hA).sub hK)
  have hd := (freeResponse_backward_derivative h t s).add
    (lower_integral_derivative_all hF hD
      (fun x u => (reversedForcing_backward_derivative h x u).const_mul _) t s)
  have hboundary : F s s = 0 := by simp [F,reversedForcing]
  have hI : (∫ u in s..t, D s u) =
      clampedMultiplier d s * (∫ u in s..t,
        clampedResponse d t u * reversedForcing p β d s u) -
          ∫ u in s..t, clampedResponse d t u * clampedMemory p β d u s := by
    have hAA : Continuous (fun u => reversedForcing p β d s u) := reversedForcing_continuous h s
    have hKK : Continuous (fun u => clampedMemory p β d u s) :=
      (clampedMemory_continuous h).comp (continuous_id.prodMk continuous_const)
    have he : D s = fun u => clampedMultiplier d s *
        (clampedResponse d t u * reversedForcing p β d s u) -
          clampedResponse d t u * clampedMemory p β d u s := by
      funext u; dsimp [D]; ring
    rw [he,intervalIntegral.integral_sub
      (f := fun u => clampedMultiplier d s * (clampedResponse d t u * reversedForcing p β d s u))
      (g := fun u => clampedResponse d t u * clampedMemory p β d u s)
      (((hR.mul hAA).const_mul _).intervalIntegrable s t)
      ((hR.mul hKK).intervalIntegrable s t),intervalIntegral.integral_const_mul]
  convert hd using 1
  · rfl
  · rw [hboundary,hI]
    dsimp [reversedCandidate]
    ring


/-- Backward response equation on the causal row, including both one-sided
endpoints. This is derived from the forward CK equations. -/
theorem response_backward_hasDerivWithinAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasDerivWithinAt (fun x => d.R t x) (backwardSlope p β d t s) (Icc 0 t) s := by
  have hd := (reversedCandidate_backward_derivative h t s).hasDerivWithinAt (s := Icc 0 t)
  have he := reversed_response_identity h hs hst
  rw [← he] at hd
  change HasDerivWithinAt (fun x => reversedCandidate p β d t x)
    (clampedBackwardSlope p β d t s) (Icc 0 t) s at hd
  rw [clampedBackwardSlope_eq hs hst] at hd
  apply hd.congr_of_mem
  · intro x hx
    exact (clampedResponse_eq hx.1 hx.2).symm.trans
      (reversed_response_identity h hx.1 hx.2)
  · exact ⟨hs,hst⟩

/-- At a strictly positive earlier time the backward equation is an ordinary
two-sided derivative. At time zero the previous theorem supplies the right
endpoint interpretation. -/
theorem response_backward_hasDerivAt {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t s : ℝ} (hs : 0 < s) (hst : s < t) :
    HasDerivAt (fun x => d.R t x) (backwardSlope p β d t s) s :=
  (response_backward_hasDerivWithinAt h hs.le hst.le).hasDerivAt (Icc_mem_nhds hs hst)

/-- The backward derivative's continuous extension to the full causal
triangle follows from the actual integral formula. -/
theorem backwardSlope_continuousOn {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) : ContinuousOn (Function.uncurry (backwardSlope p β d)) causalTriangle := by
  apply (clampedBackwardSlope_continuous h).continuousOn.congr
  intro z hz
  exact (clampedBackwardSlope_eq hz.1 hz.2).symm

theorem backwardSlope_diagonal {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    backwardSlope p β d t t = d.multiplier t := by
  simp [backwardSlope,h.response_diagonal t ht]

/-- Both partial derivatives of the response extend continuously to every
closed causal triangle. The original CK hypotheses give the forward part,
and the proved reverse resolvent formula gives the backward part. -/
theorem response_partial_derivatives_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    ContinuousOn (Function.uncurry (responseSlope p β d)) causalTriangle ∧
    ContinuousOn (Function.uncurry (backwardSlope p β d)) causalTriangle :=
  ⟨h.response_slope_continuous,backwardSlope_continuousOn h⟩


/-- The nonnegative forcing from times before the initial row time. -/
@[expose] def comparisonForcing (p : ℕ) (β : ℝ) (d : CKData) (s t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..s, clampedMemory p β d t u * clampedCorrelation d u s) +
    coloredForcing p β d s t

theorem comparisonForcing_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) : Continuous (comparisonForcing p β d s) := by
  have hi : Continuous (fun t => ∫ u in (0 : ℝ)..s,
      clampedMemory p β d t u * clampedCorrelation d u s) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun t u => clampedMemory p β d t u * clampedCorrelation d u s)
      ((clampedMemory_continuous h).mul
        ((clampedCorrelation_continuous h).comp (continuous_snd.prodMk continuous_const))) 0 s
  exact hi.add (coloredForcing_continuous h s)

@[expose] def responseGap (d : CKData) (t s : ℝ) : ℝ :=
  clampedCorrelation d t s - clampedResponse d t s

theorem responseGap_row_continuous {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (s : ℝ) : Continuous (fun t => responseGap d t s) :=
  ((clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)).sub
    ((clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const))

/-- Splitting the correlation memory at the row's earlier time leaves the
homogeneous response operator and exactly the earlier-time forcing. -/
theorem responseGap_forward_derivative {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    HasDerivWithinAt (fun x => responseGap d x s)
      (-d.multiplier t * responseGap d t s +
        (∫ u in s..t, clampedMemory p β d t u * responseGap d u s) +
          comparisonForcing p β d s t) (Ici s) t := by
  have hdC := h.correlation_derivative t s hs hst
  rw [correlationSlope_linear (hs.trans hst) hs] at hdC
  have hdCC : HasDerivWithinAt (fun x => clampedCorrelation d x s)
      (-d.multiplier t * clampedCorrelation d t s +
        (∫ u in (0 : ℝ)..t, clampedMemory p β d t u * clampedCorrelation d u s) +
          coloredForcing p β d s t) (Ici s) t := by
    apply hdC.congr_of_mem
    · intro x hx
      exact clampedCorrelation_eq (hs.trans hx) hs
    · exact hst
  have hd := hdCC.sub (clampedResponse_forward_derivative h hs hst)
  have hK : Continuous (fun u => clampedMemory p β d t u) :=
    (clampedMemory_continuous h).comp (continuous_const.prodMk continuous_id)
  have hC : Continuous (fun u => clampedCorrelation d u s) :=
    (clampedCorrelation_continuous h).comp (continuous_id.prodMk continuous_const)
  have hR : Continuous (fun u => clampedResponse d u s) :=
    (clampedResponse_continuous h).comp (continuous_id.prodMk continuous_const)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    ((hK.mul hC).intervalIntegrable 0 s) ((hK.mul hC).intervalIntegrable s t)
  have hsub : (∫ u in s..t, clampedMemory p β d t u * responseGap d u s) =
      (∫ u in s..t, clampedMemory p β d t u * clampedCorrelation d u s) -
        ∫ u in s..t, clampedMemory p β d t u * clampedResponse d u s := by
    simp only [responseGap,mul_sub]
    exact intervalIntegral.integral_sub
      (f := fun u => clampedMemory p β d t u * clampedCorrelation d u s)
      (g := fun u => clampedMemory p β d t u * clampedResponse d u s)
      ((hK.mul hC).intervalIntegrable s t) ((hK.mul hR).intervalIntegrable s t)
  convert hd using 1
  · rfl
  · rw [hsub]
    dsimp [responseGap,comparisonForcing]
    dsimp only [Pi.mul_apply] at hsplit
    nlinarith only [hsplit]

/-- The entire response gap is the propagated earlier-time forcing. This is
an actual variation-of-constants identity obtained by causal row uniqueness. -/
theorem response_gap_identity {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    d.C t s - d.R t s =
      ∫ u in s..t, d.R t u * comparisonForcing p β d s u := by
  have hF := comparisonForcing_continuous h s
  have hY : Continuous (fun x => ∫ u in s..x,
      clampedResponse d x u * comparisonForcing p β d s u) :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      ((clampedResponse_continuous h).mul (hF.comp continuous_snd)) continuous_id
  have he := ck_inhomogeneous_rows_eq h
    (F := fun x => responseGap d x s)
    (G := fun x => ∫ u in s..x, clampedResponse d x u * comparisonForcing p β d s u)
    (A := comparisonForcing p β d s) hs hst (responseGap_row_continuous h s) hY
    (by simp [responseGap,clampedCorrelation_eq hs hs,clampedResponse_eq hs (le_refl s),
      h.correlation_diagonal s hs,h.response_diagonal s hs])
    (fun x hx => responseGap_forward_derivative h hs hx)
    (fun x hx => weighted_response_from_linear_derivative h hF hs hx)
  rw [responseGap,clampedCorrelation_eq (hs.trans hst) hs,clampedResponse_eq hs hst] at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [uIcc_of_le hst] at hu
  dsimp
  rw [clampedResponse_eq (hs.trans hu.1) hu.2]

theorem clampedResponse_nonnegative {d : CKData} (hb : PhysicalBounds d) (t u : ℝ) :
    0 ≤ clampedResponse d t u :=
  hb.2 _ _ (le_max_left _ _) (le_max_right _ _)

theorem clampedCorrelation_nonnegative {d : CKData} (hb : PhysicalBounds d) (t u : ℝ) :
    0 ≤ clampedCorrelation d t u :=
  (hb.1 _ _ (le_max_left _ _) (le_max_left _ _)).1

theorem clampedMemory_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (hp : 3 ≤ p) (hb : PhysicalBounds d) (t u : ℝ) : 0 ≤ clampedMemory p β d t u := by
  unfold clampedMemory xiDoublePrime
  have hpm : 0 ≤ (p : ℝ)-1 := by exact_mod_cast (show 0 ≤ (p : ℤ)-1 by omega)
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hpm)
      (pow_nonneg (clampedCorrelation_nonnegative hb t u) _)))
    (clampedResponse_nonnegative hb t u)

theorem comparisonForcing_nonnegative {p : ℕ} {β : ℝ} {d : CKData}
    (hp : 3 ≤ p) (hb : PhysicalBounds d) {s : ℝ} (hs : 0 ≤ s) (t : ℝ) :
    0 ≤ comparisonForcing p β d s t := by
  unfold comparisonForcing coloredForcing
  apply add_nonneg
  · apply intervalIntegral.integral_nonneg hs
    intro u _
    exact mul_nonneg (clampedMemory_nonnegative hp hb t u)
      (clampedCorrelation_nonnegative hb u s)
  · apply mul_nonneg (mul_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
    apply intervalIntegral.integral_nonneg hs
    intro u _
    exact mul_nonneg (clampedResponse_nonnegative hb s u)
      (pow_nonneg (clampedCorrelation_nonnegative hb t u) _)

/-- Actual response domination, Proposition 4.5 Step 1. The nonnegative
physical CK kernel and genuine variation-of-constants formula give R ≤ C. -/
theorem response_le_correlation {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) : d.R t s ≤ d.C t s := by
  have hz : 0 ≤ d.C t s-d.R t s := by
    rw [response_gap_identity h hs hst]
    apply intervalIntegral.integral_nonneg hst
    intro u hu
    exact mul_nonneg (hb.2 t u (hs.trans hu.1) hu.2)
      (comparisonForcing_nonnegative h.spin_ge_three hb hs u)
  linarith

/-- The complete pointwise comparison in Proposition 4.5. -/
theorem response_correlation_bounds {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) (hb : PhysicalBounds d) {s t : ℝ}
    (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ d.R t s ∧ d.R t s ≤ d.C t s ∧ d.C t s ≤ 1 :=
  ⟨hb.2 t s hs hst,response_le_correlation h hb hs hst,(hb.1 t s (hs.trans hst) hs).2⟩


theorem responseSlope_diagonal {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) {t : ℝ} (ht : 0 ≤ t) :
    responseSlope p β d t t = -d.multiplier t := by
  simp [responseSlope,h.response_diagonal t ht]

/-- All assertions of Proposition 4.4, with endpoint derivatives expressed
on the physical causal rows and with the stated continuous extensions. -/
theorem backward_response_proposition {p : ℕ} {β : ℝ} {d : CKData}
    (h : CKEquations p β d) :
    (∀ t s, 0 ≤ s → s ≤ t →
      HasDerivWithinAt (fun x => d.R t x) (backwardSlope p β d t s) (Icc 0 t) s) ∧
    ContinuousOn (Function.uncurry (responseSlope p β d)) causalTriangle ∧
    ContinuousOn (Function.uncurry (backwardSlope p β d)) causalTriangle ∧
    (∀ t, 0 ≤ t → responseSlope p β d t t = -d.multiplier t) ∧
    (∀ t, 0 ≤ t → backwardSlope p β d t t = d.multiplier t) :=
  ⟨fun _ _ hs hst => response_backward_hasDerivWithinAt h hs hst,
    h.response_slope_continuous,backwardSlope_continuousOn h,
    fun _ ht => responseSlope_diagonal h ht,fun _ ht => backwardSlope_diagonal h ht⟩

end SphericalAging.BackwardResponse
