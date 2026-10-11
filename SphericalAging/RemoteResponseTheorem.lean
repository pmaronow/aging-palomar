module

public import SphericalAging.FiniteForkStanding
public import SphericalAging.RemoteResponseScalarLimits
public import SphericalAging.RemoteResponseParameterLimits

public section

/-! Complete local source 11.11. The standing finite fork construction10.4
and unweighted hard-sphere Brownian bridge3.4 remain explicit preceding
inputs. All remote bounds and the ordered long-time limits are proved. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology InnerProductSpace
namespace SphericalAging.RemoteResponseTheorem
open FiniteModel CKSpecification WienerForkTransfer ForkSeedCoordinates FiniteForkMoments
open FiniteForkStanding ForkNormalizedEnergy ForkEnergyComparison RandomGaussianPairing RandomVectorBounds
open RemoteResponseFixedTime RemoteResponseScalarLimits RemoteResponseParameterLimits
open ForkParameterBounds ForkParameterLimits ProfileCenterEnergy ExternalFieldUniformCost
open ExternalFieldElementaryPenalty ExternalFieldSharpScalar WeightedBrownianTheorem WhitePrefixResponse

theorem energyError_nonneg {p K : ℕ} {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hp : 3≤p)
    (hK : 0<K) {β : ℝ} {t T : ℝ≥0}
    {Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)}
    (hY : ∀n,ForkJointLaw β t T (Y n)) (e : ℝ) : 0≤energyError dim e Y := by
  have hb n : |(∫z,Hamiltonian (dim n) p z.1.1.1 (mean (Y n) z)
      ∂forkLaw (dim n) p K)/(dim n:ℝ)|≤GaussianLandscapeMoments.momentCeiling p 1 := by
    have hn : 0<dim n := by have hh := hDim n;omega
    simpa only [energy_transfer] using energy_abs_le hn (by omega : 0<p)
      (disorder_hasLaw (dim n) p K) (seededMean_memLp (hY n)).aestronglyMeasurable
      (seededMean_bound hK (hY n))
  apply le_limsup_of_le (isBoundedUnder_of_eventually_le
    (Eventually.of_forall fun n => (abs_sub _ _).trans (add_le_add (hb n) le_rfl)))
  intro b hb'
  obtain ⟨n,hn⟩ := hb'.exists
  exact (abs_nonneg _).trans hn

theorem normError_nonneg {p K : ℕ} {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n)
    (hK : 0<K) {β : ℝ} {t T : ℝ≥0}
    {Y : ∀n,Fin K→ForkSpace (dim n) p K→Vector (dim n)}
    (hY : ∀n,ForkJointLaw β t T (Y n)) (Q : ℝ) : 0≤normError Q Y := by
  have hb n : (∫z,(‖mean (Y n) z‖^2/(dim n:ℝ)-Q)^2 ∂forkLaw (dim n) p K)≤(1+|Q|)^2 := by
    have hn : 0<dim n := by have hh := hDim n;omega
    simpa only [defect_transfer] using defect_bound hn hK (hY n) Q
  apply le_limsup_of_le (isBoundedUnder_of_eventually_le (Eventually.of_forall hb))
  intro b hb'
  obtain ⟨n,hn⟩ := hb'.exists
  exact (integral_nonneg fun _ => sq_nonneg _).trans hn

theorem sequence_bound {p : ℕ} (hp : 3≤p) {β e q : ℝ} {d : CKData} {c r : ℝ→ℝ}
    (h : CKEquations p β d) (H : Profile c r q) (hq : 0<q)
    (hr : ∀u,0<u→0≤r u) (hPub : ∀Lip : ℝ≥0,PublishedFieldThreshold p Lip)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    (F : Forks dim p β e c r) {K : ℕ} (hK : 1≤K) (L : ℝ≥0)
    (t : ℕ→ℝ≥0) (htp : ∀n,0<t n) (ht : Tendsto (fun n => (t n:ℝ)) atTop atTop)
    (hprimitive : ∀T : ℝ≥0,∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) :
    IsBoundedUnder (·≤·) atTop (fun n => remoteTail d (t n+L) L) ∧
      limsup (fun n => remoteTail d (t n+L) L) atTop≤branchBound p β e c r K L := by
  let Q := forkNorm c K L
  let E := forkEnergy p β e c r K L
  let γ n := energyError dim E (F.branches K L (t n))
  let ζ n := normError Q (F.branches K L (t n))
  let κ n := Real.sqrt (ζ n)/Q
  let δ := thresholdEnergy p-Q^(-((p:ℝ)/2))*E
  have hKn : 0<K := by omega
  have hQB := fork_norm_bounds H hr hK L.coe_nonneg
  have hQ : 0<Q := hq.trans_le (hQB.1.trans hQB.2.1)
  have hQ1 : Q≤1 := hQB.2.2.1
  have hδeq : δ=branchDeficit p β e c r K L := by
    dsimp only [δ,branchDeficit,Q,E]
    rw [Real.rpow_neg hQ.le,div_eq_mul_inv]
    ring
  have hδ : 0≤δ := hδeq.symm ▸ branch_deficit_nonneg hQ (F.ceiling K hK L)
  have hγ : ∀n,0≤γ n := fun n => energyError_nonneg hDim hp hKn (F.branch_law K L (t n)) E
  have hζ : ∀n,0≤ζ n := fun n => normError_nonneg hDim hKn (F.branch_law K L (t n)) Q
  have hκ : ∀n,0≤κ n := fun n => div_nonneg (Real.sqrt_nonneg _) hQ.le
  have hγlim : Tendsto γ atTop (𝓝 0) := F.energy_limit K hK L t htp ht
  have hκlim : Tendsto κ atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero,zero_div] using
      (F.concentration_limit K hK L t htp ht).sqrt.div_const Q
  have hpoint : ∀ε>0,∀n,Real.sqrt (2*remoteTail d (t n+L) L/Q)≤
      (betaD p)^(-((p:ℝ)⁻¹))*(δ+Q^(-((p:ℝ)/2))*γ n+comparison p Q*(ε+κ n))^((p:ℝ)⁻¹)+ε+κ n := by
    intro ε hε n
    obtain ⟨Lip,A,hA,hgood,hApprox⟩ := F.approximation K hK L (t n) (htp n) ε hε
    exact fixed_time hp hKn (hPub Lip) dim hDim hTop h (t n) L (htp n) hQ hQ1
      (hγ n) (hζ n) hε.le hδ (F.branches K L (t n)) (F.branch_law K L (t n))
      A hA hgood le_rfl le_rfl hApprox (hprimitive (t n))
  have hs := time_limit hQ (betaD_positive hp) hδ
    (Real.rpow_nonneg hQ.le _) (comparison_nonneg p Q)
    (fun n => remoteTail_nonneg _ _ _) hγ hκ hγlim hκlim hpoint
  have hl := hs.2
  rw [calibrated_power (betaD_positive hp) hδ,hδeq] at hl
  exact ⟨hs.1,hl⟩

theorem branch_real_ray_bound {p : ℕ} (hp : 3≤p) {β e q : ℝ} {d : CKData} {c r : ℝ→ℝ}
    (h : CKEquations p β d) (H : Profile c r q) (hq : 0<q)
    (hr : ∀u,0<u→0≤r u) (hPub : ∀Lip : ℝ≥0,PublishedFieldThreshold p Lip)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    (F : Forks dim p β e c r) {K : ℕ} (hK : 1≤K) (L : ℝ≥0)
    (hprimitive : ∀T : ℝ≥0,∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) :
    IsBoundedUnder (·≤·) atTop (fun t : ℝ => remoteTail d t L) ∧
      limsup (fun t : ℝ => remoteTail d t L) atTop≤branchBound p β e c r K L := by
  have hs := real_ray_limsup_of_sequences
    (f:=fun T : ℝ => remoteTail d (T+L) L) (fun _ => remoteTail_nonneg _ _ _) (by
      intro t htp ht
      let tN n : ℝ≥0 := ⟨t n,(htp n).le⟩
      exact sequence_bound hp h H hq hr hPub hDim hTop F hK L tN
        (fun n => by exact_mod_cast htp n) ht hprimitive)
  have he : limsup (fun T : ℝ => remoteTail d (T+L) L) atTop=
      limsup (fun t : ℝ => remoteTail d t L) atTop := by
    change limsup ((fun t : ℝ => remoteTail d t L) ∘ (fun T : ℝ => T+(L:ℝ))) atTop=_
    rw [limsup_comp,map_add_atTop_eq]
  rw [he] at hs
  refine ⟨?_,hs.2⟩
  obtain ⟨B,hB⟩ := hs.1
  change ∀ᶠT : ℝ in atTop,remoteTail d (T+L) L≤B at hB
  refine ⟨B,?_⟩
  change ∀ᶠt : ℝ in atTop,remoteTail d t L≤B
  have ht : Tendsto (fun t : ℝ => t-(L:ℝ)) atTop atTop := by
    simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-(L:ℝ)) tendsto_id
  simpa only [sub_add_cancel] using ht.eventually hB

theorem profile_real_ray_bound {p : ℕ} (hp : 3≤p) {β e q : ℝ} {d : CKData} {c r : ℝ→ℝ}
    (hβ : 0≤β) (h : CKEquations p β d) (H : Profile c r q) (hq : 0<q)
    (hr : ∀u,0<u→0≤r u) (hPub : ∀Lip : ℝ≥0,PublishedFieldThreshold p Lip)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    (F : Forks dim p β e c r) (L : ℝ≥0)
    (hprimitive : ∀T : ℝ≥0,∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) :
    IsBoundedUnder (·≤·) atTop (fun t : ℝ => remoteTail d t L) ∧
      limsup (fun t : ℝ => remoteTail d t L) atTop≤profileBound p β e c r L := by
  refine ⟨(branch_real_ray_bound hp h H hq hr hPub hDim hTop F (K:=1) (by norm_num) L hprimitive).1,?_⟩
  apply ge_of_tendsto (branch_bound_tendsto H hβ L.coe_nonneg hq hr)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
  exact (branch_real_ray_bound hp h H hq hr hPub hDim hTop F hK L hprimitive).2

theorem profile_deficit_nonneg {p : ℕ} {β e q : ℝ} {c r : ℝ→ℝ}
    (hβ : 0≤β) (H : Profile c r q) (hq : 0<q) (hr : ∀u,0<u→0≤r u)
    {dim : ℕ→ℕ} (F : Forks dim p β e c r) {L : ℝ} (hL : 0≤L) :
    0≤profileDeficit p β e c r L := by
  apply ge_of_tendsto (branch_deficit_tendsto H hβ hL hq hr)
  filter_upwards [eventually_ge_atTop (1:ℕ)] with K hK
  have hQB := fork_norm_bounds H hr hK hL
  exact branch_deficit_nonneg (hq.trans_le (hQB.1.trans hQB.2.1)) (F.ceiling K hK ⟨L,hL⟩)

/-- Complete local source11.11. The first result is the literal real-ray
bound, the second is its actual age limit, and the third is the remote
localization used in strong response-row convergence. -/
theorem source11_11 {p : ℕ} (hp : 3≤p) {β ell e q : ℝ} {d : CKData} {c r : ℝ→ℝ}
    (hβ : 0<β) (h : CKEquations p β d) (H : Profile c r q) (hq : 0<q) (hq1 : q<1)
    (hell : ell=PlateauAlgebra.multiplier p β q) (he : e=(ell-1)/((p:ℝ)*β))
    (hr : ∀u,0<u→0≤r u) (hm : β^2*PlateauAlgebra.marginalityPolynomial p q=1)
    (hPub : ∀Lip : ℝ≥0,PublishedFieldThreshold p Lip)
    {dim : ℕ→ℕ} (hDim : ∀n,1≤dim n) (hTop : Tendsto dim atTop atTop)
    (F : Forks dim p β e c r)
    (hprimitive : ∀L T : ℝ≥0,∀u : ℝ≥0,u≤T→Tendsto
      (fun n => brownianPrimitive (dim n) p β (T+L) u) atTop
      (𝓝 (∫v in (0:ℝ)..(u:ℝ),d.R (T+L) v))) :
    (∀L : ℝ,0<L→0≤profileDeficit p β e c r L ∧
      limsup (fun t : ℝ => remoteTail d t L) atTop≤
        c (2*L)/2*(betaD p)^(-(2/(p:ℝ)))*
          (thresholdEnergy p-prefixEnergy p β e c r L/(c (2*L))^((p:ℝ)/2))^(2/(p:ℝ))) ∧
    Tendsto (fun L : ℝ => limsup (fun t : ℝ => remoteTail d t L) atTop) atTop (𝓝 0) ∧
    (∀ε : ℝ,0<ε→∀ᶠL : ℝ in atTop,0<L ∧ ∀ᶠt : ℝ in atTop,remoteTail d t L≤ε) := by
  have hlocal (L : ℝ) (hL : 0≤L) := profile_real_ray_bound hp hβ.le h H hq hr hPub
    hDim hTop F (⟨L,hL⟩ : ℝ≥0) (hprimitive ⟨L,hL⟩)
  have hbound := profile_bound_tendsto hp hβ H hq hq1 hell he hr hm
  have hnonneg (L : ℝ) (hL : 0≤L) : 0≤limsup (fun t : ℝ => remoteTail d t L) atTop := by
    apply le_limsup_of_le (hlocal L hL).1
    intro b hb
    obtain ⟨t,ht⟩ := hb.exists
    exact (remoteTail_nonneg d t L).trans ht
  have hlimit : Tendsto (fun L : ℝ => limsup (fun t : ℝ => remoteTail d t L) atTop) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
      ((eventually_ge_atTop (0:ℝ)).mono fun L hL => hnonneg L hL)
      ((eventually_ge_atTop (0:ℝ)).mono fun L hL => (hlocal L hL).2)
  refine ⟨?_,hlimit,?_⟩
  · intro L hL
    exact ⟨profile_deficit_nonneg hβ.le H hq hr F hL.le,(hlocal L hL.le).2⟩
  · intro ε hε
    filter_upwards [eventually_gt_atTop (0:ℝ),hlimit.eventually (eventually_lt_nhds hε)] with L hL hs
    refine ⟨hL,?_⟩
    exact (eventually_lt_of_limsup_lt hs (hlocal L hL.le).1).mono fun _ ht => ht.le

end SphericalAging.RemoteResponseTheorem
