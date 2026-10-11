module

public import SphericalAging.ActualForkCanonicalLateResponse
public import SphericalAging.ActualForkOrderedTraceReplacement
public import SphericalAging.ActualForkResponseFamily
public import SphericalAging.PhysicalForkMeanEnergyBound
public import SphericalAging.PrefixEnergyReal

public section

/-! The actual physical fork's center energy in the ordered dimension-first
and stationary-time-second limit. Finite fork response matrices, subtraction,
common-past cancellation, and the last-window replacement are constructed.
The only energy input is the preceding single-model Proposition 4.1. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2300000
namespace SphericalAging.ActualForkCenterEnergyLimit
open MeasureTheory ProbabilityTheory StochasticCalculus Set Filter FiniteModel HardSphereDynamics
open ActualForkEnergySubtraction ActualForkTraceFormula ActualForkResponseFamily
open ActualForkCanonicalLateResponse ActualForkOrderedTraceReplacement
open PhysicalForkMeanEnergyBound PhysicalForkCenterConcentration
open CKSpecification StationaryClusterInputs ActualForkMeanBridge SphereFisherHelly
open ActualSphereForkEndpoints ActualResponseWindowLimit ForkParameterBounds
open PhysicalForkConstruction AnnealedHamiltonianEnergyStein TwoTimeResponseTimeParameter
open scoped NNReal ENNReal Topology BigOperators

/-- Precisely the preceding single-model fixed-time energy identification.
No fork energy or late-time conclusion is part of this bridge. -/
@[expose] def CanonicalEnergyBridge {p : ℕ} (β : ℝ≥0) (dim : ℕ→ℕ) (d : CKData) : Prop :=
  ∀t : ℝ≥0,Tendsto (fun j => ActualForkEnergySubtraction.modelEnergy (dim j) p β t)
    atTop (𝓝 (CKSpecification.energy p β d t))

theorem stationary_model_energy_limit {p : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hEnergy : CanonicalEnergyBridge (p:=p) β dim d) (L : ℝ≥0) :
    Tendsto (fun z : ℕ×ℕ => ActualForkEnergySubtraction.modelEnergy (dim z.2) p β
      ((T z.1).toNNReal+L)) ((atTop : Filter ℕ).curry (atTop : Filter ℕ))
      (𝓝 ((ell-1)/((p:ℝ)*(β:ℝ)))) := by
  have hm : Tendsto (fun n => d.multiplier (T n+(L:ℝ))) atTop (𝓝 ell) :=
    (H.multiplier L L.coe_nonneg).tendsto_at (x:=(L:ℝ)) ⟨L.coe_nonneg,le_rfl⟩
  have he : Tendsto (fun n => CKSpecification.energy p β d ((T n).toNNReal+L))
      atTop (𝓝 ((ell-1)/((p:ℝ)*(β:ℝ)))) := by
    have hh := (hm.sub (tendsto_const_nhds (x:=(1:ℝ)))).div_const ((p:ℝ)*(β:ℝ))
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      simp only [NNReal.coe_add,Real.coe_toNNReal _ (hT n)]
      exact (PrefixEnergyLimit.energy_eq_multiplier_quotient h
        (add_nonneg (hT n) L.coe_nonneg)).symm
  exact CurriedLimitTransfer.tendsto_curried_of_iterated_limits
    (Eventually.of_forall fun n => hEnergy ((T n).toNNReal+L)) he

/-- Actual center-energy convergence, with the same constructed response
family in the rank error and the full-history trace replacement. -/
theorem actual_center_energy_ordered_limit {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hprimitive : ResponsePrimitiveBridge (by have hh:=h.spin_ge_three;omega : 2≤p) β dim d)
    (hEnergy : CanonicalEnergyBridge (p:=p) β dim d) (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun z : ℕ×ℕ => meanEnergy (dim z.2) p K β ((T z.1).toNNReal+L) (T z.1).toNNReal)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ))
      (𝓝 (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)) := by
  have hp : 2≤p := by have hh:=h.spin_ge_three;omega
  let U := fun n j => responseFamily (by have hd:=hDim j;omega : 0<dim j)
    hp hK β ((T n).toNNReal+L) (T n).toNNReal
  let trace := fun n j => (β:ℝ)*(p:ℝ)*(K:ℝ)⁻¹*∑b : Fin K,
    ∫a,subtractionField β ((T n).toNNReal+L) (T n).toNNReal b (U n j b) a
      ∂integratedLaw (dim j) p K ((T n).toNNReal+L)
  have htraceError := actual_ordered_averaged_trace_replacement H hT dim hDim hTop E hLaw
    hbridge hi hn hL1 hK L U
    (fun n j b => (responseFamily_spec (by have hd:=hDim j;omega : 0<dim j)
      hp hK β ((T n).toNNReal+L) (T n).toNNReal).1 b)
    (fun n j b => (responseFamily_spec (by have hd:=hDim j;omega : 0<dim j)
      hp hK β ((T n).toNNReal+L) (T n).toNNReal).2.1 b)
  have hcanonical := (canonicalLateResponse_ordered_limit (K:=K) hp β dim
    (fun j => by have hd:=hDim j;omega) H hT hprimitive L).const_mul ((β:ℝ)*(p:ℝ))
  have htrace : Tendsto (fun z : ℕ×ℕ => trace z.1 z.2)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ))
      (𝓝 ((β:ℝ)*(p:ℝ)*(∫τ in (0:ℝ)..L,r τ*(c τ^(p-1)-mixedOverlap c K L τ^(p-1))))) := by
    simpa only [trace,U,canonicalLateWeightedResponse,canonicalLateResponse,
      sub_add_cancel,zero_add] using htraceError.add hcanonical
  have hres (n : ℕ) : Tendsto (fun j =>
      ActualForkEnergySubtraction.modelEnergy (dim j) p β ((T n).toNNReal+L)-
        meanEnergy (dim j) p K β ((T n).toNNReal+L) (T n).toNNReal-trace n j)
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    exact actual_energy_subtraction_residual_sequence_limit hp hK dim hDim hTop β
      ((T n).toNNReal+L) (T n).toNNReal
  have hr : Tendsto (fun z : ℕ×ℕ =>
      ActualForkEnergySubtraction.modelEnergy (dim z.2) p β ((T z.1).toNNReal+L)-
        meanEnergy (dim z.2) p K β ((T z.1).toNNReal+L) (T z.1).toNNReal-trace z.1 z.2)
      ((atTop : Filter ℕ).curry (atTop : Filter ℕ)) (𝓝 0) :=
    CurriedLimitTransfer.tendsto_curried_of_iterated_limits
    (Eventually.of_forall hres) (tendsto_const_nhds (x:=0))
  have hh := ((stationary_model_energy_limit H hT dim hEnergy L).sub htrace).sub hr
  simp only [sub_zero] at hh
  change Tendsto _ _ (𝓝 (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)) at hh
  apply hh.congr
  intro z
  ring

/-- Literal source10.4(a) energy error: the dimension limsup followed by
stationary time. Its necessary boundedness follows from the actual Gaussian
landscape first moment and the ball-valued physical mean. -/
theorem actual_energyError_tendsto {p K : ℕ} {β : ℝ≥0} {d : CKData}
    {h : CKEquations p β d} {T : ℕ→ℝ} {c r : ℝ→ℝ} {ell q : ℝ}
    (H : Cluster h T c r ell q) (hT : ∀n,0≤T n)
    (dim : ℕ→ℕ) (hDim : ∀j,3≤dim j) (hTop : Tendsto dim atTop atTop)
    (E : ∀j,FisherDensity (dim j) p β)
    (hLaw : ∀j,WaitingDensityLaw β (dim j+1) (modelRadius_pos (dim j)) (E j))
    (hbridge : MeanBridge (p:=p) β dim (fun j => dim j+1)
      (fun j => modelRadius_pos (dim j)) d)
    {f : ℝ→ℝ} (hi : IntegrableOn f (Ioi 0)) (hn : ∀t,0≤f t)
    (hL1 : ∀t,Tendsto (fun j => ∫w in Ioc 0 t,|(E j).full w-f w|) atTop (𝓝 0))
    (hprimitive : ResponsePrimitiveBridge (by have hh:=h.spin_ge_three;omega : 2≤p) β dim d)
    (hEnergy : CanonicalEnergyBridge (p:=p) β dim d) (hK : 0<K) (L : ℝ≥0) :
    Tendsto (fun n => FiniteForkStanding.energyError dim
      (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)
      (fun j => branch (N:=dim j) (p:=p) (K:=K) β ((T n).toNNReal+L) (T n).toNNReal))
      atTop (𝓝 0) := by
  apply ordered_limsup_tendsto
    (M:=GaussianLandscapeMoments.momentCeiling p 1+
      |forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L|)
  · exact fun _ _ => abs_nonneg _
  · exact fun n j => physical_mean_energy_error_bound
      (by have hd:=hDim j;omega) (by have hh:=h.spin_ge_three;omega) hK β
        ((T n).toNNReal+L) (T n).toNNReal _
  · simpa only [meanEnergy,sub_self,abs_zero] using
      ((actual_center_energy_ordered_limit H hT dim hDim hTop E hLaw hbridge hi hn hL1
        hprimitive hEnergy hK L).sub_const
          (forkEnergy p β ((ell-1)/((p:ℝ)*(β:ℝ))) c r K L)).abs

end SphericalAging.ActualForkCenterEnergyLimit
