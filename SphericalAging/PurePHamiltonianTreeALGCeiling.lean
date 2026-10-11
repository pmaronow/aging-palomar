module

public import SphericalAging.PurePHamiltonianTreeALGUpper
public import SphericalAging.PurePFiniteForkCorrection

public section

/-! The complete finite tree ALG ceiling with all approximation parameters
chosen internally. The original Gaussian tree law and common event are literal. -/
noncomputable section
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace SphericalAging.PurePHamiltonianTreeALGCeiling
open Set MeasureTheory ProbabilityTheory FiniteModel AdaptiveGradientDisclosure
open IndependentBranchingSuccess RegularTreeEnergyTelescoping HamiltonianTreeEnergy
open HamiltonianTreeFieldBand PurePHamiltonianTreeALGUpper PurePFiniteForkCorrection
open ExternalFieldElementaryPenalty
variable {p : ℕ}

 theorem actual_tree_field_alg_uniform (hp : 3≤p) {H η : ℝ} (hH : 0≤H) (hη : 0<η) :
     ∃δ>0,∀(D : ℕ)(γ : ℝ),0<γ→
       ∃K0 : ℕ,0<K0 ∧ ∀K≥K0,∃N0 : ℕ,∃hN0 : K<N0,∀(N : ℕ)(hNN : N0≤N),
         ∀V Q : ℕ→ℝ,(∀j,0≤V j ∧ V j≤1)→(∀j,V (j+1)≤V j)→
           (∀j,γ≤Q j ∧ Q j≤1)→(∀j,Q (j+1)≤Q j)→V D=0→
           (∀j<D,Q j-Q (j+1)≤δ)→
         ∀h : Vector N,‖h‖≤Real.sqrt N*H→
         ∃E : Set (TensorSpace N p×TreeSample (TensorSpace N p) K D),MeasurableSet E ∧
           1-Real.exp (-(N:ℝ)/2)≤
             ((stdGaussian (TensorSpace N p)).prod (treeLaw (stdGaussian (TensorSpace N p)) K D)).real E ∧
           ∀z∈E,∀c : TreeData (Vector N) K D,TreeForkGeometry Q D c→‖root D c‖^2=(N:ℝ)*Q D→
             totalLeafEnergy V D h c z≤algorithmicField p H+η := by
   obtain ⟨δ,hδ,hbound⟩ := actual_tree_field_alg_ceiling hp hH (by positivity : 0<η/3)
   refine ⟨δ,hδ,?_⟩
   intro D γ hγ
   let ε := η/(6*((D:ℝ)+1))
   have hε : 0<ε := by unfold ε;positivity
   obtain ⟨K1,hK1,hband⟩ := hbound D γ ε hγ hε
   obtain ⟨K2,hK2,hcorr⟩ := exists_correction_cutoff p D (H:=0) (by norm_num) (by positivity : 0<η/3)
   refine ⟨max K1 K2,by omega,?_⟩
   intro K hK
   obtain ⟨N0,hN0,hbandN⟩ := hband K (by omega)
   refine ⟨N0,hN0,?_⟩
   intro N hNN V Q hV hVm hQ hQm hroot hmesh h hnorm
   have hk : (D:ℝ)*Real.sqrt ((p:ℝ)/K)≤η/3 := by
     simpa only [correction,zero_mul,add_zero] using hcorr K (by omega)
   have heps : 2*(D:ℝ)*ε≤η/3 := by
     have hd : 0<(D:ℝ)+1 := by positivity
     have hf : (D:ℝ)/((D:ℝ)+1)≤1 := (div_le_one hd).mpr (by linarith)
     have he : 2*(D:ℝ)*ε=(η/3)*((D:ℝ)/((D:ℝ)+1)) := by
       unfold ε
       field_simp
       <;> ring
     rw [he]
     exact mul_le_of_le_one_right (by positivity : 0≤η/3) hf
   obtain ⟨E,hEm,hEp,hE⟩ := hbandN N hNN V Q hV hVm hQ hQm hroot hmesh h hnorm
   refine ⟨E,hEm,hEp,?_⟩
   intro z hz c hc hx
   exact (hE z hz c hc hx).trans (by linarith)

end SphericalAging.PurePHamiltonianTreeALGCeiling
