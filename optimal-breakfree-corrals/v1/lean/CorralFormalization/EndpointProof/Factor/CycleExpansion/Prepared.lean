import CorralFormalization.EndpointProof.Factor.CycleExpansion.Conclusion
import CorralFormalization.EndpointProof.Factor.Allocation.UniformContracted

/-! # The actual contracted paper closure expands to the physical conclusion -/

open scoped Classical BigOperators
namespace EndpointFactor.CycleExpansion
open OrdinaryFragments FragmentChecksum Allocation RouterAttachment
open EndpointRouter EndpointLayeredSample EndpointMatching.AbsorptionAssembly
noncomputable section
universe u
variable {G : Type u} [Fintype G] [AddCommGroup G]
variable {m ℓ w d : ℕ} {dist : Densities m} {sample : AugmentedSample G m}
variable {W D X Y : Finset G}

/-- Construct the whole physical cyclic order from the actual chosen
router setting, actual ordinary paths and actual exact-matching/virtual closure. -/
theorem markedCycle_of_contractedClosure
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (hColors : ∀ i, A.color i ⊆ P.ordinaryColour i)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)
    (C : ContractedClosure P A hLayer O) (hℓ : 0 < ℓ) :
    Nonempty (MarkedCycle W D X Y) := by
  let F := preparedFamily P A hLayer hColors O C.firstOn C.secondOn C.first_valid C.second_valid
  let σ := switchProduct C.secondOn * switchProduct C.firstOn
  let ρ := C.closing * σ
  let key : Fin ℓ ≃ F.Index := RouterAttachment.PhysicalRouter.settingKeys P.router O.after
    (outcome_starts P A hLayer O) C.firstOn C.secondOn
  let endAt : Fin ℓ ≃ O.after.ends := σ.trans (preparedEndAtOutput P A hLayer O)
  have hFirst (i : Fin ℓ) : F.first (key i) = P.router.input i :=
    RouterAttachment.PhysicalRouter.prependRouter_track_first P.router O.after
      (outcome_starts P A hLayer O) C.firstOn C.secondOn C.first_valid C.second_valid
      (outcome_point_fresh P A hLayer O) (outcome_color_fresh P A hColors O) i
  have hEnd (i : Fin ℓ) : F.last (key i) = (endAt i).val :=
    RouterAttachment.PhysicalRouter.prependRouter_track_last P.router O.after
      (outcome_starts P A hLayer O) C.firstOn C.secondOn C.first_valid C.second_valid
      (outcome_point_fresh P A hLayer O) (outcome_color_fresh P A hColors O) i
  have hClose (i : Fin ℓ) : F.first (key (ρ i)) = (C.full (endAt i)).val := by
    rw [hFirst]
    exact C.closing_link (σ i)
  have hVirtual : ∀ i, ∀ hy : (endAt i).val ∈ Y,
      F.first (key (ρ i)) = (C.virtual ⟨(endAt i).val,hy⟩).val := by
    intro i hy
    exact (hClose i).trans (C.virtual_link (endAt i) hy)
  have hReal : ∀ i, ∀ hy : (endAt i).val ∉ Y,
      (C.matching.color ⟨(endAt i).val,Finset.mem_sdiff.mpr ⟨(endAt i).property,hy⟩⟩).val =
        F.first (key (ρ i))-F.last (key i) := by
    intro i hy
    exact (C.real_link (endAt i) hy).trans
      (congrArg₂ (fun a b : G => a-b) (hClose i).symm (hEnd i).symm)
  exact exists_markedCycle_of_familyClosure hℓ F key ρ C.one_cycle W D O.after.ends (P.special 0) X Y
    (remainingBank P.bank O.joins P.ordinaryPool A.colors)
    (preparedFamily_vertices P A hLayer hColors O C.firstOn C.secondOn C.first_valid C.second_valid)
    (preparedFamily_colors P A hLayer hColors O C.firstOn C.secondOn C.first_valid C.second_valid)
    (P.remainingBank_subset_target A O) O.prescribed_ends C.matching endAt hEnd C.virtual hVirtual hReal

/-- Both K=0 and K>0 from the constructed physical cycle. There is no
physical cycle, path-factor or endpoint-existence premise. -/
theorem endpointConclusion_of_contractedClosure
    (P : PreparedTarget dist sample W D X Y ℓ w d)
    (A : LayerData G (m+1) ℓ) (hLayer : A.layer = P.ordinaryLayer)
    (hColors : ∀ i, A.color i ⊆ P.ordinaryColour i)
    (O : Outcome A P.ordinaryPool P.leftover P.bank Y)
    (C : ContractedClosure P A hLayer O) (hℓ : 0 < ℓ) :
    CycleCut.PhysicalEndpointConclusion W D X Y := by
  obtain ⟨M⟩ := markedCycle_of_contractedClosure P A hLayer hColors O C hℓ
  exact M.endpointConclusion

/-- The literal prepared floor/remainder predicate exposes positive track
count and all actual closure data, so it receives the same finite result. -/
theorem endpointConclusion_of_preparedWithContractedClosure
    (h : PreparedWithContractedClosure dist sample W D X Y) :
    CycleCut.PhysicalEndpointConclusion W D X Y := by
  dsimp [PreparedWithContractedClosure] at h
  obtain ⟨hℓ,P,A,hLayer,hColors,O,⟨C⟩⟩ := h
  exact endpointConclusion_of_contractedClosure P A hLayer hColors O C hℓ

end
end EndpointFactor.CycleExpansion
