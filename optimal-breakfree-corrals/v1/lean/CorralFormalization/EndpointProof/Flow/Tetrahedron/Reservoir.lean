import CorralFormalization.EndpointProof.Matching.UniversalCore.SampledCore
open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointFullProduct EndpointOriginalReservoir
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- One sampled inverse orbit cannot carry the same child label in two
different tagged parts. -/
theorem reservoir_part_unique (ω : FullSample G) (kind : Bool) (p q : Fin 3) (a : G)
    (hp : ReservoirVertex ω kind (p,a)) (hq : ReservoirVertex ω kind (q,a)) : p = q := by
  obtain ⟨o,s,hs,ho⟩ := hp
  obtain ⟨o',s',hs',ho'⟩ := hq
  have he : (o,s) = (o',s') := orbitPlace.injective (hs.trans hs'.symm)
  have heo : o = o' := congrArg Prod.fst he
  subst o'
  have hl := ho.symm.trans ho'
  exact congrArg Prod.fst (Option.some.inj hl)

theorem reservoir_part_unique_up_to_sign (ω : FullSample G) (kind : Bool)
    (p q : Fin 3) (a b : G)
    (hp : ReservoirVertex ω kind (p,a)) (hq : ReservoirVertex ω kind (q,b))
    (he : a = b ∨ a = -b) : p = q := by
  rcases he with he | he
  · subst b
    exact reservoir_part_unique ω kind p q a hp hq
  · have hp' : ReservoirVertex ω kind (p,-a) :=
      (pairReservoir_of_reservoirVertex ω kind).paired (p,a) hp
    have hminus : -a = b := by rw [he, neg_neg]
    rw [hminus] at hp'
    exact reservoir_part_unique ω kind p q b hp' hq

end
end EndpointMatching.Tetrahedron
