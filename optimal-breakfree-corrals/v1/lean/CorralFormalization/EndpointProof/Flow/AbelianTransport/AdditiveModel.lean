import CorralFormalization.EndpointProof.Probability.SelectorsSixRootsAndCovers

/-!
The actual selector/paired-cover output interfaces over an additive commutative group.
No multiplication, one, or auxiliary ring structure occurs in these model
definitions. The ring-proof adapters only copy actual finite witnesses.
-/

open scoped Classical BigOperators

namespace EndpointFlow.AbelianTransport

open EndpointOriginalReservoir EndpointFullProduct

noncomputable section

section Additive

variable {G : Type*} [Fintype G] [AddCommGroup G]

abbrev Vertex (G : Type*) := Fin 3 × G

def Hyperedge (E : Finset (Vertex G)) : Prop :=
  ∃ x y z : G, x+y+z=0 ∧ E = {(0,x),(1,y),(2,z)}

structure Matching (S : Finset (Vertex G)) where
  edges : Finset (Finset (Vertex G))
  valid : ∀ E ∈ edges, Hyperedge E
  disjoint : (edges : Set (Finset (Vertex G))).Pairwise Disjoint
  cover : edges.biUnion id = S

def support (S : Finset (Vertex G)) : Finset G :=
  S.image Prod.snd ∪ S.image (fun v ↦ -v.2)

def LegalPair (p : Fin 3) (T : Finset (Vertex G)) : Prop :=
  ∃ a : G, a ≠ 0 ∧ T = {(p,a),(p,-a)}

def slice (S : Finset (Vertex G)) (p : Fin 3) : Finset (Vertex G) :=
  S.filter (fun v ↦ v.1=p)

def Balanced (S : Finset (Vertex G)) : Prop :=
  ∀ p : Fin 3, (slice S p).card = (slice S 0).card

def OnePerPart (S : Finset (Vertex G)) : Prop :=
  ∀ p : Fin 3, ∃! x : G, (p,x) ∈ S

/-- Actual P (`false`) and Q (`true`) child membership, on the original
group's existing inverse orbits and the unchanged augmented sample. -/
def ReservoirVertex (ω : FullSample G) (isQ : Bool) (v : Vertex G) : Prop :=
  ∃ (o : OddOrbit G) (side : Bool), orbitPlace (o,side)=v.2 ∧
    childLabel ((regroup ω).1 o) = some (v.1,isQ)

structure Selector (P : Vertex G → Prop) (R : Finset (Finset (Vertex G))) where
  interior : Finset (Vertex G)
  inside : ∀ v ∈ interior, P v
  fresh : ∀ T ∈ R, Disjoint interior T
  matching : ∀ T ∈ R, Nonempty (Matching (interior ∪ T))

def ColouredSelectors (ω : FullSample G) (budget : ℕ) : Prop :=
  ∀ (p : Fin 3) (R : Finset (Finset (Vertex G))),
    R.Nonempty → R.card ≤ 100 → (∀ T ∈ R, LegalPair p T) →
    ∀ F : Finset G, F.card ≤ budget →
    ∃ S : Selector (ReservoirVertex ω false) R,
      S.interior.card ≤ 18*R.card-2 ∧ Disjoint (support S.interior) F ∧
      (support (S.interior ∪ R.biUnion id)).card ≤ 3996

structure SixRootOutput (Q : Vertex G → Prop)
    (O X : Finset (Vertex G)) (F : Finset G) where
  added : Finset (Vertex G)
  output : Finset (Vertex G)
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  added_balanced : Balanced added
  added_card_le : added.card ≤ 18
  output_subset : output ⊆ added
  output_onePerPart : OnePerPart output
  roots_fresh : Disjoint (support added) (support (O ∪ X))
  avoids : Disjoint (support added) F
  matching : Matching (((O ∪ X) ∪ added) \ output)

def SixRootSupplier (Q : Vertex G → Prop) (budget : ℕ) : Prop :=
  ∀ (O X : Finset (Vertex G)) (F : Finset G),
    OnePerPart O → OnePerPart X → Disjoint O X →
    (∀ v ∈ O, v.2 ≠ 0) → (∀ v ∈ X, v.2 ≠ 0) → F.card ≤ budget →
    Nonempty (SixRootOutput Q O X F)

structure PairedCover (Q : Vertex G → Prop) (S : Finset (Vertex G)) (U : Finset G) where
  added : Finset (Vertex G)
  pairsPerPart : ℕ
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  added_balanced : Balanced added
  original_added_disjoint : Disjoint S added
  avoids : Disjoint (support added)
    ((U ∪ S.image Prod.snd) ∪ (U ∪ S.image Prod.snd).image Neg.neg)
  added_card_le : added.card ≤ 6*S.card
  part_card : ∀ p : Fin 3, (slice added p).card = 2*pairsPerPart
  pairs_le : pairsPerPart ≤ S.card
  total_card : added.card = 6*pairsPerPart
  matching : Matching (S ∪ added)

def PairedCoversAvailable (ω : FullSample G) (budget : ℕ) : Prop :=
  ∀ S : Finset (Vertex G), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
    (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G, 2*U.card+20*S.card ≤ budget →
      Nonempty (PairedCover (ReservoirVertex ω true) S U)

/-- One augmentation of the original sample, before every later selector/paired-cover
request. This definition has only the supplied additive group structure. -/
def OriginalAdmitsSelectorsSixRootsAndCovers (externalBudget qBudget : ℕ) (s : OriginalSample G) : Prop :=
  ∃ ω : FullSample G, originalProcess ω = s ∧
    ColouredSelectors ω externalBudget ∧
    SixRootSupplier (ReservoirVertex ω true) qBudget ∧ PairedCoversAvailable ω qBudget

end Additive

section RingAdapters

variable {G : Type*} [Fintype G] [CommRing G]

def matchingOfRing {S : Finset (Vertex G)}
    (M : EndpointSelector.Assembly.MatchingOn S) : Matching S where
  edges := M.edges
  valid := M.valid
  disjoint := M.disjoint
  cover := M.cover

def selectorOfRing {P : Vertex G → Prop} {R : Finset (Finset (Vertex G))}
    (S : EndpointSelector.Assembly.SelectorOn P R) : Selector P R where
  interior := S.interior
  inside := S.inside
  fresh := S.fresh
  matching := fun T hT ↦ ⟨matchingOfRing (Classical.choice (S.matching T hT))⟩

def sixRootOutputOfRing {Q : Vertex G → Prop} {O X : Finset (Vertex G)} {F : Finset G}
    (A : EndpointFlow.Cover.SixRootOutput Q O X F) : SixRootOutput Q O X F where
  added := A.added
  output := A.output
  added_Q := A.added_Q
  added_paired := A.added_paired
  added_nonzero := A.added_nonzero
  added_balanced := A.added_balanced
  added_card_le := A.added_card_le
  output_subset := A.output_subset
  output_onePerPart := A.output_onePerPart
  roots_fresh := A.roots_fresh
  avoids := A.avoids
  matching := matchingOfRing A.matching

def pairedCoverOfRing {Q : Vertex G → Prop} {S : Finset (Vertex G)} {U : Finset G}
    (C : EndpointFlow.Cover.PairedCoverResult Q S U) : PairedCover Q S U where
  added := C.added
  pairsPerPart := C.pairsPerPart
  added_Q := C.added_Q
  added_paired := C.added_paired
  added_nonzero := C.added_nonzero
  added_balanced := C.added_balanced
  original_added_disjoint := C.original_added_disjoint
  avoids := C.avoids
  added_card_le := C.added_card_le
  part_card := C.part_card
  pairs_le := C.pairs_le
  total_card := C.total_card
  matching := matchingOfRing C.matching

/-- The witnesses and the augmentation are copied unchanged. No sampling
law, coordinate relabelling, or independent auxiliary sample is introduced. -/
theorem additive_selectors_sixRoots_and_covers_of_ring {externalBudget qBudget : ℕ} {s : OriginalSample G}
    (h : EndpointFullProduct.OriginalAdmitsSelectorsSixRootsAndCovers externalBudget qBudget s) :
    OriginalAdmitsSelectorsSixRootsAndCovers externalBudget qBudget s := by
  obtain ⟨ω,hω,hselectors,hflow,hcovers⟩ := h
  refine ⟨ω,hω,?_,?_,?_⟩
  · intro p R hne hk hlegal F hF
    obtain ⟨S,hsize,havoid,hsupport⟩ := hselectors p R hne hk hlegal F hF
    exact ⟨selectorOfRing S,hsize,havoid,hsupport⟩
  · intro O X F hO hX hd hOn hXn hF
    obtain ⟨A⟩ := hflow O X F hO hX hd hOn hXn hF
    exact ⟨sixRootOutputOfRing A⟩
  · intro S hb hnz hsum U hbudget
    obtain ⟨C⟩ := hcovers S hb hnz hsum U hbudget
    exact ⟨pairedCoverOfRing C⟩

end RingAdapters

end
end EndpointFlow.AbelianTransport
