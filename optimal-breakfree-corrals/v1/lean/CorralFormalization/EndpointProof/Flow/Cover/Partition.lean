import CorralFormalization.EndpointProof.Flow.Cover.Sums
import Mathlib.Data.Fintype.EquivFin

/-!
Every finite balanced tagged set admits an actual decomposition into
pairwise disjoint one-per-part triples. This is the input ordering needed
by the paired cover construction paired-cover iteration; no flow is constructed here.
-/

open scoped Classical BigOperators

namespace EndpointFlow.Cover

open EndpointSelector EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

def partSlice (S : Finset (Vertex G)) (p : Fin 3) : Finset (Vertex G) :=
  S.filter (fun v ↦ v.1 = p)

def Balanced (S : Finset (Vertex G)) : Prop :=
  ∀ p : Fin 3, (partSlice S p).card = (partSlice S 0).card

/-- Exact finite decomposition, not an assumed input enumeration. -/
structure TriplePartition (S : Finset (Vertex G)) (r : ℕ) where
  block : Fin r → Finset (Vertex G)
  onePerPart : ∀ i, OnePerPart (block i)
  pairwise : Pairwise fun i j ↦ Disjoint (block i) (block j)
  union_eq : Finset.univ.biUnion block = S
  card_three : ∀ i, (block i).card = 3

def partEquiv (S : Finset (Vertex G)) (hb : Balanced S) (p : Fin 3) :
    Fin (partSlice S 0).card ≃ ↥(partSlice S p) :=
  (Finset.equivFinOfCardEq (hb p)).symm

def indexedVertex (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) (p : Fin 3) : Vertex G :=
  partEquiv S hb p i

theorem indexedVertex_mem (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) (p : Fin 3) : indexedVertex S hb i p ∈ S :=
  (Finset.mem_filter.mp (partEquiv S hb p i).property).1

@[simp] theorem indexedVertex_part (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) (p : Fin 3) : (indexedVertex S hb i p).1 = p :=
  (Finset.mem_filter.mp (partEquiv S hb p i).property).2

theorem indexedVertex_part_injective (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) : Function.Injective (indexedVertex S hb i) := by
  intro p q hpq
  have h := congrArg Prod.fst hpq
  simpa using h

theorem indexedVertex_index_injective (S : Finset (Vertex G)) (hb : Balanced S)
    (p : Fin 3) : Function.Injective (fun i ↦ indexedVertex S hb i p) := by
  intro i j hij
  apply (partEquiv S hb p).injective
  exact Subtype.ext hij

def indexedBlock (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) : Finset (Vertex G) :=
  Finset.univ.image (indexedVertex S hb i)

theorem indexedBlock_card (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) : (indexedBlock S hb i).card = 3 := by
  simp [indexedBlock,Finset.card_image_of_injective _ (indexedVertex_part_injective S hb i)]

theorem indexedBlock_onePerPart (S : Finset (Vertex G)) (hb : Balanced S)
    (i : Fin (partSlice S 0).card) : OnePerPart (indexedBlock S hb i) := by
  intro p
  refine ⟨(indexedVertex S hb i p).2,?_,?_⟩
  · apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_univ _,?_⟩
    exact Prod.ext (by simp) rfl
  · intro x hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
    have hjp : j = p := by
      have h := congrArg Prod.fst hj
      simpa using h
    subst j
    exact (congrArg Prod.snd hj).symm

theorem indexedBlock_disjoint (S : Finset (Vertex G)) (hb : Balanced S) :
    Pairwise fun i j ↦ Disjoint (indexedBlock S hb i) (indexedBlock S hb j) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro v hvi hvj
  obtain ⟨p,_,hp⟩ := Finset.mem_image.mp hvi
  obtain ⟨q,_,hq⟩ := Finset.mem_image.mp hvj
  have hpq : p = q := by
    have h := congrArg Prod.fst (hp.trans hq.symm)
    simpa using h
  subst q
  exact hij ((indexedVertex_index_injective S hb p) (hp.trans hq.symm))

theorem indexedBlock_union (S : Finset (Vertex G)) (hb : Balanced S) :
    Finset.univ.biUnion (indexedBlock S hb) = S := by
  ext v
  constructor
  · intro hv
    obtain ⟨i,_,hv⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hv
    exact indexedVertex_mem S hb i p
  · intro hv
    let p : Fin 3 := v.1
    have hslice : v ∈ partSlice S p := Finset.mem_filter.mpr ⟨hv,rfl⟩
    let w : ↥(partSlice S p) := ⟨v,hslice⟩
    let i := (partEquiv S hb p).symm w
    apply Finset.mem_biUnion.mpr
    refine ⟨i,Finset.mem_univ _,?_⟩
    apply Finset.mem_image.mpr
    refine ⟨p,Finset.mem_univ _,?_⟩
    change ((partEquiv S hb p) ((partEquiv S hb p).symm w)).val = v
    simp [w]

def balancedTriplePartition (S : Finset (Vertex G)) (hb : Balanced S) :
    TriplePartition S (partSlice S 0).card where
  block := indexedBlock S hb
  onePerPart := indexedBlock_onePerPart S hb
  pairwise := indexedBlock_disjoint S hb
  union_eq := indexedBlock_union S hb
  card_three := indexedBlock_card S hb

theorem balanced_card (S : Finset (Vertex G)) (hb : Balanced S) :
    S.card = 3*(partSlice S 0).card := by
  calc
    S.card = (Finset.univ.biUnion (indexedBlock S hb)).card :=
      congrArg Finset.card (indexedBlock_union S hb).symm
    _ = ∑ i, (indexedBlock S hb i).card := by
      apply Finset.card_biUnion
      intro i hi j hj hij
      exact indexedBlock_disjoint S hb hij
    _ = 3*(partSlice S 0).card := by simp [indexedBlock_card,Nat.mul_comm]

end
end EndpointFlow.Cover
