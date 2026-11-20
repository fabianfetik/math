import CorralFormalization.EndpointProof.Matching.UniversalCore.FromSupplies
import CorralFormalization.EndpointProof.Flow.AbelianTransport.Access

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
open EndpointFlow.AbelianTransport
open EndpointSelector.FixedCardinality
open EndpointMatching.AbsorptionAssembly
noncomputable section
variable {G : Type*} [AddCommGroup G]

/-- The actual inverse pair containing a tagged vertex. -/
def pairOf (v : Vertex G) : Finset (Vertex G) := {v, (v.1, -v.2)}

def pairLabels (X : Finset (Vertex G)) : Finset (Finset (Vertex G)) :=
  X.image pairOf

theorem pairOf_legal (v : Vertex G) (hn : v.2 ≠ 0) : LegalPair v.1 (pairOf v) := by
  obtain ⟨p,a⟩ := v
  exact ⟨a, hn, rfl⟩

theorem pairOf_mem (v : Vertex G) : v ∈ pairOf v := by simp [pairOf]

theorem pairLabels_biUnion (X : Finset (Vertex G))
    (hpaired : ∀ v ∈ X, (v.1,-v.2) ∈ X) :
    (pairLabels X).biUnion id = X := by
  ext v
  simp only [pairLabels, Finset.mem_biUnion, Finset.mem_image, id_eq]
  constructor
  · rintro ⟨T, ⟨w, hw, rfl⟩, hv⟩
    simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact hw
    · exact hpaired w hw
  · intro hv
    exact ⟨pairOf v, ⟨v,hv,rfl⟩, pairOf_mem v⟩

theorem pairLabels_slice_card [Fintype G] (hodd : Odd (Fintype.card G))
    (X : Finset (Vertex G)) (p : Fin 3)
    (hpaired : ∀ v ∈ X, (v.1,-v.2) ∈ X)
    (hnonzero : ∀ v ∈ X, v.2 ≠ 0) :
    (slice X p).card = 2 * (pairLabels (slice X p)).card := by
  classical
  let Xp := slice X p
  have hpairp : ∀ v ∈ Xp, (v.1,-v.2) ∈ Xp := by
    intro v hv
    have hv' := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hpaired v hv'.1,hv'.2⟩
  have hleg : ∀ T ∈ pairLabels Xp, LegalPair p T := by
    intro T hT
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hT
    have hv' := Finset.mem_filter.mp hv
    have hvp : v.1 = p := hv'.2
    simpa only [hvp] using pairOf_legal v (hnonzero v hv'.1)
  have hdis : (↑(pairLabels Xp) : Set (Finset (Vertex G))).PairwiseDisjoint id := by
    intro T hT T' hT' hne
    exact legalPairs_disjoint (hleg T hT) (hleg T' hT') hne
  have hcount : ∀ T ∈ pairLabels Xp, T.card = 2 := by
    intro T hT
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hT
    have hvX : v ∈ X := (Finset.mem_filter.mp hv).1
    have hneq : v ≠ (v.1,-v.2) := by
      intro he
      exact (ne_neg_of_odd hodd (hnonzero v hvX)) (congrArg Prod.snd he)
    exact Finset.card_pair hneq
  have h := Finset.card_biUnion hdis
  simp only [id_eq] at h
  rw [pairLabels_biUnion Xp hpairp] at h
  have hsum : (∑ T ∈ pairLabels Xp, T.card) = 2 * (pairLabels Xp).card := by
    calc
      _ = ∑ _T ∈ pairLabels Xp, 2 := Finset.sum_congr rfl hcount
      _ = _ := by simp [Nat.mul_comm]
  rw [hsum] at h
  exact h

theorem pairLabels_inter_inventory
    (X : Finset (Vertex G)) (Q : Fin 3 → Finset (Finset (Vertex G)))
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T)
    (hinventory : ∀ v ∈ X, pairOf v ∈ Q v.1) (p : Fin 3) :
    pairLabels X ∩ Q p = pairLabels (slice X p) := by
  ext T
  constructor
  · intro hT
    obtain ⟨hTX,hTQ⟩ := Finset.mem_inter.mp hT
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hTX
    have hp : v.1 = p := legalPair_vertex_part (hlegal p _ hTQ) (pairOf_mem v)
    exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hv,hp⟩, rfl⟩
  · intro hT
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hT
    have hv' := Finset.mem_filter.mp hv
    apply Finset.mem_inter.mpr
    constructor
    · exact Finset.mem_image.mpr ⟨v,hv'.1,rfl⟩
    · simpa only [← hv'.2] using hinventory v hv'.1

/-- A paired cover decomposes into the exact inventory of inverse pairs
used by the universal-core assembly, with no change to its matching. -/
theorem paired_cover_pair_inventory [Fintype G] (hodd : Odd (Fintype.card G))
    (X : Finset (Vertex G)) (S : Finset (Vertex G))
    (Q : Fin 3 → Finset (Finset (Vertex G))) (m : ℕ)
    (hpaired : ∀ v ∈ X, (v.1,-v.2) ∈ X)
    (hnonzero : ∀ v ∈ X, v.2 ≠ 0)
    (hparts : ∀ p, (slice X p).card = 2 * m)
    (hlegal : ∀ p T, T ∈ Q p → LegalPair p T)
    (hinventory : ∀ v ∈ X, pairOf v ∈ Q v.1)
    (hmatch : Nonempty (Matching (S ∪ X))) :
    ∃ T : Finset (Finset (Vertex G)),
      T ⊆ Finset.univ.biUnion Q ∧ (∀ p, (T ∩ Q p).card = m) ∧
      T.biUnion id = X ∧ Nonempty (Matching (S ∪ T.biUnion id)) := by
  refine ⟨pairLabels X, ?_, ?_, pairLabels_biUnion X hpaired, ?_⟩
  · intro T hT
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_biUnion.mpr ⟨v.1, Finset.mem_univ _, hinventory v hv⟩
  · intro p
    rw [pairLabels_inter_inventory X Q hlegal hinventory p]
    have hc := pairLabels_slice_card hodd X p hpaired hnonzero
    have hp := hparts p
    omega
  · rw [pairLabels_biUnion X hpaired]
    exact hmatch

/-- All nonzero paired Q labels in a tagged part that avoid the given
numerical forbidden set. Both signs are retained in the same pair. -/
def availablePairInventory [Fintype G] (Q : Vertex G → Prop)
    (U : Finset G) (p : Fin 3) : Finset (Finset (Vertex G)) :=
  (Finset.univ.filter (fun a : G => Q (p,a) ∧ a ∉ U ∧ -a ∉ U)).image
    (fun a => pairOf (p,a))

theorem availablePairInventory_legal [Fintype G] (Q : Vertex G → Prop)
    (hQ : PairReservoir Q) (U : Finset G) :
    ∀ p T, T ∈ availablePairInventory Q U p → LegalPair p T := by
  intro p T hT
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hT
  exact pairOf_legal (p,a) (hQ.nonzero (p,a) (Finset.mem_filter.mp ha).2.1)

theorem pairOf_mem_availablePairInventory [Fintype G] (Q : Vertex G → Prop)
    (U : Finset G) (X : Finset (Vertex G))
    (hXQ : ∀ v ∈ X, Q v) (havoid : Disjoint (support X) U)
    (v : Vertex G) (hv : v ∈ X) :
    pairOf v ∈ availablePairInventory Q U v.1 := by
  obtain ⟨p,a⟩ := v
  have ha : a ∉ U := by
    intro haU
    apply Finset.disjoint_left.mp havoid _ haU
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(p,a),hv,rfl⟩)
  have hna : -a ∉ U := by
    intro haU
    apply Finset.disjoint_left.mp havoid _ haU
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(p,a),hv,rfl⟩)
  exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, hXQ (p,a) hv, ha, hna⟩, rfl⟩

theorem availablePairInventory_avoids [Fintype G] (Q : Vertex G → Prop)
    (U : Finset G) :
    Disjoint (support ((Finset.univ.biUnion (availablePairInventory Q U)).biUnion id)) U := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hx hxU
  simp only [support, Finset.mem_union, Finset.mem_image] at hx
  rcases hx with ⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩
  all_goals
    obtain ⟨T,hT,hvT⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨p,_,hTp⟩ := Finset.mem_biUnion.mp hT
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hTp
    have ha' := (Finset.mem_filter.mp ha).2
    change v ∈ pairOf (p,a) at hvT
    simp only [pairOf, Finset.mem_insert, Finset.mem_singleton] at hvT
    rcases hvT with rfl | rfl <;> simp_all

/-- The previously constructed paired-cover witness yields the exact pair
inventory and the unchanged matching needed by the core theorem. -/
theorem pairedCover_to_available_inventory [Fintype G]
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (hQ : PairReservoir Q)
    (U : Finset G) (S : Finset (Vertex G)) (C : PairedCover Q S U) (K : ℕ)
    (hK : C.pairsPerPart ≤ K) :
    ∃ (T : Finset (Finset (Vertex G))) (m : ℕ),
      T ⊆ Finset.univ.biUnion (availablePairInventory Q U) ∧
      (∀ p, (T ∩ availablePairInventory Q U p).card = m) ∧ m ≤ K ∧
      Nonempty (Matching (S ∪ T.biUnion id)) := by
  have havoid : Disjoint (support C.added) U := by
    apply C.avoids.mono_right
    exact Finset.Subset.trans Finset.subset_union_left Finset.subset_union_left
  obtain ⟨T, hT, hparts, _, hmatch⟩ := paired_cover_pair_inventory hodd C.added S
    (availablePairInventory Q U) C.pairsPerPart C.added_paired C.added_nonzero
    C.part_card (availablePairInventory_legal Q hQ U)
    (pairOf_mem_availablePairInventory Q U C.added C.added_Q havoid) ⟨C.matching⟩
  exact ⟨T, C.pairsPerPart, hT, hparts, hK, hmatch⟩

/-- The existing joint sample event provides actual core-cover queries at
its own stated budget. No stronger quadratic budget is inferred. -/
theorem sampled_pairedCovers_supply_core [Fintype G]
    (hodd : Odd (Fintype.card G)) (ω : EndpointFullProduct.FullSample G)
    (qBudget capacity K : ℕ) (U : Finset G)
    (hcovers : PairedCoversAvailable ω qBudget)
    (hbudget : 2 * U.card + 20 * capacity ≤ qBudget) (hK : capacity ≤ K) :
    ∀ S : Finset (Vertex G),
      (∀ v ∈ S, v.2 ≠ 0) → Balanced S → (∑ v ∈ S, v.2 = 0) →
      Disjoint ((Finset.univ.biUnion
        (availablePairInventory (ReservoirVertex ω true) U)).biUnion id) S →
      S.card ≤ capacity →
      ∃ (T : Finset (Finset (Vertex G))) (m : ℕ),
        T ⊆ Finset.univ.biUnion (availablePairInventory (ReservoirVertex ω true) U) ∧
        (∀ p, (T ∩ availablePairInventory (ReservoirVertex ω true) U p).card = m) ∧
        m ≤ K ∧ Nonempty (Matching (S ∪ T.biUnion id)) := by
  intro S hnz hb hsum _ hS
  have hbudgetS : 2 * U.card + 20 * S.card ≤ qBudget := by omega
  obtain ⟨C⟩ := hcovers S hb hnz hsum U hbudgetS
  apply pairedCover_to_available_inventory hodd (ReservoirVertex ω true)
    (pairReservoir_of_reservoirVertex ω true) U S C K
  exact C.pairs_le.trans (hS.trans hK)

/-- The paired-cover interface. It permits four added inverse pairs per
merge, hence the bound 3m ≤ 4|S| rather than the older m ≤ |S|. -/
structure FourThirdsPairedCover (Q : Vertex G → Prop)
    (S : Finset (Vertex G)) (U : Finset G) where
  added : Finset (Vertex G)
  pairsPerPart : ℕ
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  avoids : Disjoint (support added) (U ∪ support S)
  part_card : ∀ p : Fin 3, (slice added p).card = 2 * pairsPerPart
  pair_bound : 3 * pairsPerPart ≤ 4 * S.card
  matching : Matching (S ∪ added)

/-- A cover with these bounds, once supplied, meets the core's exact inventory
contract whenever the paper's numerical m-versus-K condition holds. -/
theorem fourThirdsCover_to_available_inventory [Fintype G]
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (hQ : PairReservoir Q)
    (U : Finset G) (S : Finset (Vertex G)) (C : FourThirdsPairedCover Q S U)
    (capacity K : ℕ) (hScard : S.card ≤ capacity) (hK : 4 * capacity ≤ 3 * K) :
    ∃ (T : Finset (Finset (Vertex G))) (m : ℕ),
      T ⊆ Finset.univ.biUnion (availablePairInventory Q U) ∧
      (∀ p, (T ∩ availablePairInventory Q U p).card = m) ∧ m ≤ K ∧
      Nonempty (Matching (S ∪ T.biUnion id)) := by
  obtain ⟨T, hT, hparts, _, hmatch⟩ := paired_cover_pair_inventory hodd C.added S
    (availablePairInventory Q U) C.pairsPerPart C.added_paired C.added_nonzero
    C.part_card (availablePairInventory_legal Q hQ U)
    (pairOf_mem_availablePairInventory Q U C.added C.added_Q
      (C.avoids.mono_right Finset.subset_union_left)) ⟨C.matching⟩
  refine ⟨T, C.pairsPerPart, hT, hparts, ?_, hmatch⟩
  have hbound := C.pair_bound
  omega

/-- The abstract event is uniform over later queries. This definition
does not assert that the event occurs in the sampled model. -/
def FourThirdsCoversAvailable (Q : Vertex G → Prop) (qBudget : ℕ) : Prop :=
  ∀ S : Finset (Vertex G), Balanced S → (∀ v ∈ S, v.2 ≠ 0) →
    (∑ v ∈ S, v.2 = 0) → ∀ U : Finset G,
    2 * U.card + 20 * S.card ≤ qBudget →
      Nonempty (FourThirdsPairedCover Q S U)

theorem fourThirdsCovers_supply_core [Fintype G]
    (hodd : Odd (Fintype.card G)) (Q : Vertex G → Prop) (hQ : PairReservoir Q)
    (qBudget capacity K : ℕ) (U : Finset G)
    (hcovers : FourThirdsCoversAvailable Q qBudget)
    (hbudget : 2 * U.card + 20 * capacity ≤ qBudget)
    (hK : 4 * capacity ≤ 3 * K) :
    ∀ S : Finset (Vertex G),
      (∀ v ∈ S, v.2 ≠ 0) → Balanced S → (∑ v ∈ S, v.2 = 0) →
      Disjoint ((Finset.univ.biUnion (availablePairInventory Q U)).biUnion id) S →
      S.card ≤ capacity →
      ∃ (T : Finset (Finset (Vertex G))) (m : ℕ),
        T ⊆ Finset.univ.biUnion (availablePairInventory Q U) ∧
        (∀ p, (T ∩ availablePairInventory Q U p).card = m) ∧
        m ≤ K ∧ Nonempty (Matching (S ∪ T.biUnion id)) := by
  intro S hnz hb hsum _ hS
  have hbudgetS : 2 * U.card + 20 * S.card ≤ qBudget := by omega
  obtain ⟨C⟩ := hcovers S hb hnz hsum U hbudgetS
  exact fourThirdsCover_to_available_inventory hodd Q hQ U S C capacity K hS hK

end
end EndpointMatching.UniversalCore
