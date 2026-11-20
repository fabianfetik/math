import CorralFormalization.EndpointProof.Selector.Assembly.FixedCardinality

open scoped Classical BigOperators
namespace EndpointMatching.UniversalCore
noncomputable section

/-- Pairwise disjoint buffer inventories let us reserve K-m entire
buffers even after an adaptive query has used at most 3m pair labels. -/
theorem select_unblocked_buffers {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (buffers : Finset ι) (pick : ι → Fin 3 → α) (T : Finset α) (K m : ℕ)
    (hunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hTcard : T.card ≤ 3 * m) (hmK : m ≤ K) (hcount : K + 2 * m ≤ buffers.card) :
    ∃ C : Finset ι, C ⊆ buffers ∧ C.card = K - m ∧
      ∀ i ∈ C, ∀ p, pick i p ∉ T := by
  classical
  let bad := buffers.filter (fun i => ∃ p, pick i p ∈ T)
  let mark : ι → Option α := fun i =>
    if h : ∃ p, pick i p ∈ T then some (pick i (Classical.choose h)) else none
  have hbadBound : bad.card ≤ T.card := by
    have hmap : Set.MapsTo mark bad (T.image some) := by
      intro i hi
      have hex : ∃ p, pick i p ∈ T := (Finset.mem_filter.mp hi).2
      have hp := Classical.choose_spec hex
      simp only [mark, dif_pos hex]
      exact Finset.mem_image.mpr ⟨pick i (Classical.choose hex), hp, rfl⟩
    have hinj : Set.InjOn mark bad := by
      intro i hi j hj he
      have hi' := Finset.mem_filter.mp hi
      have hj' := Finset.mem_filter.mp hj
      have hihex : ∃ p, pick i p ∈ T := hi'.2
      have hjhex : ∃ p, pick j p ∈ T := hj'.2
      have heq : pick i (Classical.choose hihex) =
          pick j (Classical.choose hjhex) := by
        have he' := he
        simp only [mark, dif_pos hihex, dif_pos hjhex, Option.some.injEq] at he'
        exact he'
      by_contra hne
      exact hunique i hi'.1 j hj'.1 hne _ _ heq
    have hcard := Finset.card_le_card_of_injOn mark hmap hinj
    rw [Finset.card_image_of_injective _ (Option.some_injective α)] at hcard
    exact hcard
  let good := buffers.filter (fun i => ∀ p, pick i p ∉ T)
  have hparts : good.card + bad.card = buffers.card := by
    have h := Finset.card_filter_add_card_filter_not (s := buffers)
      (fun i => ∃ p, pick i p ∈ T)
    simpa only [good, bad, not_exists, Nat.add_comm] using h
  have hgood : K - m ≤ good.card := by omega
  obtain ⟨C, hCgood, hCcard⟩ := Finset.exists_subset_card_eq hgood
  refine ⟨C, hCgood.trans (Finset.filter_subset _ _), hCcard, ?_⟩
  intro i hi p
  exact (Finset.mem_filter.mp (hCgood hi)).2 p

/-- Pair labels contributed by a chosen family of three-part buffers. -/
def bufferPairs {ι α : Type*} [DecidableEq α] (C : Finset ι)
    (pick : ι → Fin 3 → α) : Finset α :=
  C.biUnion (fun i => Finset.univ.image (pick i))

/-- A later covered residual uses m labels from each part. A stock of at
least 3K disjoint buffers provides K-m untouched buffers, leaving exactly
K pair labels removed from each part in total. -/
theorem pad_pair_inventory {ι α : Type*} [DecidableEq ι] [DecidableEq α]
    (Q : Fin 3 → Finset α) (buffers : Finset ι) (pick : ι → Fin 3 → α)
    (T : Finset α) (K m : ℕ)
    (hQdis : ∀ p q, p ≠ q → Disjoint (Q p) (Q q))
    (hBmem : ∀ i ∈ buffers, ∀ p, pick i p ∈ Q p)
    (hunique : ∀ i ∈ buffers, ∀ j ∈ buffers, i ≠ j →
      ∀ p q, pick i p ≠ pick j q)
    (hTsub : T ⊆ Finset.univ.biUnion Q)
    (hTpart : ∀ p, (T ∩ Q p).card = m)
    (hmK : m ≤ K) (hcount : 3 * K ≤ buffers.card) :
    ∃ C : Finset ι, C ⊆ buffers ∧ C.card = K - m ∧
      (bufferPairs C pick ⊆ Finset.univ.biUnion Q) ∧
      Disjoint (bufferPairs C pick) T ∧
      (∀ p, (bufferPairs C pick ∩ Q p).card = K - m) ∧
      (∀ p, (Q p \ (T ∪ bufferPairs C pick)).card = (Q p).card - K) := by
  classical
  have hTcard : T.card ≤ 3 * m := by
    have hsub : T ⊆ Finset.univ.biUnion (fun p => T ∩ Q p) := by
      intro x hx
      obtain ⟨p, _, hxp⟩ := Finset.mem_biUnion.mp (hTsub hx)
      exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hx, hxp⟩⟩
    calc
      T.card ≤ (Finset.univ.biUnion (fun p => T ∩ Q p)).card := Finset.card_le_card hsub
      _ ≤ ∑ p : Fin 3, (T ∩ Q p).card := Finset.card_biUnion_le
      _ = 3 * m := by simp [hTpart, Nat.mul_comm]
  obtain ⟨C, hCsub, hCcard, hCsafe⟩ :=
    select_unblocked_buffers buffers pick T K m hunique hTcard hmK (by omega)
  let F := bufferPairs C pick
  have hFsub : F ⊆ Finset.univ.biUnion Q := by
    intro x hx
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hBmem i (hCsub hi) p⟩
  have hFdis : Disjoint F T := by
    apply Finset.disjoint_left.mpr
    intro x hx hxT
    obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hx
    exact hCsafe i hi p hxT
  have hFpartSet (p : Fin 3) : F ∩ Q p = C.image (fun i => pick i p) := by
    ext x
    constructor
    · intro hx
      have hxF := (Finset.mem_inter.mp hx).1
      have hxP := (Finset.mem_inter.mp hx).2
      obtain ⟨i, hi, hx⟩ := Finset.mem_biUnion.mp hxF
      obtain ⟨q, _, hx⟩ := Finset.mem_image.mp hx
      have hq : pick i q ∈ Q q := hBmem i (hCsub hi) q
      have hp : pick i q ∈ Q p := by simpa [hx] using hxP
      have hqp : q = p := by
        by_contra hne
        exact Finset.disjoint_left.mp (hQdis q p hne) hq hp
      subst q
      exact Finset.mem_image.mpr ⟨i, hi, hx⟩
    · intro hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_inter.mpr
        ⟨Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨p, Finset.mem_univ _, rfl⟩⟩,
          hBmem i (hCsub hi) p⟩
  have hFpart (p : Fin 3) : (F ∩ Q p).card = K - m := by
    rw [hFpartSet]
    rw [Finset.card_image_of_injOn]
    · exact hCcard
    · intro i hi j hj he
      by_contra hne
      exact hunique i (hCsub hi) j (hCsub hj) hne p p he
  refine ⟨C, hCsub, hCcard, hFsub, hFdis, hFpart, ?_⟩
  intro p
  have hpieces : Q p ∩ (T ∪ F) = (T ∩ Q p) ∪ (F ∩ Q p) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_union]
    tauto
  have hpiecesDis : Disjoint (T ∩ Q p) (F ∩ Q p) :=
    hFdis.symm.mono Finset.inter_subset_left Finset.inter_subset_left
  have hsplit := Finset.card_sdiff_add_card_inter (Q p) (T ∪ F)
  rw [hpieces, Finset.card_union_of_disjoint hpiecesDis, hTpart, hFpart] at hsplit
  dsimp [F] at hsplit
  omega
end
end EndpointMatching.UniversalCore
