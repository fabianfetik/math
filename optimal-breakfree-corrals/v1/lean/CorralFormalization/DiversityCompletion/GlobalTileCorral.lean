import CorralFormalization.DiversityCompletion.PhaseTiling

namespace CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace

open PhaseTiling LatinTransfer PhysicalCorral

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

def tileFirst (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  TileGapWords.row (zeroSite h n q+((n-1 : ℕ) : ZMod (h*n))) (TileGapWords.first n T.body)
def tileTwoSecond (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  TileGapWords.row (zeroSite h n q+2) (TileGapWords.twoSecond n T.body)
def tileThreeSecond (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  TileGapWords.row (zeroSite h n q+2) (TileGapWords.threeSecond n T.body)
def tileThreeThird (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  TileGapWords.row (zeroSite h n (q-1)+12) (TileGapWords.threeThird n T.body)

def tileRows (T : CompletedTerrace n) {m k : ℕ} (i : TileIndex m k) :
    Finset (Finset (ZMod (h*n))) :=
  match i with
  | .inl i =>
    let q := top h (.inl i : TileIndex m k)
    {T.tileFirst q,T.tileThreeSecond q,T.tileThreeThird q}
  | .inr j =>
    let q := top h (.inr j : TileIndex m k)
    {T.tileFirst q,T.tileTwoSecond q}

theorem pair_disjoint {X : Type*} [DecidableEq X] (A B R S : Finset X)
    (hab : Disjoint A B) (hR : R ∈ ({A,B} : Finset (Finset X)))
    (hS : S ∈ ({A,B} : Finset (Finset X))) (hRS : R ≠ S) : Disjoint R S := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hR hS
  rcases hR with rfl | rfl <;> rcases hS with rfl | rfl <;>
    first | exact False.elim (hRS rfl) | exact hab | exact hab.symm

theorem triple_disjoint {X : Type*} [DecidableEq X] (A B C R S : Finset X)
    (hab : Disjoint A B) (hac : Disjoint A C) (hbc : Disjoint B C)
    (hR : R ∈ ({A,B,C} : Finset (Finset X)))
    (hS : S ∈ ({A,B,C} : Finset (Finset X))) (hRS : R ≠ S) : Disjoint R S := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at hR hS
  rcases hR with rfl | rfl | rfl <;> rcases hS with rfl | rfl | rfl <;>
    first | exact False.elim (hRS rfl) | exact hab | exact hac | exact hbc |
      exact hab.symm | exact hac.symm | exact hbc.symm

theorem tileRows_inventory (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (i : TileIndex m k) (R : Finset (ZMod (h*n))) (hR : R ∈ T.tileRows (h := h) i) :
    finiteCyclicGapInventory (h*n) (R.image ZMod.val) = Multiset.ofList (fullGapList n) := by
  cases i with
  | inl i =>
    let q := top h (.inl i : TileIndex m k)
    obtain ⟨ha,hb,hc,hd⟩ := TileGapWords.all_tile_inventories hn hsmall T.body T.differences
      (zeroSite h n q+((n-1 : ℕ) : ZMod (h*n))) (zeroSite h n q+2) (zeroSite h n (q-1)+12)
    simp only [tileRows,Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl | rfl | rfl
    · exact ha
    · exact hc
    · exact hd
  | inr j =>
    let q := top h (.inr j : TileIndex m k)
    obtain ⟨ha,hb,hc,hd⟩ := TileGapWords.all_tile_inventories hn hsmall T.body T.differences
      (zeroSite h n q+((n-1 : ℕ) : ZMod (h*n))) (zeroSite h n q+2) (zeroSite h n (q-1)+12)
    simp only [tileRows,Finset.mem_insert,Finset.mem_singleton] at hR
    rcases hR with rfl | rfl
    · exact ha
    · exact hb

theorem tileRows_disjoint (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (i : TileIndex m k) (R S : Finset (ZMod (h*n)))
    (hR : R ∈ T.tileRows (h := h) i) (hS : S ∈ T.tileRows (h := h) i) (hRS : R ≠ S) : Disjoint R S := by
  cases i with
  | inl i =>
    let q := top h (.inl i : TileIndex m k)
    obtain ⟨hab,hac,hbc,_⟩ := T.three_tile_partition hn hsmall q
    exact triple_disjoint _ _ _ R S hab hac hbc hR hS hRS
  | inr j =>
    let q := top h (.inr j : TileIndex m k)
    have hab := (T.two_tile_partition hn hsmall q).1
    exact pair_disjoint _ _ R S hab hR hS hRS

theorem tileRows_cover (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (i : TileIndex m k) : (T.tileRows (h := h) i).biUnion id = T.tileSupport (h := h) i := by
  cases i with
  | inl i =>
    let q := top h (.inl i : TileIndex m k)
    have hc : T.tileFirst q ∪ T.tileThreeSecond q ∪ T.tileThreeThird q =
      T.roundSites q ∪ T.roundSites (q-1) ∪ T.roundSites (q-2) ∪
        {zeroSite h n q,zeroSite h n (q-2),zeroSite h n (q-1)} :=
      (T.three_tile_partition hn hsmall q).2.2.2
    simp only [tileRows,Finset.biUnion_insert,Finset.singleton_biUnion,id_eq]
    rw [tileSupport,phaseBlock_three]
    simp only [Finset.biUnion_insert,Finset.singleton_biUnion,phaseSupport,← Finset.union_assoc]
    rw [hc]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto
  | inr j =>
    let q := top h (.inr j : TileIndex m k)
    have hc : T.tileFirst q ∪ T.tileTwoSecond q =
      T.roundSites q ∪ T.roundSites (q-1) ∪ {zeroSite h n (q-1),zeroSite h n q} :=
      (T.two_tile_partition hn hsmall q).2
    simp only [tileRows,Finset.biUnion_insert,Finset.singleton_biUnion,id_eq]
    rw [tileSupport,phaseBlock_two]
    simp only [Finset.biUnion_insert,Finset.singleton_biUnion,phaseSupport,← Finset.union_assoc]
    rw [hc]
    ext x
    simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    tauto

theorem tileRows_subset_support (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (i : TileIndex m k) (R : Finset (ZMod (h*n))) (hR : R ∈ T.tileRows (h := h) i) :
    R ⊆ T.tileSupport (h := h) i := by
  intro x hx
  rw [← T.tileRows_cover hn hsmall i]
  exact Finset.mem_biUnion.mpr ⟨R,hR,hx⟩

def globalFamily (T : CompletedTerrace n) (m k : ℕ) : Finset (Finset (ZMod (h*n))) :=
  (Finset.univ : Finset (TileIndex m k)).biUnion (T.tileRows (h := h))

theorem global_inventory (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    (m k : ℕ) (R : Finset (ZMod (h*n))) (hR : R ∈ T.globalFamily (h := h) m k) :
    finiteCyclicGapInventory (h*n) (R.image ZMod.val) = Multiset.ofList (fullGapList n) := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hR
  exact T.tileRows_inventory hn hsmall i R hi

theorem global_disjoint (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) (R S : Finset (ZMod (h*n)))
    (hR : R ∈ T.globalFamily (h := h) m k) (hS : S ∈ T.globalFamily (h := h) m k) (hRS : R ≠ S) : Disjoint R S := by
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hR
  obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hS
  by_cases he : i=j
  · subst j
    exact T.tileRows_disjoint hn hsmall i R S hi hj hRS
  · apply Finset.disjoint_left.mpr
    intro x hxR hxS
    have hxi := T.tileRows_subset_support hn hsmall i R hi hxR
    have hxj := T.tileRows_subset_support hn hsmall j S hj hxS
    obtain ⟨owner,_,huniq⟩ := T.tileSupport_exactly_once htotal x
    exact he ((huniq i hxi).trans (huniq j hxj).symm)

theorem global_full (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) :
    (T.globalFamily (h := h) m k).biUnion id = (Finset.univ : Finset (ZMod (h*n))) := by
  ext x
  simp only [Finset.mem_univ,iff_true]
  obtain ⟨i,hi,_⟩ := T.tileSupport_exactly_once htotal x
  rw [← T.tileRows_cover hn hsmall i] at hi
  obtain ⟨R,hR,hxR⟩ := Finset.mem_biUnion.mp hi
  exact Finset.mem_biUnion.mpr ⟨R,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hR⟩,hxR⟩

theorem card_of_inventory (R : Finset (ZMod (h*n)))
    (hg : finiteCyclicGapInventory (h*n) (R.image ZMod.val) = Multiset.ofList (fullGapList n)) :
    R.card = n := by
  have hc := congrArg Multiset.card hg
  rw [finiteCyclicGapInventory_card,Finset.card_image_of_injective _ (ZMod.val_injective (h*n))] at hc
  simpa [fullGapList] using hc

theorem global_card (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) : (T.globalFamily (h := h) m k).card = h := by
  let F := T.globalFamily (h := h) m k
  have hc : (F.biUnion id).card = ∑ R ∈ F, R.card := by
    apply Finset.card_biUnion
    intro R hR S hS hRS
    exact T.global_disjoint hn hsmall htotal R S hR hS hRS
  have hs : (∑ R ∈ F, R.card) = F.card*n := by
    calc
      _ = ∑ _R ∈ F,n := Finset.sum_congr rfl (fun R hR =>
        card_of_inventory R (T.global_inventory hn hsmall m k R hR))
      _ = _ := by simp
  rw [T.global_full hn hsmall htotal,hs] at hc
  simp only [Finset.card_univ,ZMod.card] at hc
  apply Nat.eq_of_mul_eq_mul_left (NeZero.pos n)
  simpa [Nat.mul_comm] using hc.symm

theorem corral_of_physical_family {H N M : ℕ} [NeZero M]
    (F : Finset (Finset (ZMod M))) (hclock : width N=M) (hcard : F.card=H)
    (hne : ∀ R ∈ F,R.Nonempty)
    (hdis : ∀ R ∈ F,∀ S ∈ F,R ≠ S → Disjoint R S)
    (hgap : ∀ R ∈ F,finiteCyclicGapInventory M (R.image ZMod.val) = Multiset.ofList (fullGapList N)) :
    ∃ R : CorralRows H N,
      Finset.univ.image R.sites = F.image (fun S => S.image ZMod.val) := by
  subst M
  obtain ⟨R,hR⟩ := physical_family_to_corralRows F hcard hne hdis hgap
  refine ⟨R,?_⟩
  rw [← hR,physicalFamily,Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact (physicalSites_decode _ (R.bounded i)).symm

theorem global_corral (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n)
    {m k : ℕ} (htotal : h=3*m+2*k) :
    ∃ R : CorralRows h n, Finset.univ.image R.sites =
      (T.globalFamily (h := h) m k).image (fun S => S.image ZMod.val) := by
  apply corral_of_physical_family _ (optimal_width (NeZero.pos h) hn) (T.global_card hn hsmall htotal)
  · intro R hR
    apply Finset.card_pos.mp
    rw [card_of_inventory R (T.global_inventory hn hsmall m k R hR)]
    exact NeZero.pos n
  · intro R hR S hS hRS
    exact T.global_disjoint hn hsmall htotal R S hR hS hRS
  · exact T.global_inventory hn hsmall m k

/-- A real baseline corral from the explicitly prescribed odd/even schedule:
one triple tile for odd h, two consecutive triple tiles for even h, then pairs.
There is no supplied corral, physical partition or PhysicalFrame premise. -/
theorem canonical_baseline_corral (T : CompletedTerrace n) (hn : n=2*h-1) (hsmall : 15 ≤ n) :
    ∃ R : CorralRows h n, Finset.univ.image R.sites =
      (T.globalFamily (h := h) (canonicalTriples h) (canonicalPairs h)).image (fun S => S.image ZMod.val) :=
  T.global_corral hn hsmall (canonical_total (by omega))

end CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace
