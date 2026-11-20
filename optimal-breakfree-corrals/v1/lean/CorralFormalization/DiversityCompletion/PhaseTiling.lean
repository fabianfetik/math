import CorralFormalization.DiversityCompletion.ThreeTilePartition

namespace CorralFormalization.LatinCompletion.PhaseTiling

open PhysicalCorral

abbrev TileIndex (m k : ℕ) := Fin m ⊕ Fin k

def start {m k : ℕ} : TileIndex m k → ℕ
  | .inl i => 3*i.val
  | .inr j => 3*m+2*j.val

def size {m k : ℕ} : TileIndex m k → ℕ
  | .inl _ => 3
  | .inr _ => 2

def natBlock {m k : ℕ} (i : TileIndex m k) : Finset ℕ :=
  Finset.Ico (start i) (start i+size i)

theorem natBlock_bound {h m k : ℕ} (htotal : h=3*m+2*k) (i : TileIndex m k)
    (x : ℕ) (hx : x ∈ natBlock i) : x < h := by
  cases i with
  | inl i =>
    have hi := i.isLt
    simp only [natBlock,start,size,Finset.mem_Ico] at hx
    omega
  | inr j =>
    have hj := j.isLt
    simp only [natBlock,start,size,Finset.mem_Ico] at hx
    omega

/-- Actual arithmetic ownership of every bounded phase by the consecutive
triple blocks followed by the consecutive pair blocks. -/
theorem natBlock_exactly_once {h m k : ℕ} (htotal : h=3*m+2*k) (x : ℕ) (hx : x<h) :
    ∃! i : TileIndex m k, x ∈ natBlock i := by
  by_cases h3 : x < 3*m
  · let i : Fin m := ⟨x/3,by omega⟩
    refine ⟨.inl i,?_,?_⟩
    · simp only [natBlock,start,size,Finset.mem_Ico]
      dsimp [i]
      omega
    · intro a ha
      cases a with
      | inl j =>
        simp only [natBlock,start,size,Finset.mem_Ico] at ha
        apply congrArg Sum.inl
        apply Fin.ext
        dsimp [i]
        omega
      | inr j =>
        simp only [natBlock,start,size,Finset.mem_Ico] at ha
        omega
  · let j : Fin k := ⟨(x-3*m)/2,by omega⟩
    refine ⟨.inr j,?_,?_⟩
    · simp only [natBlock,start,size,Finset.mem_Ico]
      dsimp [j]
      omega
    · intro a ha
      cases a with
      | inl i =>
        have hi := i.isLt
        simp only [natBlock,start,size,Finset.mem_Ico] at ha
        omega
      | inr i =>
        simp only [natBlock,start,size,Finset.mem_Ico] at ha
        apply congrArg Sum.inr
        apply Fin.ext
        dsimp [j]
        omega

def phaseBlock (h : ℕ) {m k : ℕ} (i : TileIndex m k) : Finset (ZMod h) :=
  physicalSites h (natBlock i)

theorem phaseBlock_mem_iff {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k)
    (i : TileIndex m k) (q : ZMod h) : q ∈ phaseBlock h i ↔ q.val ∈ natBlock i :=
  physicalSites_mem_iff _ (natBlock_bound htotal i) q

theorem phaseBlock_exactly_once {h m k : ℕ} [NeZero h] (htotal : h=3*m+2*k)
    (q : ZMod h) : ∃! i : TileIndex m k, q ∈ phaseBlock h i := by
  obtain ⟨i,hi,huniq⟩ := natBlock_exactly_once htotal q.val q.val_lt
  exact ⟨i,(phaseBlock_mem_iff htotal i q).mpr hi,
    fun j hj => huniq j ((phaseBlock_mem_iff htotal j q).mp hj)⟩

def top (h : ℕ) {m k : ℕ} : TileIndex m k → ZMod h
  | .inl i => ((3*i.val+2 : ℕ) : ZMod h)
  | .inr j => ((3*m+2*j.val+1 : ℕ) : ZMod h)

theorem phaseBlock_three (h : ℕ) {m k : ℕ} (i : Fin m) :
    phaseBlock h (.inl i : TileIndex m k) =
      {top h (.inl i : TileIndex m k),top h (.inl i : TileIndex m k)-1,
        top h (.inl i : TileIndex m k)-2} := by
  have hb : natBlock (.inl i : TileIndex m k) = {3*i.val,3*i.val+1,3*i.val+2} := by
    ext x
    simp only [natBlock,start,size,Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
    omega
  have h₁ : top h (.inl i : TileIndex m k)-1 = ((3*i.val+1 : ℕ) : ZMod h) := by
    simp only [top,Nat.cast_add,Nat.cast_ofNat]; ring
  have h₂ : top h (.inl i : TileIndex m k)-2 = ((3*i.val : ℕ) : ZMod h) := by
    simp only [top,Nat.cast_add,Nat.cast_ofNat]; ring
  rw [phaseBlock,physicalSites,hb,h₁,h₂]
  simp only [Finset.image_insert,Finset.image_singleton]
  ext x
  simp only [top,Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem phaseBlock_two (h : ℕ) {m k : ℕ} (j : Fin k) :
    phaseBlock h (.inr j : TileIndex m k) =
      {top h (.inr j : TileIndex m k),top h (.inr j : TileIndex m k)-1} := by
  have hb : natBlock (.inr j : TileIndex m k) = {3*m+2*j.val,3*m+2*j.val+1} := by
    ext x
    simp only [natBlock,start,size,Finset.mem_Ico,Finset.mem_insert,Finset.mem_singleton]
    omega
  have h₁ : top h (.inr j : TileIndex m k)-1 = ((3*m+2*j.val : ℕ) : ZMod h) := by
    simp only [top,Nat.cast_add,Nat.cast_one]; ring
  rw [phaseBlock,physicalSites,hb,h₁]
  simp only [Finset.image_insert,Finset.image_singleton]
  ext x
  simp only [top,Finset.mem_insert,Finset.mem_singleton]
  tauto

def canonicalTriples (h : ℕ) : ℕ := if h%2=1 then 1 else 2
def canonicalPairs (h : ℕ) : ℕ := (h-3*canonicalTriples h)/2

theorem canonical_total {h : ℕ} (hh : 8 ≤ h) :
    h=3*canonicalTriples h+2*canonicalPairs h := by
  by_cases ho : h%2=1
  · simp only [canonicalPairs,canonicalTriples,if_pos ho]
    omega
  · simp only [canonicalPairs,canonicalTriples,if_neg ho]
    omega

theorem canonical_odd {h : ℕ} (hh : Odd h) : canonicalTriples h = 1 := by
  obtain ⟨k,hk⟩ := hh
  have ho : h%2=1 := by omega
  simp [canonicalTriples,ho]

theorem canonical_even {h : ℕ} (hh : Even h) : canonicalTriples h = 2 := by
  obtain ⟨k,hk⟩ := hh
  have ho : ¬ h%2=1 := by omega
  simp [canonicalTriples,ho]

end CorralFormalization.LatinCompletion.PhaseTiling

namespace CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace

open PhaseTiling

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

def phaseSupport (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  T.roundSites q ∪ {zeroSite h n q}

theorem phaseSupport_disjoint (T : CompletedTerrace n) {q p : ZMod h} (hqp : q ≠ p) :
    Disjoint (T.phaseSupport q) (T.phaseSupport p) := by
  apply Finset.disjoint_left.mpr
  intro x hq hp
  rcases Finset.mem_union.mp hq with hq | hq <;>
    rcases Finset.mem_union.mp hp with hp | hp
  · exact Finset.disjoint_left.mp (T.roundSites_disjoint hqp) hq hp
  · have he := Finset.mem_singleton.mp hp
    exact T.zero_not_mem_round _ _ (he ▸ hq)
  · have he := Finset.mem_singleton.mp hq
    exact T.zero_not_mem_round _ _ (he ▸ hp)
  · have heq := Finset.mem_singleton.mp hq
    have hep := Finset.mem_singleton.mp hp
    exact hqp (zeroSite_injective (NeZero.pos n) (heq.symm.trans hep))

theorem phaseSupport_exactly_once (T : CompletedTerrace n) (x : ZMod (h*n)) :
    ∃! q, x ∈ T.phaseSupport q := by
  have hex : ∃ q, x ∈ T.phaseSupport q := by
    by_cases hx : residueMap h n x = 0
    · obtain ⟨q,hq,_⟩ := (zeroSite_exactly_once x).mp hx
      exact ⟨q,Finset.mem_union_right _ (Finset.mem_singleton.mpr hq.symm)⟩
    · obtain ⟨⟨q,t⟩,hqt,_⟩ := (T.site_exactly_once x).mp hx
      exact ⟨q,Finset.mem_union_left _ (Finset.mem_image.mpr ⟨t,Finset.mem_univ _,hqt⟩)⟩
  obtain ⟨q,hq⟩ := hex
  refine ⟨q,hq,?_⟩
  intro p hp
  by_contra hne
  exact Finset.disjoint_left.mp (T.phaseSupport_disjoint hne) hp hq

def tileSupport (T : CompletedTerrace n) {m k : ℕ} (i : TileIndex m k) : Finset (ZMod (h*n)) :=
  (phaseBlock h i).biUnion T.phaseSupport

theorem tileSupport_exactly_once (T : CompletedTerrace n) {m k : ℕ}
    (htotal : h=3*m+2*k) (x : ZMod (h*n)) :
    ∃! i : TileIndex m k, x ∈ T.tileSupport i := by
  obtain ⟨q,hq,hquniq⟩ := T.phaseSupport_exactly_once x
  obtain ⟨i,hi,hiuniq⟩ := phaseBlock_exactly_once htotal q
  refine ⟨i,Finset.mem_biUnion.mpr ⟨q,hi,hq⟩,?_⟩
  intro j hj
  obtain ⟨p,hp,hxp⟩ := Finset.mem_biUnion.mp hj
  have hpq : p=q := hquniq p hxp
  exact hiuniq j (hpq ▸ hp)

end CorralFormalization.LatinCompletion.TerraceLift.CompletedTerrace
