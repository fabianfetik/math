import CorralFormalization.DiversityCompletion.LatinConnectorGreedyRun

/-!
# Successive cells in the lexicographic prefix order

The direct-join proof uses each preceding cell once, and every successor is
either the next column of the same row or the first column of the next row.
These facts refer to the actual `lexEdges` list used by the prefix.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

open LatinTransfer LatinPrefixSupply LatinPrefixSupply.ConnectorGreedy

private theorem zip_tail_first {α : Type*} (l : List α) :
    (l.zip l.tail).map Prod.fst = l.dropLast := by
  induction l with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b bs => simpa using congrArg (List.cons a) ih

/-- No cell is used twice as the source of a direct join. -/
theorem lexEdges_sources_nodup (r : ℕ) :
    ((lexEdges r).map Prod.fst).Nodup := by
  have hs : (lexCells r).Nodup :=
    (lexCells_perm r).nodup_iff.mpr (Finset.nodup_toList _)
  rw [lexEdges, zip_tail_first, List.dropLast_eq_take]
  exact hs.take

/-- Every actual consecutive edge has precisely one of the two forms used
by the direct-join colours in L11 and L12. -/
theorem lexEdges_successor {r : ℕ} [NeZero r] {e : Cell r × Cell r}
    (he : e ∈ lexEdges r) :
    (e.2.1.val = e.1.1.val ∧ e.2.2.val = e.1.2.val+1) ∨
      (e.1.2.val+1 = r ∧ e.2.2.val = 0 ∧ e.2.1.val = e.1.1.val+1) := by
  obtain ⟨i, hi, hev⟩ := List.mem_iff_getElem.mp he
  have hi1 : i+1 < (lexCells r).length := by
    have h := hi
    simp only [lexEdges, List.length_zip, List.length_tail] at h
    omega
  have hi0 : i < (lexCells r).length := by omega
  have hpair : ((lexCells r)[i], (lexCells r)[i+1]) = e := by
    simpa only [lexEdges, List.getElem_zip, List.getElem_tail] using hev
  have hfirst : (lexCells r)[i] = e.1 := congrArg Prod.fst hpair
  have hsecond : (lexCells r)[i+1] = e.2 := congrArg Prod.snd hpair
  have h0 := lexCells_rank r i hi0
  have h1 := lexCells_rank r (i+1) hi1
  rw [hfirst] at h0
  rw [hsecond] at h1
  change e.1.2.val+r*e.1.1.val=i at h0
  change e.2.2.val+r*e.2.1.val=i+1 at h1
  have heq : e.2.2.val+r*e.2.1.val = (e.1.2.val+1)+r*e.1.1.val := by omega
  have hd := congrArg (fun x : ℕ => x/r) heq
  rw [Nat.add_mul_div_left _ _ (NeZero.pos r),
      Nat.add_mul_div_left _ _ (NeZero.pos r), Nat.div_eq_of_lt e.2.2.isLt] at hd
  by_cases hwithin : e.1.2.val+1 < r
  · rw [Nat.div_eq_of_lt hwithin] at hd
    left
    constructor
    · omega
    · have hc : e.2.1.val=e.1.1.val := by omega
      rw [hc] at heq
      omega
  · have hend : e.1.2.val+1=r := by have := e.1.2.isLt; omega
    rw [hend, Nat.div_self (NeZero.pos r)] at hd
    right
    refine ⟨hend, ?_, by omega⟩
    have hc : e.2.1.val=e.1.1.val+1 := by omega
    rw [hc, hend] at heq
    nlinarith

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
