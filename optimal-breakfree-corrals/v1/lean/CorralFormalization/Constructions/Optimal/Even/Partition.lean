import CorralFormalization.Constructions.Optimal.Even.GapRows
import CorralFormalization.BucketGeometry

namespace CorralFormalization

/-- The two source rows used in the paper: the actual printed prefix set
and its actual reflection. -/
def evenConstructionRowSource (k : ℕ) (b : Fin 2) : Finset ℕ :=
  if b.val = 0 then evenConstructionRawPrefixSet k else evenConstructionReflectedSet k

def evenConstructionRowPair (k : ℕ) (b : Fin 2) (s : Fin k) : Finset ℕ :=
  translatedSites k (evenConstructionPeriod k) s.val (evenConstructionRowSource k b)

/-- Translations by full periods leave the smaller-period residue unchanged. -/
theorem evenConstructionTranslated_residue (k s x : ℕ) (S : Finset ℕ)
    (hx : x ∈ translatedSites k (evenConstructionPeriod k) s S) :
    ∃ q ∈ S, q % evenConstructionPeriod k = x % evenConstructionPeriod k := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
  refine ⟨q, hq, ?_⟩
  rw [Nat.mod_mul_left_mod]
  simp [Nat.add_mod]

/-- The source label is visible in the actual projected residue of every
point in its translated row. -/
theorem evenConstructionRowPair_label (k : ℕ) (hk : 1 ≤ k)
    (b : Fin 2) (s : Fin k) (x : ℕ) (hx : x ∈ evenConstructionRowPair k b s) :
    b.val = 0 ↔ x % evenConstructionPeriod k ∈ evenConstructionProjectedSet k := by
  obtain ⟨q, hq, hrem⟩ := evenConstructionTranslated_residue k s.val x
    (evenConstructionRowSource k b) hx
  fin_cases b
  · simp only [evenConstructionRowSource, Fin.val_zero, ↓reduceIte] at hq
    have hm := evenConstructionRawPrefix_projected_mem k q hk hq
    rw [hrem] at hm
    simp [hm]
  · simp only [evenConstructionRowSource, Fin.val_one, one_ne_zero, ↓reduceIte] at hq
    have hn := evenConstructionReflectedSet_projected_complement k q hk hq
    rw [hrem] at hn
    simp [hn]

/-- Both row sources lie in the transversal used in the fiber lemma. -/
theorem evenConstructionRowSource_subset (k : ℕ) (b : Fin 2) :
    evenConstructionRowSource k b ⊆ evenConstructionRawPrefixSet k ∪ evenConstructionReflectedSet k := by
  intro q hq
  fin_cases b
  · exact Finset.mem_union.mpr (Or.inl (by simpa [evenConstructionRowSource] using hq))
  · exact Finset.mem_union.mpr (Or.inr (by simpa [evenConstructionRowSource] using hq))

theorem evenConstructionRowPair_in_union (k : ℕ) (b : Fin 2) (s : Fin k) (x : ℕ)
    (hx : x ∈ evenConstructionRowPair k b s) :
    x ∈ translatedSites k (evenConstructionPeriod k) s.val
      (evenConstructionRawPrefixSet k ∪ evenConstructionReflectedSet k) := by
  obtain ⟨q, hq, heq⟩ := Finset.mem_image.mp hx
  exact Finset.mem_image.mpr ⟨q, evenConstructionRowSource_subset k b hq, heq⟩

/-- The two actual source families and all their period translations
partition the entire physical clock. -/
theorem evenConstructionRowPair_partition (k : ℕ) (hk : 1 ≤ k) (x : ℕ)
    (hx : x < evenConstructionClock k) :
    ∃! bs : Fin 2 × Fin k, x ∈ evenConstructionRowPair k bs.1 bs.2 := by
  let S := evenConstructionRawPrefixSet k ∪ evenConstructionReflectedSet k
  have hbound : ∀ q ∈ S, q < k * evenConstructionPeriod k := by
    intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact evenConstructionRawPrefixSet_clock_bound k q hk hq
    · exact evenConstructionReflectedSet_bound k q hk hq
  have htrans : ∀ r, r < evenConstructionPeriod k → ∃! q, q ∈ S ∧ q % evenConstructionPeriod k = r :=
    evenConstructionTwoPrefixes_transversal k hk
  obtain ⟨s, hs, hsuniq⟩ := transversal_block_translates_partition k (evenConstructionPeriod k) S
    (by omega) (by unfold evenConstructionPeriod; omega) hbound htrans x hx
  have hsplit : x ∈ translatedSites k (evenConstructionPeriod k) s.val (evenConstructionRawPrefixSet k) ∨
      x ∈ translatedSites k (evenConstructionPeriod k) s.val (evenConstructionReflectedSet k) := by
    simpa [S, translatedSites, Finset.image_union] using hs
  have hrowuniq : ∀ (b b' : Fin 2) (s' : Fin k),
      x ∈ evenConstructionRowPair k b s → x ∈ evenConstructionRowPair k b' s' →
      (b', s') = (b, s) := by
    intro b b' s' hb hb'
    have heqs : s' = s := hsuniq s' (evenConstructionRowPair_in_union k b' s' x hb')
    have hl := evenConstructionRowPair_label k hk b s x hb
    have hl' := evenConstructionRowPair_label k hk b' s' x hb'
    have heqb : b' = b := by
      apply Fin.ext
      by_cases hm : x % evenConstructionPeriod k ∈ evenConstructionProjectedSet k
      · have hb0 := hl.2 hm
        have hb0' := hl'.2 hm
        omega
      · have hb0 : b.val ≠ 0 := by intro h; exact hm (hl.1 h)
        have hb0' : b'.val ≠ 0 := by intro h; exact hm (hl'.1 h)
        have hbl := b.isLt
        have hb'l := b'.isLt
        omega
    exact Prod.ext heqb heqs
  rcases hsplit with hleft | hright
  · have hrow : x ∈ evenConstructionRowPair k 0 s := by simpa [evenConstructionRowPair, evenConstructionRowSource] using hleft
    refine ⟨(0, s), hrow, ?_⟩
    intro bs hbs
    exact hrowuniq 0 bs.1 bs.2 hrow hbs
  · have hrow : x ∈ evenConstructionRowPair k 1 s := by simpa [evenConstructionRowPair, evenConstructionRowSource] using hright
    refine ⟨(1, s), hrow, ?_⟩
    intro bs hbs
    exact hrowuniq 1 bs.1 bs.2 hrow hbs

end CorralFormalization
