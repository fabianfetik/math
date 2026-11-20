import CorralFormalization.DiversityCompletion.CyclicReplacement

namespace CorralFormalization.LatinCompletion

/-- Ordinary one-turn prefix offsets immediately preceding a gap of length d. -/
def gapOffsets (d : ℕ) : List ℕ → List ℕ
  | [] => []
  | a :: gs => (if a = d then [0] else []) ++ (gapOffsets d gs).map (a + ·)

/-- Fixed gap tails of a piece frame, computed solely from the unchanged
piece weights. No Latin values occur in this definition. -/
def fixedGapOffsets {I : Type*} (A B : I → ℕ) (d : ℕ) : List (Piece I) → List ℕ
  | [] => []
  | Piece.fixed a :: ps =>
      (if a = d then [0] else []) ++ (fixedGapOffsets A B d ps).map (a + ·)
  | Piece.cell i :: ps => (fixedGapOffsets A B d ps).map (A i + B i + ·)

theorem mem_gapOffsets_iff (d : ℕ) (g : List ℕ) (x : ℕ) :
    x ∈ gapOffsets d g ↔
      ∃ k, k < g.length ∧ g.getD k 0 = d ∧ (g.take k).sum = x := by
  induction g generalizing x with
  | nil => simp [gapOffsets]
  | cons a gs ih =>
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hhead | htail
      · split_ifs at hhead with had
        · have hx0 : x = 0 := by simpa using hhead
          subst x
          exact ⟨0, by simp, by simpa using had, by simp⟩
        · simp at hhead
      · obtain ⟨y, hy, he⟩ := List.mem_map.mp htail
        obtain ⟨k, hk, hget, hsum⟩ := (ih y).mp hy
        refine ⟨k + 1, by simpa using Nat.succ_lt_succ hk, ?_, ?_⟩
        · simpa using hget
        · simpa [List.take_succ_cons, hsum] using he
    · rintro ⟨k, hk, he, hsum⟩
      cases k with
      | zero =>
        have had : a = d := by simpa using he
        have hx0 : x = 0 := by simpa using hsum.symm
        simp [gapOffsets, had, hx0]
      | succ k =>
        have hk' : k < gs.length := by simpa using hk
        have he' : gs.getD k 0 = d := by simpa using he
        have hsum' : a + (gs.take k).sum = x := by simpa using hsum
        exact List.mem_append_right _ (List.mem_map.mpr
          ⟨(gs.take k).sum, (ih _).mpr ⟨k, hk', he', rfl⟩, hsum'⟩)

/-- If the moving gap pairs never contain d, every d-tail is at a fixed
piece boundary, whose prefix offset is independent of the choices. -/
theorem gapOffsets_word_eq_fixed {I : Type*} (A B c : I → ℕ) (d : ℕ)
    (ps : List (Piece I)) (hc : ∀ i, c i ≤ B i)
    (hin : ∀ i, A i + c i ≠ d) (hout : ∀ i, B i - c i ≠ d) :
    gapOffsets d (word A B c ps) = fixedGapOffsets A B d ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    dsimp [word] at ih
    cases p with
    | fixed a => simp [word, Piece.gaps, gapOffsets, fixedGapOffsets, ih]
    | cell i =>
      have hfun : (fun z => A i + c i + (B i - c i + z)) = (A i + B i + ·) := by
        funext z
        have := hc i
        omega
      simp only [word, List.flatMap_cons, Piece.gaps, List.cons_append, List.nil_append,
        gapOffsets, hin i, hout i, if_false, List.nil_append, List.map_map, Function.comp_def]
      rw [hfun, ih]
      rfl

end CorralFormalization.LatinCompletion
