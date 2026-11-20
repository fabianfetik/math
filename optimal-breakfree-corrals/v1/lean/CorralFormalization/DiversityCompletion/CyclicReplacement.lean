import CorralFormalization.ConstructionSupport.LatinTransfer
import CorralFormalization.ConstructionSupport.PhysicalRows

/-! Local centre replacements in positive one-winding physical gap words.
No endpoint-completion or terrace-existence theorem is asserted here. -/

namespace CorralFormalization.LatinCompletion

open scoped BigOperators
open LatinTransfer

inductive Piece (I : Type*) where
  | fixed : ℕ → Piece I
  | cell : I → Piece I
  deriving DecidableEq

namespace Piece

variable {I : Type*}

def weight (A B : I → ℕ) : Piece I → ℕ
  | fixed d => d
  | cell i => A i + B i

def gaps (A B c : I → ℕ) : Piece I → List ℕ
  | fixed d => [d]
  | cell i => [A i + c i, B i - c i]

end Piece

variable {I : Type*}

def word (A B c : I → ℕ) (ps : List (Piece I)) : List ℕ :=
  ps.flatMap (Piece.gaps A B c)

def cells : List (Piece I) → List I
  | [] => []
  | Piece.fixed _ :: ps => cells ps
  | Piece.cell i :: ps => i :: cells ps

def unchanged : List (Piece I) → Multiset ℕ
  | [] => 0
  | Piece.fixed d :: ps => {d} + unchanged ps
  | Piece.cell _ :: ps => unchanged ps

def fixedOffsets (A B : I → ℕ) (ps : List (Piece I)) : List ℕ :=
  properPrefixSites (ps.map (Piece.weight A B))

def movingOffsets (A B c : I → ℕ) : List (Piece I) → List ℕ
  | [] => []
  | Piece.fixed d :: ps => (movingOffsets A B c ps).map (d + ·)
  | Piece.cell i :: ps => (A i + c i) ::
      (movingOffsets A B c ps).map (A i + B i + ·)

/-- The exact fixed integer-lift position before each variable two-gap block. -/
def locatedCells (A B : I → ℕ) : List (Piece I) → List (I × ℕ)
  | [] => []
  | Piece.fixed d :: ps => (locatedCells A B ps).map (fun p => (p.1, d + p.2))
  | Piece.cell i :: ps => (i, 0) ::
      (locatedCells A B ps).map (fun p => (p.1, A i + B i + p.2))

theorem locatedCells_indices (A B : I → ℕ) (ps : List (Piece I)) :
    (locatedCells A B ps).map Prod.fst = cells ps := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [locatedCells, cells, List.map_map, Function.comp_def, ih]

theorem movingOffsets_locations (A B c : I → ℕ) (ps : List (Piece I)) :
    movingOffsets A B c ps =
      (locatedCells A B ps).map (fun p => p.2 + A p.1 + c p.1) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p <;> simp [movingOffsets, locatedCells, ih, List.map_map,
      Function.comp_def, Nat.add_assoc]

theorem word_sum (A B c : I → ℕ) (ps : List (Piece I))
    (hc : ∀ i, c i ≤ B i) :
    (word A B c ps).sum = (ps.map (Piece.weight A B)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p with
    | fixed d => simpa [word, Piece.gaps, Piece.weight] using congrArg (d + ·) ih
    | cell i =>
      have hi : A i + c i + (B i - c i) = A i + B i := by have := hc i; omega
      simpa [word, Piece.gaps, Piece.weight, List.sum_append, ← Nat.add_assoc, hi]
        using congrArg (A i + B i + ·) ih

theorem word_positive (A B c : I → ℕ) (ps : List (Piece I))
    (hfixed : ∀ d, Piece.fixed d ∈ ps → 0 < d)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, c i < B i) :
    ∀ x ∈ word A B c ps, 0 < x := by
  intro x hx
  obtain ⟨p, hp, hx⟩ := List.mem_flatMap.mp hx
  cases p with
  | fixed d =>
    have hxd : x = d := by simpa [Piece.gaps] using hx
    simpa [hxd] using hfixed d hp
  | cell i =>
    have hi := hA i
    have hs := hc i
    simp only [Piece.gaps, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> omega

theorem word_length (A B c : I → ℕ) (ps : List (Piece I)) :
    (word A B c ps).length = ps.length + (cells ps).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    cases p <;> simp [word, Piece.gaps, cells] at * <;> omega

theorem word_palette (A B c : I → ℕ) (ps : List (Piece I)) :
    Multiset.ofList (word A B c ps) = unchanged ps +
      ((cells ps).map (fun i => ({A i + c i} : Multiset ℕ) + {B i - c i})).sum := by
  induction ps with
  | nil => simp [word, unchanged, cells]
  | cons p ps ih =>
    cases p with
    | fixed d =>
      change ({d} : Multiset ℕ) + Multiset.ofList (word A B c ps) =
        ({d} + unchanged ps) +
          ((cells ps).map (fun i => ({A i + c i} : Multiset ℕ) + {B i - c i})).sum
      rw [ih]
      ac_rfl
    | cell i =>
      change (({A i + c i} : Multiset ℕ) + {B i - c i}) +
          Multiset.ofList (word A B c ps) =
        unchanged ps + ((({A i + c i} : Multiset ℕ) + {B i - c i}) +
          ((cells ps).map (fun i => ({A i + c i} : Multiset ℕ) + {B i - c i})).sum)
      rw [ih]
      ac_rfl

theorem list_map_toFinset (f : ℕ → ℕ) (xs : List ℕ) :
    (xs.map f).toFinset = xs.toFinset.image f := by
  ext x
  simp

theorem prefix_split (A B c : I → ℕ) (ps : List (Piece I))
    (hc : ∀ i, c i ≤ B i) :
    (properPrefixSites (word A B c ps)).toFinset =
      (fixedOffsets A B ps).toFinset ∪ (movingOffsets A B c ps).toFinset := by
  induction ps with
  | nil => simp [word, fixedOffsets, movingOffsets, properPrefixSites]
  | cons p ps ih =>
    cases p with
    | fixed d =>
      simpa [word, Piece.gaps, fixedOffsets, movingOffsets, Piece.weight,
        properPrefixSites, list_map_toFinset, Finset.image_union] using
        congrArg (fun S : Finset ℕ => insert 0 (S.image (d + ·))) ih
    | cell i =>
      have hi : A i + c i + (B i - c i) = A i + B i := by have := hc i; omega
      have hfun : (fun z => A i + c i + (B i - c i + z)) = (A i + B i + ·) := by
        funext z
        omega
      simp only [word, List.flatMap_cons, Piece.gaps, List.cons_append, List.nil_append,
        properPrefixSites, List.map_cons, Nat.add_zero, List.map_map, Function.comp_def]
      rw [hfun]
      simp only [List.toFinset_cons, list_map_toFinset]
      change insert 0 (insert (A i + c i)
        ((properPrefixSites (word A B c ps)).toFinset.image (A i + B i + ·))) = _
      rw [ih]
      simp [fixedOffsets, Piece.weight, properPrefixSites, movingOffsets,
        list_map_toFinset, Finset.image_union, Finset.union_comm]

/-- Physical translation is taken in the actual cyclic site type. -/
def physicalOffsets (W origin : ℕ) (xs : List ℕ) : Finset (ZMod W) :=
  xs.toFinset.image (fun x : ℕ => ((origin + x : ℕ) : ZMod W))

/-- Positive one-winding gap words give their actual physical cyclic gap
inventory, including the wrap and any crossing of physical zero. -/
theorem physical_word_inventory (W origin : ℕ) (g : List ℕ) (hW : 0 < W)
    (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = W) :
    finiteCyclicGapInventory W
      ((physicalOffsets W origin (properPrefixSites g)).image ZMod.val) =
      Multiset.ofList g := by
  have hset : (physicalOffsets W origin (properPrefixSites g)).image ZMod.val =
      (properPrefixSites g).toFinset.image (fun x => (x + origin) % W) := by
    simp only [physicalOffsets, Finset.image_image]
    congr 1
    funext x
    exact (ZMod.val_natCast W (origin + x)).trans (by rw [Nat.add_comm])
  rw [hset, finite_set_cyclic_gap_rotate W origin _ hW]
  · cases g with
    | nil => simp at hsum; omega
    | cons x xs =>
      rw [← hsum]
      exact properPrefixSites_finite_gaps x xs hpos
  · intro p hp
    rw [← hsum]
    exact properPrefixSites_lt_sum g hpos p (List.mem_toFinset.mp hp)

theorem physicalOffsets_card (W origin : ℕ) (xs : List ℕ) (hnodup : xs.Nodup)
    (hbound : ∀ x ∈ xs, x < W) :
    (physicalOffsets W origin xs).card = xs.length := by
  unfold physicalOffsets
  rw [Finset.card_image_of_injOn, List.toFinset_card_of_nodup hnodup]
  intro x hx y hy he
  simp only [Nat.cast_add] at he
  have hv := congrArg ZMod.val (add_left_cancel he)
  rw [ZMod.val_natCast_of_lt (hbound x (List.mem_toFinset.mp hx)),
    ZMod.val_natCast_of_lt (hbound y (List.mem_toFinset.mp hy))] at hv
  exact hv

theorem physical_prefix_card (W origin : ℕ) (g : List ℕ)
    (hpos : ∀ x ∈ g, 0 < x) (hsum : g.sum = W) :
    (physicalOffsets W origin (properPrefixSites g)).card = g.length := by
  rw [physicalOffsets_card, properPrefixSites_length]
  · exact (properPrefixSites_strict g hpos).imp (by intro a b hab; omega)
  · intro p hp
    rw [← hsum]
    exact properPrefixSites_lt_sum g hpos p hp

theorem physical_prefix_split (W origin : ℕ) (A B c : I → ℕ)
    (ps : List (Piece I)) (hc : ∀ i, c i ≤ B i) :
    physicalOffsets W origin (properPrefixSites (word A B c ps)) =
      physicalOffsets W origin (fixedOffsets A B ps) ∪
        physicalOffsets W origin (movingOffsets A B c ps) := by
  unfold physicalOffsets
  rw [prefix_split A B c ps hc, Finset.image_union]

/-- A noncircular cyclic-edge decomposition derived from the local gap
blocks and an ordinary one-winding condition. -/
theorem physical_frame_inventory (W origin : ℕ) (A B c : I → ℕ)
    (ps : List (Piece I)) (hW : 0 < W)
    (hfixed : ∀ d, Piece.fixed d ∈ ps → 0 < d)
    (hA : ∀ i, 0 < A i) (hc : ∀ i, c i < B i)
    (hwinding : (ps.map (Piece.weight A B)).sum = W) :
    finiteCyclicGapInventory W
      ((physicalOffsets W origin (properPrefixSites (word A B c ps))).image ZMod.val) =
      unchanged ps +
        ((cells ps).map (fun i => ({A i + c i} : Multiset ℕ) + {B i - c i})).sum := by
  rw [physical_word_inventory W origin _ hW (word_positive A B c ps hfixed hA hc)
    ((word_sum A B c ps (fun i => (hc i).le)).trans hwinding), word_palette]

end CorralFormalization.LatinCompletion
