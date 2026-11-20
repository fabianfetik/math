import CorralFormalization.Results.GeneralTiles.TerraceTileConstruction

/-!
# Simultaneous binary reversals of genuine two-gap cells

The input is a literal decomposition of an original positive one-turn word.
No palette, adjacency, marker, or validity assertion about a switched row is
assumed. Every binary choice reverses the two consecutive gaps of each cell.
-/

namespace CorralFormalization.Results.SwitchFamily.Physical

open CorralFormalization CorralFormalization.LatinCompletion
open LatinTransfer PhysicalCorral DiversitySymmetry

variable {I : Type*}

def binaryCoefficient (b : I → Bool) (i : I) : ℕ := (b i).toNat

@[simp] theorem binaryCoefficient_le (b : I → Bool) (i : I) :
    binaryCoefficient b i ≤ 1 := Bool.toNat_le (b i)

theorem binary_pair_palette (a : ℕ) (b : Bool) :
    ({a+b.toNat} : Multiset ℕ)+{a+1-b.toNat}={a}+{a+1} := by
  cases b <;> simp [add_comm]

theorem binary_word_palette (A : I → ℕ) (ps : List (Piece I))
    (b c : I → Bool) :
    Multiset.ofList (word A (fun i => A i+1) (binaryCoefficient b) ps)=
      Multiset.ofList (word A (fun i => A i+1) (binaryCoefficient c) ps) := by
  rw [word_palette,word_palette]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  exact (binary_pair_palette (A i) (b i)).trans
    (binary_pair_palette (A i) (c i)).symm

theorem binary_word_sum (A : I → ℕ) (ps : List (Piece I)) (b : I → Bool) :
    (word A (fun i => A i+1) (binaryCoefficient b) ps).sum=
      (ps.map (Piece.weight A (fun i => A i+1))).sum := by
  apply word_sum
  intro i
  have := binaryCoefficient_le b i
  omega

theorem binary_word_positive (A : I → ℕ) (ps : List (Piece I)) (b : I → Bool)
    (hA : ∀ i,0<A i) (hfixed : ∀ d,Piece.fixed d∈ps → 0<d) :
    ∀ x∈word A (fun i => A i+1) (binaryCoefficient b) ps,0<x := by
  apply word_positive _ _ _ _ hfixed hA
  intro i
  have := binaryCoefficient_le b i
  have := hA i
  omega

theorem list_toFinset_map {α β : Type*} [DecidableEq α] [DecidableEq β]
    (f : α → β) (xs : List α) : (xs.map f).toFinset=xs.toFinset.image f := by
  ext x
  simp

/-- A literal positive one-winding frame; the baseline is an actual gap
word, while all other settings and their physical inventories are derived. -/
structure BinaryWordFrame (M : ℕ) (I : Type*) where
  origin : ℕ
  base : I → ℕ
  pieces : List (Piece I)
  base_positive : ∀ i,0<base i
  fixed_positive : ∀ d,Piece.fixed d∈pieces → 0<d
  winding : (pieces.map (Piece.weight base (fun i => base i+1))).sum=M
  length_two : 2≤pieces.length+(cells pieces).length

namespace BinaryWordFrame

variable {M : ℕ} [NeZero M]

def gaps (G : BinaryWordFrame M I) (b : I → Bool) : List ℕ :=
  word G.base (fun i => G.base i+1) (binaryCoefficient b) G.pieces

def row (G : BinaryWordFrame M I) (b : I → Bool) : Finset (ZMod M) :=
  physicalOffsets M G.origin (properPrefixSites (G.gaps b))

def fixedRow (G : BinaryWordFrame M I) : Finset (ZMod M) :=
  physicalOffsets M G.origin (fixedOffsets G.base (fun i => G.base i+1) G.pieces)

def movingRow (G : BinaryWordFrame M I) (b : I → Bool) : Finset (ZMod M) :=
  physicalOffsets M G.origin
    (movingOffsets G.base (fun i => G.base i+1) (binaryCoefficient b) G.pieces)

theorem positive (G : BinaryWordFrame M I) (b : I → Bool) :
    ∀ x∈G.gaps b,0<x :=
  binary_word_positive G.base G.pieces b G.base_positive G.fixed_positive

theorem sum (G : BinaryWordFrame M I) (b : I → Bool) : (G.gaps b).sum=M := by
  exact (binary_word_sum G.base G.pieces b).trans G.winding

theorem length (G : BinaryWordFrame M I) (b : I → Bool) :
    (G.gaps b).length=G.pieces.length+(cells G.pieces).length :=
  word_length _ _ _ _

theorem row_split (G : BinaryWordFrame M I) (b : I → Bool) :
    G.row b=G.fixedRow∪G.movingRow b := by
  apply physical_prefix_split
  intro i
  have := binaryCoefficient_le b i
  omega

theorem inventory (G : BinaryWordFrame M I) (b : I → Bool) :
    finiteCyclicGapInventory M ((G.row b).image ZMod.val)=Multiset.ofList (G.gaps b) :=
  physical_word_inventory M G.origin _ (NeZero.pos M) (G.positive b) (G.sum b)

/-- The complete physical palette of every setting follows from that of
one original word; this is a theorem about actual cyclic gaps, including
the edge crossing physical zero. -/
theorem inventory_eq (G : BinaryWordFrame M I) (b c : I → Bool) :
    finiteCyclicGapInventory M ((G.row b).image ZMod.val)=
      finiteCyclicGapInventory M ((G.row c).image ZMod.val) := by
  rw [G.inventory b,G.inventory c]
  exact binary_word_palette G.base G.pieces b c

theorem card (G : BinaryWordFrame M I) (b : I → Bool) :
    (G.row b).card=G.pieces.length+(cells G.pieces).length := by
  rw [row,physical_prefix_card _ _ _ (G.positive b) (G.sum b),G.length b]

theorem movingOffsets_length (A B c : I → ℕ) (ps : List (Piece I)) :
    (movingOffsets A B c ps).length=(cells ps).length := by
  induction ps with
  | nil => rfl
  | cons p ps ih => cases p <;> simp [movingOffsets,cells,ih]

theorem physicalOffsets_card_le (M origin : ℕ) (xs : List ℕ) :
    (physicalOffsets M origin xs).card≤xs.length := by
  exact (Finset.card_image_le).trans (List.toFinset_card_le _)

/-- Moving cell interiors and all fixed piece boundaries are disjoint.
This is paid by positivity and one winding, with no disjoint-support input. -/
theorem fixed_moving_disjoint (G : BinaryWordFrame M I) (b : I → Bool) :
    Disjoint G.fixedRow (G.movingRow b) := by
  have hf : G.fixedRow.card≤G.pieces.length := by
    simpa only [fixedRow,fixedOffsets,properPrefixSites_length,List.length_map]
      using physicalOffsets_card_le M G.origin
        (fixedOffsets G.base (fun i => G.base i+1) G.pieces)
  have hm : (G.movingRow b).card≤(cells G.pieces).length := by
    simpa only [movingRow,movingOffsets_length]
      using physicalOffsets_card_le M G.origin
        (movingOffsets G.base (fun i => G.base i+1) (binaryCoefficient b) G.pieces)
  have hc := G.card b
  rw [G.row_split b] at hc
  have hi := Finset.card_union_add_card_inter G.fixedRow (G.movingRow b)
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply Finset.card_eq_zero.mp
  omega

theorem movingRow_locations (G : BinaryWordFrame M I) (b : I → Bool) :
    G.movingRow b=
      ((locatedCells G.base (fun i => G.base i+1) G.pieces).map
        (fun p => p.2+G.base p.1+binaryCoefficient b p.1)).toFinset.image
          (fun u : ℕ => ((G.origin+u : ℕ) : ZMod M)) := by
  rw [movingRow,movingOffsets_locations]
  rfl

/-- A common permutation of physical sites realizes the switched word if
it fixes the actual fixed boundaries and has the stated action at every
actual cell interior. This is only a point-action bridge; word validity and
palettes have already been proved independently. -/
theorem row_image (G : BinaryWordFrame M I) (b c : I → Bool)
    (τ : Equiv.Perm (ZMod M))
    (hfixed : ∀ x∈G.fixedRow,τ x=x)
    (hmoving : ∀ i p,(i,p)∈locatedCells G.base (fun i => G.base i+1) G.pieces →
      τ ((G.origin+(p+G.base i+binaryCoefficient b i) : ℕ) : ZMod M)=
        ((G.origin+(p+G.base i+binaryCoefficient c i) : ℕ) : ZMod M)) :
    (G.row b).image τ=G.row c := by
  classical
  rw [G.row_split b,G.row_split c,Finset.image_union]
  have hf : G.fixedRow.image τ=G.fixedRow := by
    ext x
    constructor
    · rintro hx
      obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
      simpa only [hfixed y hy] using hy
    · intro hx
      exact Finset.mem_image.mpr ⟨x,hx,hfixed x hx⟩
  rw [hf]
  congr 1
  rw [G.movingRow_locations b,G.movingRow_locations c]
  simp only [list_toFinset_map,Finset.image_image]
  apply Finset.image_congr
  rintro ⟨i,p⟩ hip
  exact hmoving i p (List.mem_toFinset.mp hip)

/-- If d is absent from both possible gaps of every cell, its full set of
actual physical tails is unchanged. The corresponding heads are tail+d. -/
theorem gapTails_eq (G : BinaryWordFrame M I) (b c : I → Bool) (d : ℕ)
    (havoid : ∀ i,G.base i≠d ∧ G.base i+1≠d) :
    gapTails (G.row b) d=gapTails (G.row c) d := by
  have hcoeff (s : I → Bool) (i : I) : binaryCoefficient s i≤G.base i+1 := by
    have := binaryCoefficient_le s i
    omega
  have hin (s : I → Bool) (i : I) : G.base i+binaryCoefficient s i≠d := by
    cases h : s i
    · simpa [binaryCoefficient,h] using (havoid i).1
    · simpa [binaryCoefficient,h] using (havoid i).2
  have hout (s : I → Bool) (i : I) : G.base i+1-binaryCoefficient s i≠d := by
    cases h : s i
    · simpa [binaryCoefficient,h] using (havoid i).2
    · simpa [binaryCoefficient,h] using (havoid i).1
  have ht (s : I → Bool) :
      gapTails (G.row s) d=
        physicalOffsets M G.origin
          (fixedGapOffsets G.base (fun i => G.base i+1) d G.pieces) := by
    rw [row,gapTails_physicalOffsets _ _ (G.positive s) (G.sum s)
      (by rw [G.length s]; exact G.length_two),gaps,
      gapOffsets_word_eq_fixed _ _ _ _ _ (hcoeff s) (hin s) (hout s)]
  rw [ht b,ht c]

end BinaryWordFrame

end CorralFormalization.Results.SwitchFamily.Physical
