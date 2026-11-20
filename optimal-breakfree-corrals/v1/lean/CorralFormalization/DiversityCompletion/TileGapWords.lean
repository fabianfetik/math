import CorralFormalization.DiversityCompletion.TailInvariance

namespace CorralFormalization.LatinCompletion.TileGapWords

open LatinTransfer PhysicalCorral DiversitySymmetry

/-- The actual difference calendar starts at residue n-1. The last gap 2
is the prescribed closing edge from n-3 back to n-1. -/
def cycle (n : ℕ) (body : List ℕ) : List ℕ := [3, 10, n-14, 12] ++ body ++ [2]
def middle (n : ℕ) (body : List ℕ) : List ℕ := [10, n-14, 12] ++ body
def thirdPrefix (n : ℕ) (body : List ℕ) : List ℕ := [n-14, 2, 10] ++ body
def first (n : ℕ) (body : List ℕ) : List ℕ := cycle n body ++ [n]
def twoSecond (n : ℕ) (body : List ℕ) : List ℕ := middle n body ++ [3,n,2]
def threeSecond (n : ℕ) (body : List ℕ) : List ℕ := middle n body ++ [2,3,n]
def threeThird (n : ℕ) (body : List ℕ) : List ℕ := thirdPrefix n body ++ [3,n,12]

theorem coe_cons_add (a : ℕ) (as : List ℕ) :
    Multiset.ofList (a :: as) = {a} + Multiset.ofList as := rfl

theorem first_perm {n : ℕ} (hn : 0 < n) (body : List ℕ)
    (hp : (cycle n body).Perm (fullGapList (n-1))) :
    (first n body).Perm (fullGapList n) := by
  have he : fullGapList (n-1) ++ [n] = fullGapList n := by
    have h := fullGapList_succ (n-1)
    simpa [Nat.sub_add_cancel hn] using h.symm
  simpa only [first, he] using hp.append (List.Perm.refl [n])

theorem twoSecond_perm_first (n : ℕ) (body : List ℕ) :
    (twoSecond n body).Perm (first n body) := by
  apply Multiset.coe_eq_coe.mp
  simp only [twoSecond, middle, first, cycle, ← Multiset.coe_add, coe_cons_add,
    Multiset.coe_nil, add_zero]
  ac_rfl

theorem threeSecond_perm_first (n : ℕ) (body : List ℕ) :
    (threeSecond n body).Perm (first n body) := by
  apply Multiset.coe_eq_coe.mp
  simp only [threeSecond, middle, first, cycle, ← Multiset.coe_add, coe_cons_add,
    Multiset.coe_nil, add_zero]
  ac_rfl

theorem threeThird_perm_first (n : ℕ) (body : List ℕ) :
    (threeThird n body).Perm (first n body) := by
  apply Multiset.coe_eq_coe.mp
  simp only [threeThird, thirdPrefix, first, cycle, ← Multiset.coe_add, coe_cons_add,
    Multiset.coe_nil, add_zero]
  ac_rfl

theorem word_properties {h n : ℕ} (hn : n = 2*h-1) (hh : 0 < h)
    (w : List ℕ) (hp : w.Perm (fullGapList n)) :
    (∀ x ∈ w, 0 < x) ∧ w.sum = h*n ∧ w.length = n := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    exact ((fullGapList_mem n x).mp (hp.mem_iff.mp hx)).1
  · rw [hp.sum_eq, fullGapList_sum, optimal_width hh hn]
  · simpa [fullGapList] using hp.length_eq

def row {M : ℕ} (origin : ZMod M) (w : List ℕ) : Finset (ZMod M) :=
  physicalOffsets M origin.val (properPrefixSites w)

/-- Each literal tile word gives an actual positive one-winding physical
row with the full cyclic palette, including its actual closing wrap. -/
theorem row_inventory {h n : ℕ} [NeZero (h*n)]
    (hn : n = 2*h-1) (hh : 0 < h) (origin : ZMod (h*n))
    (w : List ℕ) (hp : w.Perm (fullGapList n)) :
    finiteCyclicGapInventory (h*n) ((row origin w).image ZMod.val) =
      Multiset.ofList (fullGapList n) := by
  obtain ⟨hpos, hsum, _⟩ := word_properties hn hh w hp
  rw [row, physical_word_inventory _ _ _ (NeZero.pos _) hpos hsum]
  exact Multiset.coe_eq_coe.mpr hp

theorem all_tile_inventories {h n : ℕ} [NeZero (h*n)] (hn : n = 2*h-1)
    (hsmall : 15 ≤ n) (body : List ℕ)
    (hp : (cycle n body).Perm (fullGapList (n-1)))
    (o₁ o₂ o₃ : ZMod (h*n)) :
    finiteCyclicGapInventory (h*n) ((row o₁ (first n body)).image ZMod.val) =
        Multiset.ofList (fullGapList n) ∧
    finiteCyclicGapInventory (h*n) ((row o₂ (twoSecond n body)).image ZMod.val) =
        Multiset.ofList (fullGapList n) ∧
    finiteCyclicGapInventory (h*n) ((row o₂ (threeSecond n body)).image ZMod.val) =
        Multiset.ofList (fullGapList n) ∧
    finiteCyclicGapInventory (h*n) ((row o₃ (threeThird n body)).image ZMod.val) =
        Multiset.ofList (fullGapList n) := by
  have hh : 0 < h := by omega
  have hf := first_perm (by omega : 0 < n) body hp
  exact ⟨row_inventory hn hh _ _ hf,
    row_inventory hn hh _ _ ((twoSecond_perm_first n body).trans hf),
    row_inventory hn hh _ _ ((threeSecond_perm_first n body).trans hf),
    row_inventory hn hh _ _ ((threeThird_perm_first n body).trans hf)⟩

theorem gapOffsets_append (d : ℕ) (g k : List ℕ) :
    gapOffsets d (g ++ k) = gapOffsets d g ++ (gapOffsets d k).map (g.sum + ·) := by
  induction g with
  | nil => simp [gapOffsets]
  | cons a g ih =>
    simp only [List.cons_append, gapOffsets, List.sum_cons, ih, List.map_append,
      List.map_map, Function.comp_def]
    simp [List.append_assoc, Nat.add_assoc]

theorem gapOffsets_eq_nil (d : ℕ) (g : List ℕ) (hg : ∀ a ∈ g, a ≠ d) :
    gapOffsets d g = [] := by
  induction g with
  | nil => rfl
  | cons a g ih =>
    have ha := hg a (by simp)
    have htail : ∀ x ∈ g, x ≠ d := by intro x hx; exact hg x (by simp [hx])
    simp [gapOffsets, ha, ih htail]

theorem body_lt {n : ℕ} (body : List ℕ)
    (hp : (cycle n body).Perm (fullGapList (n-1))) (x : ℕ) (hx : x ∈ body) : x < n := by
  have hxg : x ∈ cycle n body := by simp [cycle, hx]
  have ht := ((fullGapList_mem (n-1) x).mp (hp.mem_iff.mp hxg)).2
  have hz := ((fullGapList_mem (n-1) x).mp (hp.mem_iff.mp hxg)).1
  omega

theorem tile_gapOffsets {n : ℕ} (hsmall : 15 ≤ n) (body : List ℕ)
    (hp : (cycle n body).Perm (fullGapList (n-1))) :
    gapOffsets n (first n body) = [(cycle n body).sum] ∧
    gapOffsets n (twoSecond n body) = [(middle n body).sum + 3] ∧
    gapOffsets n (threeSecond n body) = [(middle n body).sum + 5] ∧
    gapOffsets n (threeThird n body) = [(thirdPrefix n body).sum + 3] := by
  have hbody : ∀ x ∈ body, x ≠ n := by
    intro x hx
    exact Nat.ne_of_lt (body_lt body hp x hx)
  have hcycle : ∀ x ∈ cycle n body, x ≠ n := by
    intro x hx
    have hv := ((fullGapList_mem (n-1) x).mp (hp.mem_iff.mp hx)).2
    omega
  have hmiddle : ∀ x ∈ middle n body, x ≠ n := by
    intro x hx
    simp only [middle, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | hx <;> try omega
    exact hbody x hx
  have hthird : ∀ x ∈ thirdPrefix n body, x ≠ n := by
    intro x hx
    simp only [thirdPrefix, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with (rfl | rfl | rfl) | hx <;> try omega
    exact hbody x hx
  have h2 : 2 ≠ n := by omega
  have h3 : 3 ≠ n := by omega
  have h12 : 12 ≠ n := by omega
  simp [first, twoSecond, threeSecond, threeThird, gapOffsets_append,
    gapOffsets_eq_nil n _ hcycle, gapOffsets_eq_nil n _ hmiddle,
    gapOffsets_eq_nil n _ hthird, gapOffsets, h2, h3, h12]

theorem row_tail {h n : ℕ} [NeZero (h*n)] (hn : n = 2*h-1) (hsmall : 15 ≤ n)
    (origin : ZMod (h*n)) (w : List ℕ) (hp : w.Perm (fullGapList n))
    (k : ℕ) (hk : gapOffsets n w = [k]) : gapTails (row origin w) n = {origin + (k : ZMod (h*n))} := by
  obtain ⟨hpos, hsum, hlen⟩ := word_properties hn (by omega) w hp
  rw [row, gapTails_physicalOffsets _ _ hpos hsum (by omega) n, hk]
  simp [physicalOffsets, Nat.cast_add]

/-- Literal H3 tail formulae, proved for actual physical cyclic rows. The
anchor z is the physical zero-column point z_p; z-n=z_(p-1), z-2n=z_(p-2).
No desired tail set is an assumption. -/
theorem tile_tails {h n : ℕ} [NeZero (h*n)] (hn : n = 2*h-1) (hsmall : 15 ≤ n)
    (body : List ℕ) (hp : (cycle n body).Perm (fullGapList (n-1))) (z : ZMod (h*n)) :
    gapTails (row (z + ((n-1 : ℕ) : ZMod (h*n))) (first n body)) n = {z-1} ∧
    gapTails (row (z+2) (twoSecond n body)) n = {z-(n : ZMod (h*n))} ∧
    gapTails (row (z+2) (threeSecond n body)) n = {z-(n : ZMod (h*n))+2} ∧
    gapTails (row (z-(n : ZMod (h*n))+12) (threeThird n body)) n =
      {z-2*(n : ZMod (h*n))} := by
  have hf := first_perm (by omega : 0 < n) body hp
  have hs : (cycle n body).sum + n = h*n := by
    have ht := (word_properties hn (by omega) (first n body) hf).2.1
    simpa [first] using ht
  have hmid : (middle n body).sum + 5 = (cycle n body).sum := by
    simp [middle, cycle]
    omega
  have hthird : (thirdPrefix n body).sum + 15 = (cycle n body).sum := by
    simp [thirdPrefix, cycle]
    omega
  have hsc := congrArg (fun t : ℕ => (t : ZMod (h*n))) hs
  have hmc := congrArg (fun t : ℕ => (t : ZMod (h*n))) hmid
  have htc := congrArg (fun t : ℕ => (t : ZMod (h*n))) hthird
  simp only [Nat.cast_add, Nat.cast_ofNat, ZMod.natCast_self] at hsc hmc htc
  have hsub : ((n-1 : ℕ) : ZMod (h*n)) = (n : ZMod (h*n))-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
  obtain ⟨ho₁, ho₂, ho₃, ho₄⟩ := tile_gapOffsets hsmall body hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [row_tail hn hsmall _ _ hf _ ho₁, hsub]
    congr 1
    linear_combination hsc
  · rw [row_tail hn hsmall _ _ ((twoSecond_perm_first n body).trans hf) _ ho₂]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    congr 1
    linear_combination hsc + hmc
  · rw [row_tail hn hsmall _ _ ((threeSecond_perm_first n body).trans hf) _ ho₃]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    congr 1
    linear_combination hsc + hmc
  · rw [row_tail hn hsmall _ _ ((threeThird_perm_first n body).trans hf) _ ho₄]
    simp only [Nat.cast_add, Nat.cast_ofNat]
    congr 1
    linear_combination hsc + htc

end CorralFormalization.LatinCompletion.TileGapWords
