import CorralFormalization.DiversityCompletion.TailMarker

/-!
The concrete gap-n tails listed in §8.5.  A is the set of starts of
two-tiles and B the set of starts of three-tiles, as physical points.
The geometry of the tiles must separately establish that these are the
actual tails; this module proves the marker consequences of the formulas.
-/

namespace CorralLatinTailMarker

variable {h n : ℕ}

def tileTails (A B : Finset (ZMod (h * n))) : Finset (ZMod (h * n)) :=
  ((A ∪ B).image (fun p => p - 1) ∪
    A.image (fun p => p - (n : ZMod (h * n))) ∪
    B.image (fun p => p - 2 * (n : ZMod (h * n)))) ∪
    B.image (fun p => p - (n : ZMod (h * n)) + 2)

private theorem res_two : residueMap h n (2 : ZMod (h * n)) = (2 : ZMod n) := by
  change residueMap h n ((2 : ℕ) : ZMod (h * n)) = ((2 : ℕ) : ZMod n)
  exact map_natCast (residueMap h n) 2

private theorem residues_distinct (hn : 7 ≤ n) :
    (-1 : ZMod n) ≠ 2 ∧ (0 : ZMod n) ≠ 2 := by
  have h3 : (3 : ZMod n) ≠ 0 :=
    small_cast_ne_zero (n := n) (k := 3) (by decide) (by omega)
  have h2 : (2 : ZMod n) ≠ 0 :=
    small_cast_ne_zero (n := n) (k := 2) (by decide) (by omega)
  constructor
  · intro he
    apply h3
    linear_combination -he
  · exact Ne.symm h2

theorem tileTails_residue_two (hn : 7 ≤ n)
    (A B : Finset (ZMod (h * n)))
    (hstarts : ∀ p ∈ A ∪ B, residueMap h n p = 0) :
    (tileTails A B).filter (fun x => residueMap h n x = 2) =
      B.image (fun p => p - (n : ZMod (h * n)) + 2) := by
  classical
  have hminus (x : ZMod (h*n)) (hx : x ∈ (A ∪ B).image (fun p => p-1)) :
      residueMap h n x = -1 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simp [map_sub, hstarts p hp]
  have hzeroA (x : ZMod (h*n)) (hx : x ∈ A.image (fun p => p-(n : ZMod (h*n)))) :
      residueMap h n x = 0 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simp [map_sub, hstarts p (Finset.mem_union_left B hp)]
  have hzeroB (x : ZMod (h*n)) (hx : x ∈ B.image (fun p => p-2*(n : ZMod (h*n)))) :
      residueMap h n x = 0 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simp [map_sub, map_mul, hstarts p (Finset.mem_union_right A hp)]
  have htwo (x : ZMod (h*n)) (hx : x ∈ B.image (fun p => p-(n : ZMod (h*n))+2)) :
      residueMap h n x = 2 := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
    simp [map_sub, map_add, hstarts p (Finset.mem_union_right A hp), res_two]
  ext x
  constructor
  · intro hx
    obtain ⟨hx, hres⟩ := Finset.mem_filter.mp hx
    simp only [tileTails, Finset.mem_union] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · exact False.elim ((residues_distinct hn).1 ((hminus x hx).symm.trans hres))
    · exact False.elim ((residues_distinct hn).2 ((hzeroA x hx).symm.trans hres))
    · exact False.elim ((residues_distinct hn).2 ((hzeroB x hx).symm.trans hres))
    · exact hx
  · intro hx
    apply Finset.mem_filter.mpr
    refine ⟨?_, htwo x hx⟩
    exact Finset.mem_union_right _ hx

theorem tileTails_residue_set
    (A B : Finset (ZMod (h * n))) (hB : B.Nonempty)
    (hstarts : ∀ p ∈ A ∪ B, residueMap h n p = 0) :
    (tileTails A B).image (residueMap h n) = residues n := by
  classical
  have hminus (p : ZMod (h*n)) (hp : p ∈ A ∪ B) :
      residueMap h n (p-1) = -1 := by simp [map_sub, hstarts p hp]
  have hzero (p : ZMod (h*n)) (hp : p ∈ A ∪ B) :
      residueMap h n (p-(n : ZMod (h*n))) = 0 := by
    simp [map_sub, hstarts p hp]
  have hzero2 (p : ZMod (h*n)) (hp : p ∈ A ∪ B) :
      residueMap h n (p-2*(n : ZMod (h*n))) = 0 := by
    simp [map_sub, map_mul, hstarts p hp]
  have htwo (p : ZMod (h*n)) (hp : p ∈ A ∪ B) :
      residueMap h n (p-(n : ZMod (h*n))+2) = 2 := by
    simp [map_sub, map_add, hstarts p hp, res_two]
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
    simp only [tileTails, Finset.mem_union] at hx
    rcases hx with ((hx | hx) | hx) | hx
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [hminus p hp]; simp [residues]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [hzero p (Finset.mem_union_left B hp)]; simp [residues]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [hzero2 p (Finset.mem_union_right A hp)]; simp [residues]
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      rw [htwo p (Finset.mem_union_right A hp)]; simp [residues]
  · intro hy
    obtain ⟨p, hp⟩ := hB
    have hpAB : p ∈ A ∪ B := Finset.mem_union_right A hp
    rcases (mem_residues y).mp hy with he | he | he
    · refine Finset.mem_image.mpr ⟨p-1, ?_, (hminus p hpAB).trans he.symm⟩
      exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hpAB)))
    · refine Finset.mem_image.mpr ⟨p-2*(n : ZMod (h*n)), ?_, (hzero2 p hpAB).trans he.symm⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))
    · refine Finset.mem_image.mpr ⟨p-(n : ZMod (h*n))+2, ?_, (htwo p hpAB).trans he.symm⟩
      exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp)

/-- One three-tile has a unique residue-2 tail, calculated from the
literal three-tile formula. -/
theorem one_three_tile_marker (hn : 7 ≤ n)
    (A : Finset (ZMod (h * n))) (p : ZMod (h * n))
    (hstarts : ∀ x ∈ A ∪ {p}, residueMap h n x = 0) :
    let T := tileTails A {p}
    let anchor := p - (n : ZMod (h * n)) + 2
    T.image (residueMap h n) = residues n ∧
    anchor ∈ T ∧ residueMap h n anchor = 2 ∧
    ∀ x ∈ T, residueMap h n x = 2 → x = anchor := by
  dsimp only
  let T := tileTails A {p}
  let anchor := p - (n : ZMod (h * n)) + 2
  have hm : T.filter (fun x => residueMap h n x = 2) = {anchor} := by
    dsimp [T, anchor]
    rw [tileTails_residue_two hn A {p} hstarts]
    simp
  have ha : anchor ∈ T.filter (fun x => residueMap h n x = 2) := by rw [hm]; simp
  refine ⟨tileTails_residue_set A {p} (by simp) hstarts,
    (Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp ha).2, ?_⟩
  intro x hx hx2
  have hx' : x ∈ T.filter (fun x => residueMap h n x = 2) := Finset.mem_filter.mpr ⟨hx, hx2⟩
  rw [hm] at hx'
  simpa using hx'

/-- Two consecutive three-tiles have residue-2 tails exactly three
phases apart. -/
theorem two_three_tile_marker (hn : 7 ≤ n)
    (A : Finset (ZMod (h * n))) (p : ZMod (h * n))
    (hstarts : ∀ x ∈ A ∪ {p, p - 3 * (n : ZMod (h * n))},
      residueMap h n x = 0) :
    let B := ({p, p - 3 * (n : ZMod (h * n))} : Finset (ZMod (h * n)))
    let T := tileTails A B
    let anchor := p - 3 * (n : ZMod (h * n)) - (n : ZMod (h * n)) + 2
    T.image (residueMap h n) = residues n ∧
    T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3 * n : ℕ) : ZMod (h * n))} := by
  dsimp only
  let B : Finset (ZMod (h*n)) := {p, p - 3 * (n : ZMod (h*n))}
  let T := tileTails A B
  let anchor := p - 3 * (n : ZMod (h*n)) - (n : ZMod (h*n)) + 2
  have hs : p - (n : ZMod (h*n)) + 2 = anchor + ((3*n : ℕ) : ZMod (h*n)) := by
    dsimp [anchor]
    push_cast
    ring
  refine ⟨tileTails_residue_set A B (by simp [B]) hstarts, ?_⟩
  rw [tileTails_residue_two hn A B hstarts]
  simp only [B, Finset.image_insert, Finset.image_singleton]
  rw [hs]
  change ({anchor + ((3*n : ℕ) : ZMod (h*n)), anchor} : Finset (ZMod (h*n))) =
    {anchor, anchor + ((3*n : ℕ) : ZMod (h*n))}
  ext x
  simp only [Finset.mem_insert, Finset.mem_singleton]
  exact or_comm

end CorralLatinTailMarker
