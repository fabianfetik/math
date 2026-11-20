import CorralFormalization.DiversityCompletion.TileGapWords

namespace CorralFormalization.LatinCompletion.TerraceLift

open LatinTransfer

def residueMap (h n : ℕ) : ZMod (h*n) →+* ZMod n :=
  ZMod.castHom (Nat.dvd_mul_left n h) (ZMod n)

def zeroSite (h n : ℕ) (q : ZMod h) : ZMod (h*n) := ((q.val*n : ℕ) : ZMod (h*n))

theorem residueMap_val {h n : ℕ} [NeZero (h*n)] (x : ZMod (h*n)) :
    residueMap h n x = (x.val : ZMod n) := by
  calc
    residueMap h n x = residueMap h n ((x.val : ℕ) : ZMod (h*n)) :=
      congrArg (residueMap h n) (ZMod.natCast_zmod_val x).symm
    _ = (x.val : ZMod n) := by rw [map_natCast]

theorem zeroSite_residue (h n : ℕ) (q : ZMod h) :
    residueMap h n (zeroSite h n q) = 0 := by
  simp [zeroSite, map_natCast, Nat.cast_mul]

theorem zeroSite_injective {h n : ℕ} [NeZero h] (hn : 0 < n) :
    Function.Injective (zeroSite h n) := by
  intro q t he
  have hq : q.val*n < h*n := Nat.mul_lt_mul_of_pos_right q.val_lt hn
  have ht : t.val*n < h*n := Nat.mul_lt_mul_of_pos_right t.val_lt hn
  have hv := congrArg ZMod.val he
  change ((q.val*n : ℕ) : ZMod (h*n)).val = ((t.val*n : ℕ) : ZMod (h*n)).val at hv
  rw [ZMod.val_natCast_of_lt hq, ZMod.val_natCast_of_lt ht] at hv
  apply ZMod.val_injective h
  exact Nat.eq_of_mul_eq_mul_left hn (by simpa [Nat.mul_comm] using hv)

theorem zeroSite_natCast (h n k : ℕ) :
    zeroSite h n (k : ZMod h) = ((k*n : ℕ) : ZMod (h*n)) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  rw [ZMod.val_natCast]
  exact (Nat.mod_modEq k h).mul_right' n

theorem zeroSite_add {h n : ℕ} [NeZero h] (q t : ZMod h) :
    zeroSite h n (q+t) = zeroSite h n q + zeroSite h n t := by
  have hrep : ((q.val+t.val : ℕ) : ZMod h) = q+t := by simp
  rw [← hrep, zeroSite_natCast]
  simp [zeroSite, Nat.cast_add, Nat.add_mul]

theorem zeroSite_pred {h n : ℕ} [NeZero h] (q : ZMod h) :
    zeroSite h n (q-1) = zeroSite h n q - (n : ZMod (h*n)) := by
  have hp := zeroSite_add (n := n) (q-1) (1 : ZMod h)
  have h1 : zeroSite h n (1 : ZMod h) = (n : ZMod (h*n)) := by
    simpa using zeroSite_natCast h n 1
  rw [sub_add_cancel, h1] at hp
  linear_combination -hp

/-- The physical zero residue column is exactly the h phase sites, with
unique ownership. This is proved from natural quotient/remainder. -/
theorem zeroSite_exactly_once {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
    (x : ZMod (h*n)) : residueMap h n x = 0 ↔ ∃! q, zeroSite h n q = x := by
  constructor
  · intro hx
    have hmod : x.val % n = 0 := by
      have hv := congrArg ZMod.val hx
      rw [residueMap_val, ZMod.val_natCast, ZMod.val_zero] at hv
      exact hv
    have hquot : x.val / n < h :=
      (Nat.div_lt_iff_lt_mul (NeZero.pos n)).mpr (by simpa [Nat.mul_comm] using x.val_lt)
    let q : ZMod h := ((x.val/n : ℕ) : ZMod h)
    have hrep : q.val*n = x.val := by
      rw [show q.val = x.val/n from ZMod.val_natCast_of_lt hquot]
      have hm := Nat.mod_add_div x.val n
      nlinarith
    have hq : zeroSite h n q = x := by
      unfold zeroSite
      rw [hrep, ZMod.natCast_zmod_val]
    exact ⟨q, hq, fun t ht => zeroSite_injective (NeZero.pos n) (ht.trans hq.symm)⟩
  · rintro ⟨q, hq, _⟩
    rw [← hq]
    exact zeroSite_residue h n q

/-- Genuine completed residue-terrace input. The supplied nonzero vertex
ordering is a bijection, and its values are the actual partial sums of the
supplied full difference calendar. This is not a physical-partition input
and makes no assertion about Corrals, tiles or a Latin frame. Existence from
endpoint completion is deliberately not claimed. -/
structure CompletedTerrace (n : ℕ) where
  body : List ℕ
  differences : (TileGapWords.cycle n body).Perm (fullGapList (n-1))
  vertices : Fin (n-1) ≃ {x : ZMod n // x ≠ 0}
  vertex_at : ∀ t : Fin (n-1), (vertices t).val =
    ((n-1 + ((TileGapWords.cycle n body).take t.val).sum : ℕ) : ZMod n)

namespace CompletedTerrace

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

def base (T : CompletedTerrace n) (t : Fin (n-1)) : ℕ :=
  n-1 + ((TileGapWords.cycle n T.body).take t.val).sum

/-- All actual nonzero sites in one round of phase q, in positive-lift
coordinates. The source index t records its genuine residue-terrace vertex. -/
def site (T : CompletedTerrace n) (c : ZMod h × Fin (n-1)) : ZMod (h*n) :=
  ((c.1.val*n + T.base c.2 : ℕ) : ZMod (h*n))

theorem site_residue (T : CompletedTerrace n) (q : ZMod h) (t : Fin (n-1)) :
    residueMap h n (T.site (q,t)) = (T.vertices t).val := by
  change residueMap h n (((q.val*n+T.base t : ℕ) : ZMod (h*n))) = _
  rw [map_natCast, T.vertex_at]
  change ((q.val*n+T.base t : ℕ) : ZMod n) = (T.base t : ZMod n)
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, mul_zero, zero_add]

theorem site_injective (T : CompletedTerrace n) : Function.Injective (T.site (h := h)) := by
  rintro ⟨q,t⟩ ⟨p,u⟩ he
  have hv : (T.vertices t).val = (T.vertices u).val := by
    simpa only [T.site_residue] using congrArg (residueMap h n) he
  have htu : t = u := T.vertices.injective (Subtype.ext hv)
  subst u
  simp only [site, Nat.cast_add] at he
  have hz : zeroSite h n q = zeroSite h n p := add_right_cancel he
  have hqp := zeroSite_injective (NeZero.pos n) hz
  subst p
  rfl

theorem site_exists (T : CompletedTerrace n) (x : ZMod (h*n))
    (hx : residueMap h n x ≠ 0) : ∃ c, T.site (h := h) c = x := by
  let t := T.vertices.symm ⟨residueMap h n x, hx⟩
  have ht : (T.vertices t).val = residueMap h n x :=
    congrArg Subtype.val (T.vertices.apply_symm_apply _)
  have hb : residueMap h n ((T.base t : ℕ) : ZMod (h*n)) = residueMap h n x := by
    rw [map_natCast]
    exact (T.vertex_at t).symm.trans ht
  have hy : residueMap h n (x - (T.base t : ZMod (h*n))) = 0 := by
    rw [map_sub, hb, sub_self]
  obtain ⟨q,hq,_⟩ := (zeroSite_exactly_once _).mp hy
  refine ⟨(q,t), ?_⟩
  change (((q.val*n + T.base t : ℕ) : ZMod (h*n))) = x
  rw [Nat.cast_add]
  change zeroSite h n q + (T.base t : ZMod (h*n)) = x
  rw [hq]
  simp

/-- The exact global physical lift partition: every site outside the zero
residue column is visited once by the complete set of terrace rounds, and
no zero-column site is visited. -/
theorem site_exactly_once (T : CompletedTerrace n) (x : ZMod (h*n)) :
    residueMap h n x ≠ 0 ↔ ∃! c, T.site (h := h) c = x := by
  constructor
  · intro hx
    obtain ⟨c,hc⟩ := T.site_exists x hx
    exact ⟨c,hc,fun d hd => T.site_injective (hd.trans hc.symm)⟩
  · rintro ⟨⟨q,t⟩,hc,_⟩
    rw [← hc, T.site_residue]
    exact (T.vertices t).property

theorem round_displacement (T : CompletedTerrace n) (hn : n = 2*h-1) :
    (((TileGapWords.cycle n T.body).sum : ℕ) : ZMod (h*n)) = -(n : ZMod (h*n)) := by
  have hf := TileGapWords.first_perm (NeZero.pos n) T.body T.differences
  have hs := (TileGapWords.word_properties hn (NeZero.pos h) _ hf).2.1
  have he : (TileGapWords.cycle n T.body).sum + n = h*n := by
    simpa [TileGapWords.first] using hs
  have hc := congrArg (fun k : ℕ => (k : ZMod (h*n))) he
  simp only [Nat.cast_add, ZMod.natCast_self] at hc
  linear_combination hc

theorem phase_pred (T : CompletedTerrace n) (q : ZMod h) (t : Fin (n-1)) :
    T.site (q-1,t) = T.site (q,t) - (n : ZMod (h*n)) := by
  have hz := zeroSite_pred (n := n) q
  simp only [site, Nat.cast_add]
  change zeroSite h n (q-1) + (T.base t : ZMod (h*n)) =
    zeroSite h n q + (T.base t : ZMod (h*n)) - (n : ZMod (h*n))
  rw [hz]
  ring

/-- One actual complete difference-calendar round advances to phase q-1,
which is why the h rounds cover all physical phases. -/
theorem next_round (T : CompletedTerrace n) (hn : n = 2*h-1)
    (q : ZMod h) (t : Fin (n-1)) :
    T.site (q,t) + (((TileGapWords.cycle n T.body).sum : ℕ) : ZMod (h*n)) =
      T.site (q-1,t) := by
  rw [T.round_displacement hn, T.phase_pred]
  simp only [sub_eq_add_neg]

def roundSites (T : CompletedTerrace n) (q : ZMod h) : Finset (ZMod (h*n)) :=
  Finset.univ.image (fun t : Fin (n-1) => T.site (q,t))

theorem roundSites_disjoint (T : CompletedTerrace n) {q p : ZMod h} (hqp : q ≠ p) :
    Disjoint (T.roundSites q) (T.roundSites p) := by
  apply Finset.disjoint_left.mpr
  intro x hx hp
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hx
  obtain ⟨u,_,hu⟩ := Finset.mem_image.mp hp
  exact hqp (congrArg Prod.fst (T.site_injective (ht.trans hu.symm)))

theorem roundSites_card (T : CompletedTerrace n) (q : ZMod h) :
    (T.roundSites q).card = n-1 := by
  rw [roundSites, Finset.card_image_of_injective]
  · simp
  · intro t u he
    exact congrArg Prod.snd (T.site_injective he)

theorem roundSites_full_nonzero (T : CompletedTerrace n) :
    Finset.univ.biUnion T.roundSites =
      Finset.univ.filter (fun x : ZMod (h*n) => residueMap h n x ≠ 0) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter]
  constructor
  · rintro ⟨q,hq⟩
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hq
    rw [← ht, T.site_residue]
    exact (T.vertices t).property
  · intro hx
    obtain ⟨⟨q,t⟩,hc,_⟩ := (T.site_exactly_once x).mp hx
    exact ⟨q,Finset.mem_image.mpr ⟨t,Finset.mem_univ _,hc⟩⟩

/-- The round row sets are exactly the proper-prefix sites of the supplied
actual difference calendar, at their un-reduced positive-lift starts. -/
theorem roundSites_physicalPrefixes (T : CompletedTerrace n) (q : ZMod h) :
    T.roundSites q = physicalOffsets (h*n) (q.val*n+(n-1))
      (properPrefixSites (TileGapWords.cycle n T.body)) := by
  have hlen : (TileGapWords.cycle n T.body).length = n-1 := by
    simpa [fullGapList] using T.differences.length_eq
  ext x
  constructor
  · intro hx
    obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hx
    apply Finset.mem_image.mpr
    refine ⟨((TileGapWords.cycle n T.body).take t.val).sum, ?_, ?_⟩
    · apply List.mem_toFinset.mpr
      exact (mem_properPrefixSites_iff _ _).mpr ⟨t.val, by omega, rfl⟩
    · simpa only [site, base, Nat.add_assoc] using ht
  · intro hx
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hx
    obtain ⟨k,hk,hks⟩ := (mem_properPrefixSites_iff _ _).mp (List.mem_toFinset.mp hp)
    refine Finset.mem_image.mpr ⟨⟨k,by omega⟩,Finset.mem_univ _,?_⟩
    simpa only [site, base, hks, Nat.add_assoc] using he

theorem prefix_append (g k : List ℕ) :
    properPrefixSites (g++k) = properPrefixSites g ++
      (properPrefixSites k).map (g.sum + ·) := by
  induction g with
  | nil => simp [properPrefixSites]
  | cons a g ih =>
    simp [properPrefixSites, ih, List.map_append, List.map_map,
      Function.comp_def, Nat.add_assoc]

theorem physicalOffsets_origin (origin : ZMod (h*n)) (a : ℕ)
    (ha : (a : ZMod (h*n)) = origin) (xs : List ℕ) :
    physicalOffsets (h*n) origin.val xs = physicalOffsets (h*n) a xs := by
  unfold physicalOffsets
  congr 1
  funext x
  simp only [Nat.cast_add, ZMod.natCast_zmod_val, ha]

/-- The first actual tile row consists of one complete terrace round plus
the next round's first vertex x_(n-1)=z_q-1. This proves the first concrete
link between the local TileGapWords rows and the global physical lift. -/
theorem first_tile_row_eq_round (T : CompletedTerrace n) (hn : n = 2*h-1)
    (q : ZMod h) :
    TileGapWords.row (zeroSite h n q + ((n-1 : ℕ) : ZMod (h*n)))
      (TileGapWords.first n T.body) = T.roundSites q ∪ {zeroSite h n q-1} := by
  have ho : ((q.val*n+(n-1) : ℕ) : ZMod (h*n)) =
      zeroSite h n q + ((n-1 : ℕ) : ZMod (h*n)) := by
    simp only [zeroSite, Nat.cast_add]
  rw [TileGapWords.row, physicalOffsets_origin _ _ ho, TileGapWords.first, prefix_append]
  simp only [properPrefixSites, List.map_cons, List.map_nil, Nat.add_zero]
  have happ : physicalOffsets (h*n) (q.val*n+(n-1))
      (properPrefixSites (TileGapWords.cycle n T.body) ++ [(TileGapWords.cycle n T.body).sum]) =
    physicalOffsets (h*n) (q.val*n+(n-1)) (properPrefixSites (TileGapWords.cycle n T.body)) ∪
      {((q.val*n+(n-1)+(TileGapWords.cycle n T.body).sum : ℕ) : ZMod (h*n))} := by
    ext x
    simp [physicalOffsets]
  rw [happ, ← T.roundSites_physicalPrefixes q]
  congr 2
  have hs := T.round_displacement hn
  have hsub : ((n-1 : ℕ) : ZMod (h*n)) = (n : ZMod (h*n))-1 := by
    rw [Nat.cast_sub (by have := NeZero.pos n; omega : 1 ≤ n), Nat.cast_one]
  simp only [Nat.cast_add, zeroSite, hsub]
  linear_combination hs

end CompletedTerrace

end CorralFormalization.LatinCompletion.TerraceLift
