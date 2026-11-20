import CorralFormalization.CorralRows

/-!
# Latin reassignment and physical-row decoding

The finite reassignment, row-palette, fixed-skeleton partition and absolute
unlabelled decoder results are independent of endpoint completion.  They do
not assert the existence of the required terrace, a cyclic gap decomposition
for its modified rows, asymmetry, a dihedral-orbit count, or Theorem 10.
-/

namespace CorralFormalization.LatinTransfer

open scoped BigOperators

structure LatinSquare (r : ℕ) where
  entry : Fin r → Fin r → Fin r
  row_bijective : ∀ j, Function.Bijective (entry j)
  column_bijective : ∀ u, Function.Bijective (fun j => entry j u)

@[ext] theorem LatinSquare.ext {r : ℕ} {S T : LatinSquare r}
    (h : ∀ j u, S.entry j u = T.entry j u) : S = T := by
  cases S
  cases T
  congr
  funext j u
  exact h j u

abbrev Family (h r : ℕ) := ZMod h → LatinSquare r

/-- Left coordinates are `(copy, Latin row, Latin column)`; right
coordinates are `(copy, Latin column, symbol)`. -/
def reassign {h r : ℕ} (L : Family h r) :
    ZMod h × Fin r × Fin r → ZMod h × Fin r × Fin r :=
  fun c => (c.1, c.2.2, (L c.1).entry c.2.1 c.2.2)

theorem reassign_bijective {h r : ℕ} (L : Family h r) :
    Function.Bijective (reassign L) := by
  constructor
  · rintro ⟨a, j, u⟩ ⟨b, k, v⟩ he
    have hab : a = b := congrArg Prod.fst he
    have huv : u = v := congrArg (fun c => c.2.1) he
    subst b
    subst v
    have hjk := (L a).column_bijective u |>.1 (congrArg (fun c => c.2.2) he)
    change j = k at hjk
    subst k
    rfl
  · rintro ⟨a, u, s⟩
    obtain ⟨j, hj⟩ := (L a).column_bijective u |>.2 s
    exact ⟨(a, j, u), by simp [reassign, hj]⟩

/-- Reparameterize a cell in physical row `q` by its copy `a=q+offset j`.
The earlier connector construction uses `offset j = 2*r*j` in `ZMod h`. -/
def rephase {h r : ℕ} (offset : Fin r → ZMod h) :
    (ZMod h × Fin r × Fin r) ≃ (ZMod h × Fin r × Fin r) where
  toFun c := (c.1 + offset c.2.1, c.2.1, c.2.2)
  invFun c := (c.1 - offset c.2.1, c.2.1, c.2.2)
  left_inv := by rintro ⟨q, j, u⟩; simp
  right_inv := by rintro ⟨a, j, u⟩; simp

def assign {h r : ℕ} (L : Family h r) (offset : Fin r → ZMod h) :
    ZMod h × Fin r × Fin r → ZMod h × Fin r × Fin r :=
  reassign L ∘ rephase offset

theorem assign_bijective {h r : ℕ} (L : Family h r)
    (offset : Fin r → ZMod h) : Function.Bijective (assign L offset) :=
  (reassign_bijective L).comp (rephase offset).bijective

section FiniteRows

variable {h r : ℕ} {X : Type*} [DecidableEq X]

/-- The actual selected point, indexed by physical row, Latin row and column. -/
def selected (Y : ZMod h × Fin r × Fin r → X)
    (L : Family h r) (offset : Fin r → ZMod h)
    (c : ZMod h × Fin r × Fin r) : X := Y (assign L offset c)

omit [DecidableEq X] in
theorem selected_injective (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (L : Family h r)
    (offset : Fin r → ZMod h) : Function.Injective (selected Y L offset) :=
  hY.comp (assign_bijective L offset).1

omit [DecidableEq X] in
/-- Each `(copy,column,symbol)` site is assigned by exactly one physical cell.
This is an exact-once statement, stronger than equality of the occupied sets. -/
theorem selected_exactly_once (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (L : Family h r)
    (offset : Fin r → ZMod h) (t : ZMod h × Fin r × Fin r) :
    ∃! c, selected Y L offset c = Y t := by
  obtain ⟨c, hc⟩ := (assign_bijective L offset).2 t
  refine ⟨c, congrArg Y hc, ?_⟩
  intro d hd
  exact selected_injective Y hY L offset (hd.trans (congrArg Y hc).symm)

def movingRow (Y : ZMod h × Fin r × Fin r → X)
    (L : Family h r) (offset : Fin r → ZMod h) (q : ZMod h) : Finset X :=
  Finset.univ.image (fun p : Fin r × Fin r => selected Y L offset (q, p))

theorem mem_movingRow (Y : ZMod h × Fin r × Fin r → X)
    (L : Family h r) (offset : Fin r → ZMod h) (q : ZMod h) (x : X) :
    x ∈ movingRow Y L offset q ↔
      ∃ j u, Y (q + offset j, u, (L (q + offset j)).entry j u) = x := by
  simp [movingRow, selected, assign, reassign, rephase]

theorem movingRows_disjoint (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (L : Family h r)
    (offset : Fin r → ZMod h) {q t : ZMod h} (hqt : q ≠ t) :
    Disjoint (movingRow Y L offset q) (movingRow Y L offset t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  obtain ⟨p, _, hp⟩ := Finset.mem_image.mp hx
  obtain ⟨v, _, hv⟩ := Finset.mem_image.mp ht
  exact hqt (congrArg Prod.fst
    (selected_injective Y hY L offset (hp.trans hv.symm)))

theorem movingRow_card (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (L : Family h r)
    (offset : Fin r → ZMod h) (q : ZMod h) :
    (movingRow Y L offset q).card = r * r := by
  rw [movingRow, Finset.card_image_of_injective]
  · simp
  · intro p v he
    exact congrArg Prod.snd (selected_injective Y hY L offset he)

theorem movingRows_cover (Y : ZMod h × Fin r × Fin r → X)
    (L : Family h r) (offset : Fin r → ZMod h) (x : X) :
    (∃ q, x ∈ movingRow Y L offset q) ↔ ∃ t, Y t = x := by
  constructor
  · rintro ⟨q, hx⟩
    obtain ⟨j, u, he⟩ := (mem_movingRow Y L offset q x).mp hx
    exact ⟨_, he⟩
  · rintro ⟨t, rfl⟩
    obtain ⟨⟨q, j, u⟩, he⟩ := (assign_bijective L offset).2 t
    refine ⟨q, Finset.mem_image.mpr ⟨(j, u), Finset.mem_univ _, ?_⟩⟩
    exact congrArg Y he

/-- The offset injectivity needed by the decoder is separate from the
column bijection needed by occupancy. -/
theorem decode_movingRow (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (L : Family h r)
    (offset : Fin r → ZMod h) (hoffset : Function.Injective offset)
    (a : ZMod h) (j u s : Fin r) :
    Y (a, u, s) ∈ movingRow Y L offset (a - offset j) ↔
      (L a).entry j u = s := by
  rw [mem_movingRow]
  constructor
  · rintro ⟨k, v, he⟩
    have hc := hY he
    have ha : a - offset j + offset k = a := congrArg Prod.fst hc
    have hoff : offset k = offset j := by linear_combination ha
    have hkj := hoffset hoff
    have hvu : v = u := congrArg (fun c => c.2.1) hc
    subst k
    subst v
    simpa using congrArg (fun c => c.2.2) hc
  · intro he
    exact ⟨j, u, by simp [he]⟩

/-- Only fixed, geometrically checkable skeleton properties are assumed:
disjoint fixed rows, avoidance of all selectable sites, coverage of their
complement, and one unchanged anchor in each fixed row.  No conclusion about
Latin injectivity, gaps or physical orbits is part of this structure. -/
structure FixedSkeleton (Y : ZMod h × Fin r × Fin r → X) where
  fixed : ZMod h → Finset X
  disjoint : ∀ q t, q ≠ t → Disjoint (fixed q) (fixed t)
  avoids : ∀ q c, Y c ∉ fixed q
  covers : ∀ x, (¬ ∃ c, Y c = x) → ∃ q, x ∈ fixed q
  anchor : ZMod h → X
  anchor_mem : ∀ q, anchor q ∈ fixed q

def transferredRows (Y : ZMod h × Fin r × Fin r → X)
    (F : FixedSkeleton Y) (L : Family h r)
    (offset : Fin r → ZMod h) (q : ZMod h) : Finset X :=
  F.fixed q ∪ movingRow Y L offset q

theorem transferredRows_disjoint (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (F : FixedSkeleton Y) (L : Family h r)
    (offset : Fin r → ZMod h) {q t : ZMod h} (hqt : q ≠ t) :
    Disjoint (transferredRows Y F L offset q) (transferredRows Y F L offset t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  rcases Finset.mem_union.mp hx with hxf | hxm <;>
    rcases Finset.mem_union.mp ht with htf | htm
  · exact Finset.disjoint_left.mp (F.disjoint q t hqt) hxf htf
  · obtain ⟨j, u, rfl⟩ := (mem_movingRow Y L offset t x).mp htm
    exact F.avoids q _ hxf
  · obtain ⟨j, u, rfl⟩ := (mem_movingRow Y L offset q x).mp hxm
    exact F.avoids t _ htf
  · exact Finset.disjoint_left.mp (movingRows_disjoint Y hY L offset hqt) hxm htm

theorem transferredRows_full_partition (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (F : FixedSkeleton Y) (L : Family h r)
    (offset : Fin r → ZMod h) (x : X) :
    ∃! q, x ∈ transferredRows Y F L offset q := by
  have hex : ∃ q, x ∈ transferredRows Y F L offset q := by
    by_cases hx : ∃ c, Y c = x
    · obtain ⟨q, hq⟩ := (movingRows_cover Y L offset x).mpr hx
      exact ⟨q, Finset.mem_union_right _ hq⟩
    · obtain ⟨q, hq⟩ := F.covers x hx
      exact ⟨q, Finset.mem_union_left _ hq⟩
  obtain ⟨q, hq⟩ := hex
  refine ⟨q, hq, ?_⟩
  intro t ht
  by_contra hne
  exact Finset.disjoint_left.mp (transferredRows_disjoint Y hY F L offset hne) ht hq

theorem transferredRows_nonempty (Y : ZMod h × Fin r × Fin r → X)
    (F : FixedSkeleton Y) (L : Family h r) (offset : Fin r → ZMod h)
    (q : ZMod h) : (transferredRows Y F L offset q).Nonempty :=
  ⟨F.anchor q, Finset.mem_union_left _ (F.anchor_mem q)⟩

theorem anchor_owner (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (F : FixedSkeleton Y) (L : Family h r)
    (offset : Fin r → ZMod h) (q t : ZMod h) :
    F.anchor q ∈ transferredRows Y F L offset t ↔ q = t := by
  constructor
  · intro hmem
    by_contra hne
    exact Finset.disjoint_left.mp (transferredRows_disjoint Y hY F L offset hne)
      (Finset.mem_union_left _ (F.anchor_mem q)) hmem
  · rintro rfl
    exact Finset.mem_union_left _ (F.anchor_mem q)

theorem decode_transferredRows (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (F : FixedSkeleton Y) (L : Family h r)
    (offset : Fin r → ZMod h) (hoffset : Function.Injective offset)
    (a : ZMod h) (j u s : Fin r) :
    Y (a, u, s) ∈ transferredRows Y F L offset (a - offset j) ↔
      (L a).entry j u = s := by
  simp only [transferredRows, Finset.mem_union, F.avoids, false_or]
  exact decode_movingRow Y hY L offset hoffset a j u s

/-- Absolute physical partitions forget row labels. This is an unordered
family of actual site-sets; there is no quotient by translation/reflection. -/
def unlabelledPartition [NeZero h] (Y : ZMod h × Fin r × Fin r → X)
    (F : FixedSkeleton Y) (offset : Fin r → ZMod h) (L : Family h r) :
    Finset (Finset X) := Finset.univ.image (transferredRows Y F L offset)

/-- An unchanged fixed anchor recovers each row from its unlabelled family;
offset separation then recovers every Latin entry from actual membership. -/
theorem unlabelledPartition_injective [NeZero h] (Y : ZMod h × Fin r × Fin r → X)
    (hY : Function.Injective Y) (F : FixedSkeleton Y)
    (offset : Fin r → ZMod h) (hoffset : Function.Injective offset) :
    Function.Injective (unlabelledPartition Y F offset) := by
  intro L K hpart
  have hrow (q : ZMod h) :
      transferredRows Y F L offset q = transferredRows Y F K offset q := by
    have hm : transferredRows Y F L offset q ∈ unlabelledPartition Y F offset K := by
      rw [← hpart]
      exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩
    obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hm
    have hanchor : F.anchor q ∈ transferredRows Y F K offset t := by
      rw [ht]
      exact Finset.mem_union_left _ (F.anchor_mem q)
    have hqt := (anchor_owner Y hY F K offset q t).mp hanchor
    simpa [← hqt] using ht.symm
  funext a
  apply LatinSquare.ext
  intro j u
  let s := (L a).entry j u
  have hmem : Y (a, u, s) ∈ transferredRows Y F L offset (a - offset j) :=
    (decode_transferredRows Y hY F L offset hoffset a j u s).mpr rfl
  rw [hrow] at hmem
  exact ((decode_transferredRows Y hY F K offset hoffset a j u s).mp hmem).symm

end FiniteRows

/-- Multisets retain multiplicities, including collisions between incoming
and outgoing blocks. -/
def block {r : ℕ} (f : Fin r → ℕ) : Multiset ℕ := ∑ s, ({f s} : Multiset ℕ)

def rowIncidentPalette {h r : ℕ} (L : Family h r) (offset : Fin r → ZMod h)
    (A B : Fin r → ℕ) (q : ZMod h) : Multiset ℕ :=
  ∑ j : Fin r,
    (block (fun u => A j + ((L (q + offset j)).entry j u).val) +
     block (fun u => B j - ((L (q + offset j)).entry j u).val))

def fullIncidentPalette {r : ℕ} (A B : Fin r → ℕ) : Multiset ℕ :=
  ∑ j : Fin r,
    (block (fun s : Fin r => A j + s.val) + block (fun s : Fin r => B j - s.val))

/-- Row Latin bijectivity preserves both full incident-gap blocks, for all
copies acting on one physical row simultaneously. Column conditions are
unused by this separate palette argument. -/
theorem rowIncidentPalette_eq {h r : ℕ} (L : Family h r)
    (offset : Fin r → ZMod h) (A B : Fin r → ℕ) (q : ZMod h) :
    rowIncidentPalette L offset A B q = fullIncidentPalette A B := by
  unfold rowIncidentPalette fullIncidentPalette
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  · exact ((L (q + offset j)).row_bijective j).sum_comp
      (fun s => ({A j + s.val} : Multiset ℕ))
  · exact ((L (q + offset j)).row_bijective j).sum_comp
      (fun s => ({B j - s.val} : Multiset ℕ))

/-- A supplied unchanged-edge multiset can be added without losing the
palette result; no assertion that these are all actual cyclic edges is made. -/
theorem completedPalette_eq {h r : ℕ} (L : Family h r)
    (offset : Fin r → ZMod h) (A B : Fin r → ℕ) (q : ZMod h)
    (unchanged : Multiset ℕ) :
    unchanged + rowIncidentPalette L offset A B q =
      unchanged + fullIncidentPalette A B := by
  rw [rowIncidentPalette_eq]

/-! ## Literal phase and selectable-site geometry from (connectorPrefixCenterSite) -/

def phaseOffset (h r : ℕ) (j : Fin r) : ZMod h := ((2 * r) * j.val : ℕ)

theorem phaseOffset_injective {h r : ℕ} (hr : 0 < r)
    (hh : 2 * r * r ≤ h) : Function.Injective (phaseOffset h r) := by
  intro j k he
  have hfactor : 0 < 2 * r := by omega
  have hj : (2 * r) * j.val < h :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left j.isLt hfactor) hh
  have hk : (2 * r) * k.val < h :=
    lt_of_lt_of_le (Nat.mul_lt_mul_of_pos_left k.isLt hfactor) hh
  have hv := congrArg ZMod.val he
  change (((2 * r) * j.val : ℕ) : ZMod h).val =
    (((2 * r) * k.val : ℕ) : ZMod h).val at hv
  rw [ZMod.val_natCast_of_lt hj, ZMod.val_natCast_of_lt hk] at hv
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hfactor hv)

def centerResidue {r : ℕ} (u s : Fin r) : ℕ :=
  20 * r * r + (r + 1) * u.val + s.val

theorem centerResidue_lt {r n : ℕ} (hn : 21 * r * r + 2 * r ≤ n)
    (u s : Fin r) : centerResidue u s < n := by
  have hu := Nat.mul_lt_mul_of_pos_left u.isLt (by omega : 0 < r + 1)
  have hs := s.isLt
  dsimp [centerResidue]
  nlinarith

def centerPhase {h r : ℕ} (a : ZMod h) (u : Fin r) : ZMod h :=
  a + ((2 + 2 * u.val : ℕ) : ZMod h)

/-- The representative phase can be reduced modulo `h` before multiplication
by `n`, because the physical clock is `h*n`. Thus this is exactly connectorPrefixCenterSite:
`x_u+s+(a+2+2u)*n (mod h*n)`, with `x_u=20*r^2+(r+1)u`. -/
def connectorPrefixCenterSite (h n r : ℕ) (c : ZMod h × Fin r × Fin r) : ZMod (h * n) :=
  ((centerResidue c.2.1 c.2.2 + (centerPhase c.1 c.2.1).val * n : ℕ) : ZMod (h * n))

theorem connectorPrefixCenterSite_eq_unreduced {h n r : ℕ} [NeZero h]
    (a : ZMod h) (u s : Fin r) :
    connectorPrefixCenterSite h n r (a, u, s) =
      ((centerResidue u s + (a.val + (2 + 2 * u.val)) * n : ℕ) : ZMod (h * n)) := by
  have hcast : ((a.val + (2 + 2 * u.val) : ℕ) : ZMod h) = centerPhase a u := by
    simp [centerPhase]
  have hp := congrArg ZMod.val hcast
  rw [ZMod.val_natCast] at hp
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mpr
  change centerResidue u s + (centerPhase a u).val * n ≡
    centerResidue u s + (a.val + (2 + 2 * u.val)) * n [MOD h * n]
  rw [← hp]
  exact ((Nat.mod_modEq _ h).mul_right' n).add_left _

theorem connectorPrefixCenterSite_val {h n r : ℕ} [NeZero h]
    (hn : 21 * r * r + 2 * r ≤ n) (c : ZMod h × Fin r × Fin r) :
    (connectorPrefixCenterSite h n r c).val = centerResidue c.2.1 c.2.2 +
      (centerPhase c.1 c.2.1).val * n := by
  apply ZMod.val_natCast_of_lt
  have hr := centerResidue_lt hn c.2.1 c.2.2
  have hp := (centerPhase c.1 c.2.1).val_lt
  nlinarith

/-- All selectable physical sites for distinct `(a,u,s)` are distinct.
The numerical assumption is weaker than the connector-prefix bound `n≥100*r^2`. -/
theorem connectorPrefixCenterSite_injective {h n r : ℕ} [NeZero h]
    (hn : 21 * r * r + 2 * r ≤ n) : Function.Injective (connectorPrefixCenterSite h n r) := by
  rintro ⟨a, u, s⟩ ⟨b, v, t⟩ he
  have hu := centerResidue_lt hn u s
  have hv := centerResidue_lt hn v t
  have hnpos : 0 < n := by omega
  have heval := congrArg ZMod.val he
  rw [connectorPrefixCenterSite_val hn, connectorPrefixCenterSite_val hn] at heval
  have hres := congrArg (fun x => x % n) heval
  simp only [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hu,
    Nat.mod_eq_of_lt hv] at hres
  have hdigit : (r + 1) * u.val + s.val = (r + 1) * v.val + t.val := by
    dsimp [centerResidue] at hres
    omega
  have hudiv := congrArg (fun x => x / (r + 1)) hdigit
  rw [Nat.mul_add_div (by omega), Nat.mul_add_div (by omega),
    Nat.div_eq_of_lt (by omega : s.val < r + 1),
    Nat.div_eq_of_lt (by omega : t.val < r + 1)] at hudiv
  have huv : u = v := Fin.ext (by simpa using hudiv)
  subst v
  have hst : s = t := Fin.ext (by omega)
  subst t
  have hmul : n * (centerPhase a u).val = n * (centerPhase b u).val := by
    nlinarith [heval]
  have hpval := Nat.eq_of_mul_eq_mul_left hnpos hmul
  have hp := ZMod.val_injective h hpval
  have hab : a = b := add_right_cancel hp
  subst b
  rfl

theorem connectorPrefix_numeric_bounds {h n r : ℕ} (hr : 2 ≤ r)
    (hn : n = 2 * h - 1) (hlarge : 100 * r * r ≤ n) :
    21 * r * r + 2 * r ≤ n ∧ 2 * r * r ≤ h := by
  have hsq : r ≤ r * r := by nlinarith [Nat.mul_le_mul_left r (by omega : 1 ≤ r)]
  have hupper : n ≤ 2 * h := by omega
  constructor <;> nlinarith

theorem optimal_width {h n : ℕ} (hh : 0 < h) (hn : n = 2 * h - 1) :
    width n = h * n := by
  have hs : n + 1 = 2 * h := by omega
  have hw := width_mul_two n
  rw [hs] at hw
  nlinarith

/-- A direct physical specialization of the unlabelled decoder, with exactly
the connector-prefix selectable sites and phase offsets.  Its fixed-skeleton
premise concerns the unchanged terrace sites, not the Latin map. -/
theorem connectorPrefixCenterSite_unlabelledPartition_injective {h n r : ℕ} [NeZero h]
    (hr : 0 < r) (hn : 21 * r * r + 2 * r ≤ n) (hh : 2 * r * r ≤ h)
    (F : FixedSkeleton (connectorPrefixCenterSite h n r)) :
    Function.Injective (unlabelledPartition (connectorPrefixCenterSite h n r) F (phaseOffset h r)) :=
  unlabelledPartition_injective (connectorPrefixCenterSite h n r) (connectorPrefixCenterSite_injective hn) F
    (phaseOffset h r) (phaseOffset_injective hr hh)

theorem connectorPrefix_unlabelledPartition_injective {h n r : ℕ} [NeZero h]
    (hr : 2 ≤ r) (hn : n = 2 * h - 1) (hlarge : 100 * r * r ≤ n)
    (F : FixedSkeleton (connectorPrefixCenterSite h n r)) :
    Function.Injective (unlabelledPartition (connectorPrefixCenterSite h n r) F (phaseOffset h r)) := by
  obtain ⟨hres, hphase⟩ := connectorPrefix_numeric_bounds hr hn hlarge
  exact connectorPrefixCenterSite_unlabelledPartition_injective (by omega) hres hphase F

def incomingBase {r : ℕ} (j : Fin r) : ℕ := 10 * r * r + r * j.val
def outgoingBase {r : ℕ} (j : Fin r) : ℕ := 50 * r * r + r * j.val
def centerBase {r : ℕ} (u : Fin r) : ℕ := 20 * r * r + (r + 1) * u.val
def predecessor {r : ℕ} (j u : Fin r) : ℕ := centerBase u - incomingBase j
def successor {r : ℕ} (j u : Fin r) : ℕ := centerBase u + outgoingBase j

/-- The displayed integer-lift triples have the claimed positive forward
distances, each below n. This is a local geometry theorem; it does not assume
or prove that these are consecutive in an entire modified cyclic row. -/
theorem local_gap_geometry {r n : ℕ} (hr : 2 ≤ r) (hn : 100 * r * r ≤ n)
    (j u s : Fin r) :
    predecessor j u < centerBase u + s.val ∧
    centerBase u + s.val < successor j u ∧
    centerBase u + s.val - predecessor j u = incomingBase j + s.val ∧
    successor j u - (centerBase u + s.val) = outgoingBase j - s.val ∧
    0 < incomingBase j + s.val ∧ incomingBase j + s.val < n ∧
    0 < outgoingBase j - s.val ∧ outgoingBase j - s.val < n := by
  have hsq : r ≤ r * r := by nlinarith [Nat.mul_le_mul_left r (by omega : 1 ≤ r)]
  have hj := Nat.mul_le_mul_left r (Nat.le_of_lt j.isLt)
  have hs := s.isLt
  have ha : incomingBase j ≤ centerBase u := by
    dsimp [incomingBase, centerBase]
    nlinarith
  have hb : s.val < outgoingBase j := by
    dsimp [outgoingBase]
    nlinarith
  have hinpos : 0 < incomingBase j + s.val := by
    dsimp [incomingBase]
    nlinarith
  have hinlt : incomingBase j + s.val < n := by
    dsimp [incomingBase]
    nlinarith
  have hblt : outgoingBase j < n := by
    dsimp [outgoingBase]
    nlinarith
  dsimp [predecessor, successor]
  omega

/-- The incoming and outgoing blocks, now as multisets of the local positive
gaps just checked by `local_gap_geometry`. -/
theorem connectorPrefix_incidentPalette_eq {h r : ℕ} (L : Family h r) (q : ZMod h) :
    rowIncidentPalette L (phaseOffset h r) incomingBase outgoingBase q =
      fullIncidentPalette (r := r) incomingBase outgoingBase :=
  rowIncidentPalette_eq L (phaseOffset h r) incomingBase outgoingBase q

/-! ## Representation bridge and the explicit missing edge certificate -/

section NaturalRepresentatives

variable {h n r : ℕ} [NeZero h] [NeZero (h * n)]

/-- The existing `CorralRows` interface indexes rows by `Fin h` and uses
bounded natural representatives. The physical row sets themselves live in
`ZMod (h*n)`. -/
def naturalRows (R : ZMod h → Finset (ZMod (h * n))) (q : Fin h) : Finset ℕ :=
  (R (q.val : ZMod h)).image ZMod.val

omit [NeZero h] in
theorem naturalRows_bounded (R : ZMod h → Finset (ZMod (h * n)))
    (q : Fin h) (x : ℕ) (hx : x ∈ naturalRows R q) : x < h * n := by
  obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
  exact y.val_lt

omit [NeZero h] in
theorem mem_naturalRows (R : ZMod h → Finset (ZMod (h * n)))
    (q : Fin h) (x : ℕ) (hx : x < h * n) :
    x ∈ naturalRows R q ↔ (x : ZMod (h * n)) ∈ R (q.val : ZMod h) := by
  constructor
  · intro hm
    obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hm
    rw [← he, ZMod.natCast_zmod_val]
    exact hy
  · intro hm
    exact Finset.mem_image.mpr ⟨(x : ZMod (h * n)), hm, ZMod.val_natCast_of_lt hx⟩

theorem naturalRows_full_partition (R : ZMod h → Finset (ZMod (h * n)))
    (hpart : ∀ x, ∃! q, x ∈ R q) (x : ℕ) (hx : x < h * n) :
    ∃! q : Fin h, x ∈ naturalRows R q := by
  obtain ⟨q, hq, huniq⟩ := hpart (x : ZMod (h * n))
  let f : Fin h := ⟨q.val, q.val_lt⟩
  have hf : (f.val : ZMod h) = q := ZMod.natCast_zmod_val q
  refine ⟨f, (mem_naturalRows R f x hx).mpr (by rw [hf]; exact hq), ?_⟩
  intro t ht
  have htz := huniq (t.val : ZMod h) ((mem_naturalRows R t x hx).mp ht)
  have hval := congrArg ZMod.val htz
  rw [ZMod.val_natCast_of_lt t.isLt] at hval
  exact Fin.ext hval

theorem naturalRows_disjoint (R : ZMod h → Finset (ZMod (h * n)))
    (hpart : ∀ x, ∃! q, x ∈ R q) (q t : Fin h) (hqt : q ≠ t) :
    Disjoint (naturalRows R q) (naturalRows R t) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  have hbound := naturalRows_bounded R q x hx
  obtain ⟨owner, _, huniq⟩ := naturalRows_full_partition R hpart x hbound
  exact hqt ((huniq q hx).trans (huniq t ht).symm)

/-- This certificate isolates the remaining cyclic-order obligation. Its
first field says exactly which edge inventory consists of the unchanged
edges plus the local Latin pairs; its second field says the baseline total
is the full palette. Neither is inferred merely from site occupancy. -/
structure CyclicEdgeCertificate
    (Y : ZMod h × Fin r × Fin r → ZMod (h * n)) (F : FixedSkeleton Y)
    (L : Family h r) (offset : Fin r → ZMod h) (A B : Fin r → ℕ) where
  unchanged : ZMod h → Multiset ℕ
  decomposition : ∀ q : Fin h,
    finiteCyclicGapInventory (h * n) (naturalRows (transferredRows Y F L offset) q) =
      unchanged (q.val : ZMod h) + rowIncidentPalette L offset A B (q.val : ZMod h)
  baseline : ∀ q : ZMod h,
    unchanged q + fullIncidentPalette A B = Multiset.ofList (fullGapList n)

/-- A conditional adapter to the maintained interface. The actual cyclic
edge certificate is explicit input, not a proved property of connectorPrefixCenterSite here. -/
def toCorralRows
    (Y : ZMod h × Fin r × Fin r → ZMod (h * n)) (hY : Function.Injective Y)
    (F : FixedSkeleton Y) (L : Family h r) (offset : Fin r → ZMod h)
    (A B : Fin r → ℕ) (hwidth : width n = h * n)
    (E : CyclicEdgeCertificate Y F L offset A B) : CorralRows h n where
  sites := naturalRows (transferredRows Y F L offset)
  nonempty := by
    intro q
    exact (transferredRows_nonempty Y F L offset (q.val : ZMod h)).image _
  bounded := by
    intro q x hx
    rw [hwidth]
    exact naturalRows_bounded _ q x hx
  disjoint := naturalRows_disjoint _ (transferredRows_full_partition Y hY F L offset)
  gaps := by
    intro q
    rw [hwidth, E.decomposition, rowIncidentPalette_eq, E.baseline]

/-- Full occupancy is retained by the bounded-natural adapter, in addition
to the four fields required by `CorralRows`. -/
theorem toCorralRows_full_occupancy
    (Y : ZMod h × Fin r × Fin r → ZMod (h * n)) (hY : Function.Injective Y)
    (F : FixedSkeleton Y) (L : Family h r) (offset : Fin r → ZMod h)
    (A B : Fin r → ℕ) (hwidth : width n = h * n)
    (E : CyclicEdgeCertificate Y F L offset A B) (x : ℕ) (hx : x < width n) :
    ∃! q, x ∈ (toCorralRows Y hY F L offset A B hwidth E).sites q := by
  apply naturalRows_full_partition _ (transferredRows_full_partition Y hY F L offset)
  simpa [hwidth] using hx

end NaturalRepresentatives

end CorralFormalization.LatinTransfer
