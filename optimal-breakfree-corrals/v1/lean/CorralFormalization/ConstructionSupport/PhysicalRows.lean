import CorralFormalization.CorralRows
import CorralFormalization.Constructions.Optimal.Even.Theorem

/-!
# Physical representation and decoding for corral diversity

This file proves general facts about physical, unlabelled-row
representations. It does not assert the complete explicit-family theorem.
-/

namespace CorralFormalization.PhysicalCorral

open Finset

/-- Cast bounded ordinary representatives into the physical cycle. -/
def physicalSites (W : ℕ) (S : Finset ℕ) : Finset (ZMod W) :=
  S.image (fun x : ℕ => (x : ZMod W))

theorem physicalSites_mem_iff {W : ℕ} [NeZero W] (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < W) (x : ZMod W) :
    x ∈ physicalSites W S ↔ x.val ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hS y hy)] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x.val, hx, ZMod.natCast_zmod_val x⟩

theorem physicalSites_decode {W : ℕ} [NeZero W] (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < W) :
    (physicalSites W S).image ZMod.val = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact (physicalSites_mem_iff S hS y).mp hy
  · intro hx
    refine Finset.mem_image.mpr ⟨(x : ZMod W), ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hS x hx)]

theorem physicalSites_card {W : ℕ} [NeZero W] (S : Finset ℕ)
    (hS : ∀ x ∈ S, x < W) :
    (physicalSites W S).card = S.card := by
  unfold physicalSites
  apply Finset.card_image_of_injOn
  intro x hx y hy heq
  have hv := congrArg ZMod.val heq
  simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt (hS x hx),
    Nat.mod_eq_of_lt (hS y hy)] using hv

theorem physicalSites_encode {W : ℕ} [NeZero W] (S : Finset (ZMod W)) :
    physicalSites W (S.image ZMod.val) = S := by
  unfold physicalSites
  rw [Finset.image_image]
  change S.image (fun x => (x.val : ZMod W)) = S
  simp

theorem adjacentGaps_length (xs : List ℕ) :
    (adjacentGaps xs).length = xs.length - 1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      simp only [adjacentGaps, List.length_cons] at *
      omega

/-- The gap inventory counts actual physical sites, also in the empty case. -/
theorem finiteCyclicGapInventory_card (W : ℕ) (S : Finset ℕ) :
    (finiteCyclicGapInventory W S).card = S.card := by
  have hlen : (S.sort (· ≤ ·)).length = S.card := Finset.length_sort _
  cases hs : S.sort (· ≤ ·) with
  | nil => simpa [finiteCyclicGapInventory, hs] using hlen
  | cons c cs =>
    simpa [finiteCyclicGapInventory, hs, cyclicGaps, adjacentGaps_length]
      using hlen

/-- A `CorralRows` row has exactly `n` sites; this is derived from the
complete inventory, rather than assumed by the representation. -/
theorem corralRows_site_card {h n : ℕ} (R : CorralRows h n) (i : Fin h) :
    (R.sites i).card = n := by
  rw [← finiteCyclicGapInventory_card (width n) (R.sites i), R.gaps]
  simp [fullGapList]

/-- Physical row sets, with every artificial row label discarded. -/
def physicalFamily {h n : ℕ} (R : CorralRows h n) :
    Finset (Finset (ZMod (width n))) :=
  Finset.univ.image (fun i => physicalSites (width n) (R.sites i))

/-- Conversely, actual unlabelled disjoint physical rows with locally
checked gap inventories can be reindexed to `CorralRows`. No labelled-row
equality or occupancy is smuggled into the input. -/
theorem physical_family_to_corralRows {h n : ℕ} [NeZero (width n)]
    (F : Finset (Finset (ZMod (width n)))) (hcard : F.card = h)
    (hne : ∀ S ∈ F, S.Nonempty)
    (hdisjoint : ∀ S ∈ F, ∀ T ∈ F, S ≠ T → Disjoint S T)
    (hgap : ∀ S ∈ F, finiteCyclicGapInventory (width n) (S.image ZMod.val) =
      Multiset.ofList (fullGapList n)) :
    ∃ R : CorralRows h n, physicalFamily R = F := by
  classical
  let e : F ≃ Fin h := Finset.equivFinOfCardEq hcard
  let R : CorralRows h n := {
    sites := fun i => ((e.symm i).val).image ZMod.val
    nonempty := by
      intro i
      exact (hne _ (e.symm i).property).image _
    bounded := by
      intro i x hx
      obtain ⟨y, _, rfl⟩ := Finset.mem_image.mp hx
      exact ZMod.val_lt _
    disjoint := by
      intro i j hij
      apply Finset.disjoint_left.mpr
      intro x hxi hxj
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxi
      obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hxj
      have hyz : y = z := ZMod.val_injective _ (hyx.trans hzx.symm)
      have hneij : (e.symm i).val ≠ (e.symm j).val := by
        intro h
        apply hij
        exact e.symm.injective (Subtype.ext h)
      exact Finset.disjoint_left.mp
        (hdisjoint _ (e.symm i).property _ (e.symm j).property hneij)
        hy (hyz ▸ hz)
    gaps := fun i => hgap _ (e.symm i).property }
  refine ⟨R, ?_⟩
  ext S
  simp only [physicalFamily, Finset.mem_image, Finset.mem_univ, true_and]
  have hrow (i : Fin h) : physicalSites (width n) (R.sites i) = (e.symm i).val :=
    physicalSites_encode _
  constructor
  · rintro ⟨i, hi⟩
    rw [hrow] at hi
    exact hi ▸ (e.symm i).property
  · intro hS
    refine ⟨e ⟨S, hS⟩, ?_⟩
    rw [hrow]
    simp

theorem corralRows_physical_nonempty {h n : ℕ} (R : CorralRows h n) (i : Fin h) :
    (physicalSites (width n) (R.sites i)).Nonempty := by
  obtain ⟨x, hx⟩ := R.nonempty i
  exact ⟨_, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩

theorem corralRows_physical_disjoint {h n : ℕ} [NeZero (width n)]
    (R : CorralRows h n) (i j : Fin h) (hij : i ≠ j) :
    Disjoint (physicalSites (width n) (R.sites i))
      (physicalSites (width n) (R.sites j)) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  exact Finset.disjoint_left.mp (R.disjoint i j hij)
    ((physicalSites_mem_iff _ (R.bounded i) x).mp hxi)
    ((physicalSites_mem_iff _ (R.bounded j) x).mp hxj)

theorem corralRows_physical_injective {h n : ℕ} [NeZero (width n)]
    (R : CorralRows h n) :
    Function.Injective (fun i => physicalSites (width n) (R.sites i)) := by
  intro i j hij
  change physicalSites (width n) (R.sites i) = physicalSites (width n) (R.sites j) at hij
  by_contra hne
  obtain ⟨x, hx⟩ := corralRows_physical_nonempty R i
  have hxj : x ∈ physicalSites (width n) (R.sites j) := by
    rw [← hij]
    exact hx
  exact Finset.disjoint_left.mp (corralRows_physical_disjoint R i j hne)
    hx hxj

theorem physicalFamily_card {h n : ℕ} [NeZero (width n)] (R : CorralRows h n) :
    (physicalFamily R).card = h := by
  rw [physicalFamily, Finset.card_image_of_injective _ (corralRows_physical_injective R)]
  simp

/-- At the counting bound no physical site is unused. The equality of
clock size and `h*n` is explicit, so this also serves other optimal clocks. -/
theorem corralRows_physical_full {h n : ℕ} [NeZero (width n)]
    (R : CorralRows h n) (hoptimal : width n = h * n) :
    Finset.univ.biUnion (fun i => physicalSites (width n) (R.sites i)) =
      (Finset.univ : Finset (ZMod (width n))) := by
  apply Finset.eq_univ_of_card
  rw [Finset.card_biUnion]
  · simp_rw [physicalSites_card _ (R.bounded _), corralRows_site_card R]
    simpa [ZMod.card] using hoptimal.symm
  · intro i hi j hj hij
    exact corralRows_physical_disjoint R i j hij

/-- Full occupancy and unique row ownership survive deletion of row labels. -/
theorem corralRows_unlabelled_partition {h n : ℕ} [NeZero (width n)]
    (R : CorralRows h n) (hoptimal : width n = h * n) (x : ZMod (width n)) :
    ∃! S, S ∈ physicalFamily R ∧ x ∈ S := by
  have hx : x ∈ Finset.univ.biUnion
      (fun i => physicalSites (width n) (R.sites i)) := by
    rw [corralRows_physical_full R hoptimal]
    exact Finset.mem_univ _
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  refine ⟨physicalSites (width n) (R.sites i),
    ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩, hi⟩, ?_⟩
  rintro S ⟨hS, hxS⟩
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hS
  by_cases hij : j = i
  · exact congrArg (fun j => physicalSites (width n) (R.sites j)) hij
  · exact False.elim (Finset.disjoint_left.mp
      (corralRows_physical_disjoint R j i hij) hxS hi)

section LocalDecoding

variable {X J A : Type*} [DecidableEq X] [Fintype J]

/-- Local input data: actual nonempty rows on disjoint supports. Alphabet
distinctness is equality of each *unordered local decomposition*, not a
condition about ambient orbits. No symmetry conclusion is an assumption. -/
structure SupportAlphabet (X J A : Type*) [DecidableEq X] where
  support : J → Finset X
  disjoint : ∀ i j, i ≠ j → Disjoint (support i) (support j)
  letters : J → A → Finset (Finset X)
  nonempty : ∀ j a S, S ∈ letters j a → S.Nonempty
  subset : ∀ j a S, S ∈ letters j a → S ⊆ support j
  distinct : ∀ j, Function.Injective (letters j)

namespace SupportAlphabet

variable (D : SupportAlphabet X J A)

/-- The physical family after independently choosing one local letter on
each support. The output contains no row labels. -/
def assemble (t : J → A) : Finset (Finset X) :=
  Finset.univ.biUnion (fun j => D.letters j (t j))

theorem assemble_mem (t : J → A) (S : Finset X) :
    S ∈ D.assemble t ↔ ∃ j, S ∈ D.letters j (t j) := by
  simp [assemble]

omit [Fintype J] in
/-- A nonempty row cannot be decoded as belonging to two distinct supports. -/
theorem local_support_unique (i j : J) (a : A) (S : Finset X)
    (hS : S ∈ D.letters i a) (hsub : S ⊆ D.support j) : i = j := by
  by_contra hij
  obtain ⟨x, hx⟩ := D.nonempty i a S hS
  exact Finset.disjoint_left.mp (D.disjoint i j hij)
    (D.subset i a S hS hx) (hsub hx)

/-- Filtering the *unlabelled* global family by one physical support
recovers precisely the chosen unordered local letter. -/
theorem recover_local_letter (t : J → A) (j : J) :
    (D.assemble t).filter (fun S => S ⊆ D.support j) = D.letters j (t j) := by
  classical
  ext S
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hS, hsub⟩
    obtain ⟨i, hi⟩ := (D.assemble_mem t S).mp hS
    have hij := D.local_support_unique i j (t i) S hi hsub
    simpa only [hij] using hi
  · intro hS
    exact ⟨(D.assemble_mem t S).mpr ⟨j, hS⟩, D.subset j (t j) S hS⟩

/-- All independent local choices are recoverable even after all row labels
have been erased. This proves the physical distinctness step of §6.4. -/
theorem assemble_injective : Function.Injective D.assemble := by
  intro t u heq
  funext j
  apply D.distinct j
  calc
    D.letters j (t j) = (D.assemble t).filter (fun S => S ⊆ D.support j) :=
      (D.recover_local_letter t j).symm
    _ = (D.assemble u).filter (fun S => S ⊆ D.support j) := by rw [heq]
    _ = D.letters j (u j) := D.recover_local_letter u j

/-- The decoded-family argument gives the full product count without any
division by an artificial row-label factor. -/
theorem assembled_family_card [DecidableEq J] [Fintype A] [DecidableEq A] :
    (Finset.univ.image D.assemble).card = Fintype.card A ^ Fintype.card J := by
  classical
  rw [Finset.card_image_of_injective _ D.assemble_injective]
  simp

/-- The number of rows is the sum of the local row counts, because a
nonempty row on one support cannot equal a row on another support. -/
theorem assemble_card (t : J → A) (r : ℕ)
    (hcard : ∀ j a, (D.letters j a).card = r) :
    (D.assemble t).card = Fintype.card J * r := by
  rw [assemble, Finset.card_biUnion]
  · simp_rw [hcard]
    simp
  · intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro S hSi hSj
    exact hij (D.local_support_unique i j (t i) S hSi (D.subset j (t j) S hSj))

theorem assemble_rows_nonempty (t : J → A) (S : Finset X)
    (hS : S ∈ D.assemble t) : S.Nonempty := by
  obtain ⟨j, hj⟩ := (D.assemble_mem t S).mp hS
  exact D.nonempty j (t j) S hj

/-- Pairwise disjointness is preserved by independent local row exchanges. -/
theorem assemble_rows_disjoint (t : J → A)
    (hlocal : ∀ j a S, S ∈ D.letters j a →
      ∀ V, V ∈ D.letters j a → S ≠ V → Disjoint S V)
    (S : Finset X) (hS : S ∈ D.assemble t)
    (V : Finset X) (hV : V ∈ D.assemble t) (hSV : S ≠ V) : Disjoint S V := by
  obtain ⟨i, hi⟩ := (D.assemble_mem t S).mp hS
  obtain ⟨j, hj⟩ := (D.assemble_mem t V).mp hV
  by_cases hij : i = j
  · subst j
    exact hlocal i (t i) S hi V hj hSV
  · exact Finset.disjoint_of_subset_left (D.subset i (t i) S hi)
      (Finset.disjoint_of_subset_right (D.subset j (t j) V hj) (D.disjoint i j hij))

/-- Local exchanges retaining each complete support retain global occupancy. -/
theorem assemble_coverage (t : J → A)
    (hcover : ∀ j a, (D.letters j a).biUnion id = D.support j) :
    (D.assemble t).biUnion id = Finset.univ.biUnion D.support := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq, D.assemble_mem]
  constructor
  · rintro ⟨S, ⟨j, hS⟩, hx⟩
    exact ⟨j, D.subset j (t j) S hS hx⟩
  · rintro ⟨j, hx⟩
    rw [← hcover j (t j)] at hx
    obtain ⟨S, hS, hxS⟩ := Finset.mem_biUnion.mp hx
    exact ⟨S, ⟨j, hS⟩, hxS⟩

/-- The construction can be returned to the existing CorralRows interface
using only local row validity, not an assumed global Corral or orbit bound. -/
theorem assemble_to_corralRows {n : ℕ} [NeZero (width n)]
    (D : SupportAlphabet (ZMod (width n)) J A) (t : J → A)
    (hcard : ∀ j a, (D.letters j a).card = 2)
    (hlocal : ∀ j a S, S ∈ D.letters j a →
      ∀ V, V ∈ D.letters j a → S ≠ V → Disjoint S V)
    (hgap : ∀ j a S, S ∈ D.letters j a →
      finiteCyclicGapInventory (width n) (S.image ZMod.val) =
        Multiset.ofList (fullGapList n)) :
    ∃ R : CorralRows (Fintype.card J * 2) n, physicalFamily R = D.assemble t := by
  apply physical_family_to_corralRows (D.assemble t) (D.assemble_card t 2 hcard)
  · exact D.assemble_rows_nonempty t
  · exact D.assemble_rows_disjoint t hlocal
  · intro S hS
    obtain ⟨j, hj⟩ := (D.assemble_mem t S).mp hS
    exact hgap j (t j) S hj

end SupportAlphabet

end LocalDecoding

/-! ## Actual translations and reflections, including permuted rows -/

/-- The physical dihedral motions. Rotations and reflections are retained
as separate constructors; on a clock of size at least three this is the
usual faithful action of its `2M` motions. -/
inductive Motion (M : ℕ)
  | rotation (c : ZMod M)
  | reflection (c : ZMod M)
  deriving DecidableEq

namespace Motion

variable {M : ℕ}

def act : Motion M → ZMod M → ZMod M
  | .rotation c, x => c + x
  | .reflection c, x => c - x

def compose : Motion M → Motion M → Motion M
  | .rotation a, .rotation b => .rotation (a + b)
  | .rotation a, .reflection b => .reflection (a + b)
  | .reflection a, .rotation b => .reflection (a - b)
  | .reflection a, .reflection b => .rotation (a - b)

theorem compose_act (f g : Motion M) (x : ZMod M) :
    (f.compose g).act x = f.act (g.act x) := by
  cases f <;> cases g <;> simp only [compose, act] <;> ring

theorem act_injective (f : Motion M) : Function.Injective f.act := by
  cases f <;> simp [act, Function.Injective]

def onRow (f : Motion M) (S : Finset (ZMod M)) : Finset (ZMod M) :=
  S.image f.act

/-- Row labels are discarded before applying the action. Equality of this
image is exactly preservation including an arbitrary permutation of rows. -/
def onFamily (f : Motion M) (F : Finset (Finset (ZMod M))) :
    Finset (Finset (ZMod M)) := F.image f.onRow

theorem onRow_compose (f g : Motion M) (S : Finset (ZMod M)) :
    (f.compose g).onRow S = f.onRow (g.onRow S) := by
  simp only [onRow, Finset.image_image, Function.comp_def]
  congr 1
  funext x
  exact compose_act f g x

@[simp] theorem identity_onRow (S : Finset (ZMod M)) :
    (rotation 0).onRow S = S := by
  change S.image (fun x => 0 + x) = S
  simp

@[simp] theorem identity_onFamily (F : Finset (Finset (ZMod M))) :
    (rotation 0).onFamily F = F := by
  change F.image (fun S => (rotation 0).onRow S) = F
  simp

theorem reflection_onRow_involutive (C : ZMod M) :
    Function.Involutive (reflection C).onRow := by
  intro S
  rw [← onRow_compose]
  simp [compose]

theorem onFamily_compose (f g : Motion M) (F : Finset (Finset (ZMod M))) :
    (f.compose g).onFamily F = f.onFamily (g.onFamily F) := by
  simp only [onFamily, Finset.image_image, Function.comp_def]
  congr 1
  funext S
  exact onRow_compose f g S

theorem reflection_onFamily_involutive (C : ZMod M) :
    Function.Involutive (reflection C).onFamily := by
  intro F
  rw [← onFamily_compose]
  simp [compose]

end Motion

/-! ## Actual two-row supports supplied by the maintained even construction -/

/-- A row from the already formalized even construction, now in `ZMod M`. -/
def evenPhysicalRow (k : ℕ) (b : Fin 2) (j : Fin k) :
    Finset (ZMod (evenConstructionClock k)) :=
  physicalSites (evenConstructionClock k) (evenConstructionRowPair k b j)

theorem evenRowPair_bound (k : ℕ) (hk : 1 ≤ k) (b : Fin 2) (j : Fin k)
    (x : ℕ) (hx : x ∈ evenConstructionRowPair k b j) : x < evenConstructionClock k := by
  obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp hx
  exact Nat.mod_lt _ (evenConstructionClock_pos k hk)

/-- Exact physical transport of the existing complete row partition. -/
theorem evenPhysicalRow_partition (k : ℕ) (hk : 1 ≤ k)
    (x : ZMod (evenConstructionClock k)) :
    ∃! bj : Fin 2 × Fin k, x ∈ evenPhysicalRow k bj.1 bj.2 := by
  let : NeZero (evenConstructionClock k) := ⟨Nat.ne_of_gt (evenConstructionClock_pos k hk)⟩
  obtain ⟨bj, hbj, huniq⟩ := evenConstructionRowPair_partition k hk x.val (ZMod.val_lt x)
  refine ⟨bj, (physicalSites_mem_iff _ (evenRowPair_bound k hk bj.1 bj.2) x).mpr hbj, ?_⟩
  intro cj hcj
  exact huniq cj ((physicalSites_mem_iff _ (evenRowPair_bound k hk cj.1 cj.2) x).mp hcj)

/-- Re-pair the two source families by any permutation. In §6 this
permutation is the half-period shift supplied by equation (D2). -/
def evenSupport (k : ℕ) (σ : Equiv.Perm (Fin k)) (j : Fin k) :
    Finset (ZMod (evenConstructionClock k)) :=
  evenPhysicalRow k 0 j ∪ evenPhysicalRow k 1 (σ j)

/-- Re-pairing actual rows gives disjoint complete physical two-row
supports. This is unconditional for every positive `k` and every `σ`. -/
theorem evenSupport_partition (k : ℕ) (hk : 1 ≤ k) (σ : Equiv.Perm (Fin k))
    (x : ZMod (evenConstructionClock k)) :
    ∃! j : Fin k, x ∈ evenSupport k σ j := by
  obtain ⟨⟨b, s⟩, hbs, huniq⟩ := evenPhysicalRow_partition k hk x
  fin_cases b
  · refine ⟨s, Finset.mem_union.mpr (Or.inl hbs), ?_⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact congrArg Prod.snd (huniq (0, j) hj)
    · have hbad := congrArg (fun bj : Fin 2 × Fin k => bj.1.val) (huniq (1, σ j) hj)
      simp at hbad
  · refine ⟨σ.symm s, Finset.mem_union.mpr (Or.inr (by simpa using hbs)), ?_⟩
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · have hbad := congrArg (fun bj : Fin 2 × Fin k => bj.1.val) (huniq (0, j) hj)
      simp at hbad
    · apply σ.injective
      simpa using congrArg Prod.snd (huniq (1, σ j) hj)

theorem evenSupport_disjoint (k : ℕ) (hk : 1 ≤ k) (σ : Equiv.Perm (Fin k))
    (i j : Fin k) (hij : i ≠ j) : Disjoint (evenSupport k σ i) (evenSupport k σ j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨s, _, huniq⟩ := evenSupport_partition k hk σ x
  exact hij ((huniq i hxi).trans (huniq j hxj).symm)

theorem evenSupport_coverage (k : ℕ) [NeZero (evenConstructionClock k)]
    (hk : 1 ≤ k) (σ : Equiv.Perm (Fin k)) :
    Finset.univ.biUnion (evenSupport k σ) =
      (Finset.univ : Finset (ZMod (evenConstructionClock k))) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  obtain ⟨j, hj, _⟩ := evenSupport_partition k hk σ x
  exact ⟨j, hj⟩

/-- The natural representative action in the maintained construction really
is translation on the physical cycle. -/
theorem evenPhysicalRow_translation (k : ℕ) (b : Fin 2) (j : Fin k) :
    evenPhysicalRow k b j =
      (Motion.rotation (evenConstructionPeriod k * j.val : ℕ)).onRow
        (physicalSites (evenConstructionClock k) (evenConstructionRowSource k b)) := by
  unfold evenPhysicalRow evenConstructionRowPair translatedSites physicalSites Motion.onRow
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro q hq
  change (((q + evenConstructionPeriod k * j.val) % evenConstructionClock k : ℕ) :
    ZMod (evenConstructionClock k)) = (evenConstructionPeriod k * j.val : ℕ) + (q : ZMod (evenConstructionClock k))
  rw [ZMod.natCast_mod, Nat.cast_add]
  exact add_comm _ _

/-- The old reflected source is also the literal reflection on `ZMod M`. -/
theorem evenPhysical_reflection (k : ℕ) (hk : 1 ≤ k) :
    physicalSites (evenConstructionClock k) (evenConstructionReflectedSet k) =
      (Motion.reflection (evenConstructionShift k : ℕ)).onRow
        (physicalSites (evenConstructionClock k) (evenConstructionRawPrefixSet k)) := by
  unfold evenConstructionReflectedSet physicalSites Motion.onRow
  rw [Finset.image_image, Finset.image_image]
  apply Finset.image_congr
  intro q hq
  have hbound := evenConstructionRawPrefixSet_clock_bound k q hk hq
  change (((evenConstructionShift k + evenConstructionClock k - q) % evenConstructionClock k : ℕ) :
    ZMod (evenConstructionClock k)) = (evenConstructionShift k : ZMod (evenConstructionClock k)) - q
  rw [ZMod.natCast_mod, Nat.cast_sub (by omega), Nat.cast_add]
  simp

/-- The precise parameter identity (D2), with `k=2m+1`, is paid over
ordinary representatives before any modular reduction. -/
theorem diversity_reflection_parameter (m : ℕ) :
    (2 * (2 * m + 1)) ^ 2 - 1 =
      evenConstructionShift (2 * m + 1) + m * evenConstructionPeriod (2 * m + 1) := by
  have hodd : (2 * m + 1) % 2 ≠ 0 := by omega
  simp only [evenConstructionShift, if_neg hodd, evenConstructionPeriod]
  have hp : 8 * (2 * m + 1) - 2 = 16 * m + 6 := by omega
  have hc : 5 * (2 * m + 1) - 2 = 10 * m + 3 := by omega
  rw [hp, hc]
  have hsquare : (2 * (2 * m + 1)) ^ 2 = (10 * m + 3 + m * (16 * m + 6)) + 1 := by ring
  rw [hsquare]
  omega

section SeedReduction

variable {M : ℕ} {T : Type*}

/-- Local rigidity of one row, rather than a stabilizer condition on an
entire assembled partition. It is an explicit condition in the subsequent conditional result. -/
def RigidRow (R : Finset (ZMod M)) : Prop :=
  ∀ f : Motion M, f.onRow R = R → f = .rotation 0

/-- If one rigid row is sent to itself or to its fixed reflection, those
two target rows force the entire ambient motion. -/
theorem rigid_seed_motion (R : Finset (ZMod M)) (C : ZMod M)
    (hrigid : RigidRow R) (f : Motion M)
    (hf : f.onRow R = R ∨ f.onRow R = (Motion.reflection C).onRow R) :
    f = .rotation 0 ∨ f = .reflection C := by
  rcases hf with hf | hf
  · exact Or.inl (hrigid f hf)
  · have hcomp : ((Motion.reflection C).compose f).onRow R = R := by
      rw [Motion.onRow_compose, hf]
      exact Motion.reflection_onRow_involutive C R
    have hzero := hrigid _ hcomp
    right
    cases f with
    | rotation c => simp [Motion.compose] at hzero
    | reflection c =>
      have hCc : C - c = 0 := Motion.rotation.inj hzero
      have hc : c = C := (sub_eq_zero.mp hCc).symm
      exact congrArg Motion.reflection hc

/-- The seed reduction used by §6.4. `marker` is a property of one physical
row (in the paper, the neighbours of its unique largest gap). Its invariance
and its exclusion on the new alphabet are local, noncircular hypotheses.
All rows are unlabelled; the whole dihedral action is quantified. -/
theorem marked_seed_reduction (family : T → Finset (Finset (ZMod M)))
    (R : Finset (ZMod M)) (C : ZMod M) (marker : Finset (ZMod M) → Prop)
    (hrigid : RigidRow R)
    (hmarker : marker R)
    (hinvariant : ∀ f : Motion M, ∀ S, marker (f.onRow S) ↔ marker S)
    (hseed : ∀ t, R ∈ family t)
    (honly : ∀ t S, S ∈ family t → marker S →
      S = R ∨ S = (Motion.reflection C).onRow R)
    (t u : T) (f : Motion M) (hf : f.onFamily (family t) = family u) :
    f = .rotation 0 ∨ f = .reflection C := by
  apply rigid_seed_motion R C hrigid f
  apply honly u (f.onRow R)
  · rw [← hf]
    exact Finset.mem_image.mpr ⟨R, hseed t, rfl⟩
  · exact (hinvariant f R).mpr hmarker

/-- Physical equivalence between unlabelled row families. -/
def PhysicallyEquivalent (F G : Finset (Finset (ZMod M))) : Prop :=
  ∃ f : Motion M, f.onFamily F = G

/-- Physical asymmetry quantifies over reflections and rotations and allows
all row permutations. -/
def PhysicallyAsymmetric (F : Finset (Finset (ZMod M))) : Prop :=
  ∀ f : Motion M, f.onFamily F = F → f = .rotation 0

/-- Once the actual seed reduction is paid, the physical equivalence
relation is exactly equality or the displayed common reflection. -/
theorem physical_equivalence_iff
    (family : T → Finset (Finset (ZMod M))) (C : ZMod M)
    (hreduce : ∀ t u f, f.onFamily (family t) = family u →
      f = Motion.rotation 0 ∨ f = Motion.reflection C)
    (t u : T) :
    PhysicallyEquivalent (family t) (family u) ↔
      family t = family u ∨ (Motion.reflection C).onFamily (family t) = family u := by
  constructor
  · rintro ⟨f, hf⟩
    rcases hreduce t u f hf with rfl | rfl
    · exact Or.inl (by simpa using hf)
    · exact Or.inr hf
  · rintro (h | h)
    · exact ⟨.rotation 0, by simpa using h⟩
    · exact ⟨.reflection C, h⟩

/-- The only possible nonidentity symmetry is the physical reflection. -/
theorem physical_asymmetry_iff
    (family : T → Finset (Finset (ZMod M))) (C : ZMod M)
    (hreduce : ∀ t u f, f.onFamily (family t) = family u →
      f = Motion.rotation 0 ∨ f = Motion.reflection C)
    (t : T) :
    PhysicallyAsymmetric (family t) ↔
      (Motion.reflection C).onFamily (family t) ≠ family t := by
  constructor
  · intro hasym hfix
    have hbad := hasym (.reflection C) hfix
    cases hbad
  · intro hnot f hf
    rcases hreduce t t f hf with h | h
    · exact h
    · subst f
      exact False.elim (hnot hf)

end SeedReduction

section InvolutionCounting

variable {T : Type*} [Fintype T] [DecidableEq T]

/-- Distinct two-element classes of an involution, excluding its fixed
points. They will be the intersections of asymmetric physical orbits with
the constructed family, once the seed reduction and equivariance are paid. -/
def involutionPairs (τ : T → T) : Finset (Finset T) :=
  (Finset.univ.filter (fun t => τ t ≠ t)).image (fun t => {t, τ t})

omit [Fintype T] in
theorem involution_pair_of_mem (τ : T → T) (hτ : Function.Involutive τ)
    (t u : T) (hu : u ∈ ({t, τ t} : Finset T)) :
    ({u, τ u} : Finset T) = {t, τ t} := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl
  · rfl
  · simp [hτ t, Finset.pair_comm]

theorem involutionPairs_disjoint (τ : T → T) (hτ : Function.Involutive τ) :
    (involutionPairs τ : Set (Finset T)).PairwiseDisjoint id := by
  intro A hA B hB hAB
  obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hB
  apply Finset.disjoint_left.mpr
  intro z hzt hzu
  exact hAB ((involution_pair_of_mem τ hτ t z hzt).symm.trans
    (involution_pair_of_mem τ hτ u z hzu))

theorem involutionPairs_cover (τ : T → T) (hτ : Function.Involutive τ) :
    (involutionPairs τ).biUnion id = Finset.univ.filter (fun t => τ t ≠ t) := by
  ext u
  constructor
  · intro hu
    obtain ⟨S, hS, huS⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hS
    have htne : τ t ≠ t := (Finset.mem_filter.mp ht).2
    simp only [id_eq, Finset.mem_insert, Finset.mem_singleton] at huS
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases huS with rfl | rfl
    · exact htne
    · simpa only [hτ t, ne_eq, eq_comm] using htne
  · intro hu
    apply Finset.mem_biUnion.mpr
    refine ⟨{u, τ u}, Finset.mem_image.mpr ⟨u, hu, rfl⟩, ?_⟩
    simp

/-- Exact general `(N-F)/2` count of the nonfixed classes of an involution.
This is an infinite schema of kernel-checked finite cardinal equalities,
not an enumeration of small Corral examples. -/
theorem involutionPairs_card (τ : T → T) (hτ : Function.Involutive τ) :
    (involutionPairs τ).card =
      (Fintype.card T - (Finset.univ.filter (fun t => τ t = t)).card) / 2 := by
  have htwo : (Finset.univ.filter (fun t => τ t ≠ t)).card =
      (involutionPairs τ).card * 2 := by
    rw [← involutionPairs_cover τ hτ,
      Finset.card_biUnion (involutionPairs_disjoint τ hτ)]
    calc
      (∑ S ∈ involutionPairs τ, (id S).card) = ∑ S ∈ involutionPairs τ, 2 := by
        apply Finset.sum_congr rfl
        intro S hS
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hS
        have htne : t ≠ τ t := ((Finset.mem_filter.mp ht).2).symm
        simp [htne]
      _ = _ := by simp
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset T)) (p := fun t => τ t = t)
  simp only [Finset.card_univ] at hsplit
  change (Finset.univ.filter (fun t => τ t = t)).card +
    (Finset.univ.filter (fun t => τ t ≠ t)).card = Fintype.card T at hsplit
  have hsub : Fintype.card T - (Finset.univ.filter (fun t => τ t = t)).card =
      (Finset.univ.filter (fun t => τ t ≠ t)).card := by omega
  rw [hsub, htwo]
  simp

end InvolutionCounting

section PhysicalOrbitCounting

variable {M : ℕ} {T : Type*} [Fintype T] [DecidableEq T]

/-- The intersection of one full physical dihedral orbit with the parameter
family. A finite parameter set is used only to represent this intersection. -/
noncomputable def physicalOrbitIntersection
    (family : T → Finset (Finset (ZMod M))) (t : T) : Finset T := by
  classical
  exact Finset.univ.filter (fun u => PhysicallyEquivalent (family t) (family u))

/-- Distinct intersections of asymmetric physical orbits with the family.
These are physical orbit classes met by the family, not labelled rows. -/
noncomputable def asymmetricOrbitIntersections
    (family : T → Finset (Finset (ZMod M))) : Finset (Finset T) := by
  classical
  exact (Finset.univ.filter (fun t => PhysicallyAsymmetric (family t))).image
    (physicalOrbitIntersection family)

/-- The exact physical `(N-F)/2` theorem from local seed data. In particular,
the crucial physical reduction is proved inside this theorem from an
invariant one-row marker and one rigid seed; it is not an orbit-count
hypothesis. The numerical value of `F` remains a separate supplier. -/
theorem marked_family_asymmetric_orbit_count
    (family : T → Finset (Finset (ZMod M))) (hinj : Function.Injective family)
    (R : Finset (ZMod M)) (C : ZMod M) (marker : Finset (ZMod M) → Prop)
    (hrigid : RigidRow R) (hmarker : marker R)
    (hinvariant : ∀ f : Motion M, ∀ S, marker (f.onRow S) ↔ marker S)
    (hseed : ∀ t, R ∈ family t)
    (honly : ∀ t S, S ∈ family t → marker S →
      S = R ∨ S = (Motion.reflection C).onRow R)
    (τ : T → T)
    (hequiv : ∀ t, (Motion.reflection C).onFamily (family t) = family (τ t)) :
    (asymmetricOrbitIntersections family).card =
      (Fintype.card T - (Finset.univ.filter (fun t => τ t = t)).card) / 2 := by
  classical
  have hreduce := marked_seed_reduction family R C marker hrigid hmarker
    hinvariant hseed honly
  have hτ : Function.Involutive τ := by
    intro t
    apply hinj
    rw [← hequiv (τ t), ← hequiv t]
    exact Motion.reflection_onFamily_involutive C (family t)
  have hrelated (t u : T) :
      PhysicallyEquivalent (family t) (family u) ↔ u = t ∨ u = τ t := by
    rw [physical_equivalence_iff family C hreduce t u, hequiv t]
    constructor
    · rintro (h | h)
      · exact Or.inl (hinj h).symm
      · exact Or.inr (hinj h).symm
    · rintro (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr rfl
  have hintersection (t : T) : physicalOrbitIntersection family t = {t, τ t} := by
    ext u
    simp only [physicalOrbitIntersection, Finset.mem_filter, Finset.mem_univ,
      true_and, Finset.mem_insert, Finset.mem_singleton]
    exact hrelated t u
  have hasym (t : T) : PhysicallyAsymmetric (family t) ↔ τ t ≠ t := by
    rw [physical_asymmetry_iff family C hreduce t, hequiv t]
    exact not_congr hinj.eq_iff
  have hclasses : asymmetricOrbitIntersections family = involutionPairs τ := by
    ext S
    simp only [asymmetricOrbitIntersections, involutionPairs, Finset.mem_image,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨t, ht, hS⟩
      exact ⟨t, (hasym t).mp ht, (hintersection t).symm.trans hS⟩
    · rintro ⟨t, ht, hS⟩
      exact ⟨t, (hasym t).mpr ht, (hintersection t).trans hS⟩
  rw [hclasses, involutionPairs_card τ hτ]

end PhysicalOrbitCounting

end CorralFormalization.PhysicalCorral
