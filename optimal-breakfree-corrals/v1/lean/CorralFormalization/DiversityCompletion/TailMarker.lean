import CorralFormalization.ConstructionSupport.PhysicalRows
import CorralFormalization.ConstructionSupport.LatinTransfer
import CorralFormalization.DiversityCompletion.CyclicGeometry

/-!
The three residue classes of gap-n tails in the Latin reassignment.
This file targets general modular statements, not a finite height check.
-/

namespace CorralLatinTailMarker

def residues (n : ℕ) : Finset (ZMod n) := {-1, 0, 2}

theorem mem_residues {n : ℕ} (x : ZMod n) :
    x ∈ residues n ↔ x = -1 ∨ x = 0 ∨ x = 2 := by
  simp [residues]

theorem small_cast_ne_zero {n k : ℕ} (hk : 0 < k) (hkn : k < n) :
    (k : ZMod n) ≠ 0 := by
  intro h
  exact Nat.not_dvd_of_pos_of_lt hk hkn ((ZMod.natCast_eq_zero_iff k n).mp h)

/-- A common rotation preserving the residue marker has zero offset. -/
theorem rotation_offset_zero {n : ℕ} (hn : 7 ≤ n) (c : ZMod n)
    (h : (residues n).image (fun x => c + x) = residues n) : c = 0 := by
  have hn1 : (1 : ZMod n) ≠ 0 := by
    simpa only [Nat.cast_one] using
      (small_cast_ne_zero (n := n) (k := 1) (by decide) (by omega))
  have hn2 : (2 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 2) (by decide) (by omega)
  have hn4 : (4 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 4) (by decide) (by omega)
  have hn5 : (5 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 5) (by decide) (by omega)
  have himage (x : ZMod n) (hx : x ∈ residues n) : c + x ∈ residues n := by
    rw [← h]
    exact Finset.mem_image_of_mem _ hx
  have hc : c = -1 ∨ c = 0 ∨ c = 2 := by
    have := himage 0 (by simp [residues])
    simpa [mem_residues] using this
  rcases hc with hc | hc | hc
  · subst c
    have hb := (mem_residues _).mp (himage (-1) (by simp [residues]))
    rcases hb with hb | hb | hb
    · exfalso; apply hn1; linear_combination -hb
    · exfalso; apply hn2; linear_combination -hb
    · exfalso; apply hn4; linear_combination -hb
  · exact hc
  · subst c
    have hb := (mem_residues _).mp (himage 2 (by simp [residues]))
    rcases hb with hb | hb | hb
    · exfalso; apply hn5; linear_combination hb
    · exfalso; apply hn4; linear_combination hb
    · exfalso; apply hn2; linear_combination hb

/-- No common reflection preserves the residue marker. -/
theorem no_reflection {n : ℕ} (hn : 7 ≤ n) (c : ZMod n) :
    (residues n).image (fun x => c - x) ≠ residues n := by
  have hn1 : (1 : ZMod n) ≠ 0 := by
    simpa only [Nat.cast_one] using
      (small_cast_ne_zero (n := n) (k := 1) (by decide) (by omega))
  have hn2 : (2 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 2) (by decide) (by omega)
  have hn3 : (3 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 3) (by decide) (by omega)
  have hn4 : (4 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 4) (by decide) (by omega)
  have hn5 : (5 : ZMod n) ≠ 0 := small_cast_ne_zero (n := n) (k := 5) (by decide) (by omega)
  intro h
  have himage (x : ZMod n) (hx : x ∈ residues n) : c - x ∈ residues n := by
    rw [← h]
    exact Finset.mem_image_of_mem _ hx
  have hc : c = -1 ∨ c = 0 ∨ c = 2 := by
    have := himage 0 (by simp [residues])
    simpa [mem_residues] using this
  rcases hc with hc | hc | hc
  · subst c
    have hb := (mem_residues _).mp (himage 2 (by simp [residues]))
    rcases hb with hb | hb | hb
    · apply hn2; linear_combination -hb
    · apply hn3; linear_combination -hb
    · apply hn5; linear_combination -hb
  · subst c
    have hb := (mem_residues _).mp (himage (-1) (by simp [residues]))
    rcases hb with hb | hb | hb
    · apply hn2; linear_combination hb
    · apply hn1; linear_combination hb
    · apply hn1; linear_combination -hb
  · subst c
    have hb := (mem_residues _).mp (himage (-1) (by simp [residues]))
    rcases hb with hb | hb | hb
    · apply hn4; linear_combination hb
    · apply hn3; linear_combination hb
    · apply hn1; linear_combination hb

def phasePair (h : ℕ) : Finset (ZMod h) := {0, 3}

/-- For h≥7, the two marked phases three apart admit no nonzero rotation. -/
theorem phase_pair_translation_zero {h : ℕ} (hh : 7 ≤ h) (c : ZMod h)
    (hpres : (phasePair h).image (fun x => c + x) = phasePair h) : c = 0 := by
  have hn3 : (3 : ZMod h) ≠ 0 := small_cast_ne_zero (n := h) (k := 3) (by decide) (by omega)
  have hn6 : (6 : ZMod h) ≠ 0 := small_cast_ne_zero (n := h) (k := 6) (by decide) (by omega)
  have himage (x : ZMod h) (hx : x ∈ phasePair h) : c + x ∈ phasePair h := by
    rw [← hpres]
    exact Finset.mem_image_of_mem _ hx
  have hc : c = 0 ∨ c = 3 := by
    have := himage 0 (by simp [phasePair])
    simpa [phasePair] using this
  rcases hc with hc | hc
  · exact hc
  · subst c
    have hb := himage 3 (by simp [phasePair])
    simp only [phasePair, Finset.mem_insert, Finset.mem_singleton] at hb
    rcases hb with hb | hb
    · exfalso; apply hn6; linear_combination hb
    · exfalso; apply hn3; linear_combination hb

/-- Projection from the physical clock h*n to residues modulo n. -/
def residueMap (h n : ℕ) : ZMod (h*n) →+* ZMod n :=
  ZMod.castHom (Nat.dvd_mul_left n h) (ZMod n)

theorem projected_translation {h n : ℕ} (T : Finset (ZMod (h*n)))
    (d : ZMod (h*n)) :
    (T.image (fun x => d+x)).image (residueMap h n) =
      (T.image (residueMap h n)).image (fun x => residueMap h n d+x) := by
  simp only [Finset.image_image, Function.comp_def, map_add]

/-- A reflected clockwise gap of length n has its tail sent to b-n-x. -/
theorem projected_tail_reflection {h n : ℕ} (T : Finset (ZMod (h*n)))
    (b : ZMod (h*n)) :
    (T.image (fun x => b - (n : ZMod (h*n)) - x)).image (residueMap h n) =
      (T.image (residueMap h n)).image (fun x => residueMap h n b-x) := by
  simp only [Finset.image_image, Function.comp_def, map_sub, map_natCast,
    ZMod.natCast_self, sub_zero]

theorem physical_rotation_residue_zero {h n : ℕ} (hn : 7 ≤ n)
    (T : Finset (ZMod (h*n))) (hres : T.image (residueMap h n) = residues n)
    (d : ZMod (h*n)) (hrot : T.image (fun x => d+x) = T) :
    residueMap h n d = 0 := by
  apply rotation_offset_zero hn
  calc
    (residues n).image (fun x => residueMap h n d+x) =
        (T.image (residueMap h n)).image (fun x => residueMap h n d+x) := by rw [hres]
    _ = (T.image (fun x => d+x)).image (residueMap h n) := by
      rw [projected_translation]
    _ = T.image (residueMap h n) := by rw [hrot]
    _ = residues n := hres

/-- No physical reflection can preserve a tail set with the H3 residues. -/
theorem physical_tail_reflection_impossible {h n : ℕ} (hn : 7 ≤ n)
    (T : Finset (ZMod (h*n))) (hres : T.image (residueMap h n) = residues n)
    (b : ZMod (h*n)) :
    T.image (fun x => b - (n : ZMod (h*n)) - x) ≠ T := by
  intro href
  apply no_reflection hn (residueMap h n b)
  calc
    (residues n).image (fun x => residueMap h n b-x) =
        (T.image (residueMap h n)).image (fun x => residueMap h n b-x) := by rw [hres]
    _ = (T.image (fun x => b - (n : ZMod (h*n)) - x)).image (residueMap h n) := by
      rw [projected_tail_reflection]
    _ = T.image (residueMap h n) := by rw [href]
    _ = residues n := hres

/-- One uniquely marked residue-2 tail excludes every remaining rotation. -/
theorem physical_rotation_zero_of_unique_tail {h n : ℕ} (hn : 7 ≤ n)
    (T : Finset (ZMod (h*n))) (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n)) (ha : anchor ∈ T) (ha2 : residueMap h n anchor = 2)
    (hunique : ∀ x ∈ T, residueMap h n x = 2 → x = anchor)
    (d : ZMod (h*n)) (hrot : T.image (fun x => d+x) = T) : d = 0 := by
  have hd := physical_rotation_residue_zero hn T hres d hrot
  have hm : d+anchor ∈ T := by
    rw [← hrot]
    exact Finset.mem_image_of_mem _ ha
  have hm2 : residueMap h n (d+anchor) = 2 := by simp [map_add, hd, ha2]
  have heq := hunique (d+anchor) hm hm2
  linear_combination heq

theorem cast_multiple_ne_zero {h n k : ℕ} (hn : 0 < n) (hk : 0 < k)
    (hkh : k < h) : ((k*n : ℕ) : ZMod (h*n)) ≠ 0 := by
  apply small_cast_ne_zero (n := h*n) (k := k*n)
  · exact Nat.mul_pos hk hn
  · exact Nat.mul_lt_mul_of_pos_right hkh hn

/-- Two residue-2 tails three phases apart exclude every remaining rotation. -/
theorem physical_rotation_zero_of_two_tails {h n : ℕ} (hn : 7 ≤ n) (hh : 7 ≤ h)
    (T : Finset (ZMod (h*n))) (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n))
    (hpair : T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3*n : ℕ) : ZMod (h*n))})
    (d : ZMod (h*n)) (hrot : T.image (fun x => d+x) = T) : d = 0 := by
  have hd := physical_rotation_residue_zero hn T hres d hrot
  have hn3 : ((3*n : ℕ) : ZMod (h*n)) ≠ 0 :=
    cast_multiple_ne_zero (by omega) (by decide) (by omega)
  have hn6 : ((6*n : ℕ) : ZMod (h*n)) ≠ 0 :=
    cast_multiple_ne_zero (by omega) (by decide) (by omega)
  have himage (x : ZMod (h*n)) (hx : x ∈ T) : d+x ∈ T := by
    rw [← hrot]
    exact Finset.mem_image_of_mem _ hx
  have hmarked (x : ZMod (h*n))
      (hx : x ∈ T.filter (fun x => residueMap h n x = 2)) :
      d+x ∈ T.filter (fun x => residueMap h n x = 2) := by
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨himage x hx.1, by simp [map_add, hd, hx.2]⟩
  have h0 : anchor ∈ T.filter (fun x => residueMap h n x = 2) := by
    rw [hpair]; simp
  have h3 : anchor + ((3*n : ℕ) : ZMod (h*n)) ∈
      T.filter (fun x => residueMap h n x = 2) := by
    rw [hpair]; simp
  have hfirst := hmarked anchor h0
  rw [hpair] at hfirst
  simp only [Finset.mem_insert, Finset.mem_singleton] at hfirst
  rcases hfirst with hfirst | hfirst
  · linear_combination hfirst
  · have hd3 : d = ((3*n : ℕ) : ZMod (h*n)) := by linear_combination hfirst
    have hsecond := hmarked (anchor + ((3*n : ℕ) : ZMod (h*n))) h3
    rw [hpair] at hsecond
    simp only [Finset.mem_insert, Finset.mem_singleton] at hsecond
    rcases hsecond with hsecond | hsecond
    · exfalso
      apply hn6
      rw [hd3] at hsecond
      push_cast at hsecond ⊢
      linear_combination hsecond
    · exfalso
      apply hn3
      have heq : d = 0 := by linear_combination hsecond
      exact hd3.symm.trans heq

open CorralFormalization.PhysicalCorral

abbrev PhysicalFamily (h n : ℕ) := Finset (Finset (ZMod (h*n)))

/-- An explicit interface for the clockwise tails of all gap-n edges.
The two transformation laws remain separate geometric proof obligations:
the reflection reverses the edge and therefore subtracts n from the old tail. -/
structure TailExtractor (h n : ℕ) where
  tails : PhysicalFamily h n → Finset (ZMod (h*n))
  rotation : ∀ d F,
    tails ((Motion.rotation d).onFamily F) = (tails F).image (fun x => d+x)
  reflection : ∀ b F,
    tails ((Motion.reflection b).onFamily F) =
      (tails F).image (fun x => b - (n : ZMod (h*n)) - x)

open CorralFormalization.DiversitySymmetry

/-- The actual n-gap tails of an unlabelled physical row family. -/
noncomputable def actualFamilyTails (h n : ℕ) [NeZero (h*n)]
    (F : PhysicalFamily h n) : Finset (ZMod (h*n)) :=
  F.biUnion (fun row => gapTails row n)

theorem actualFamilyTails_rotation {h n : ℕ} [NeZero (h*n)]
    (d : ZMod (h*n)) (F : PhysicalFamily h n) :
    actualFamilyTails h n ((Motion.rotation d).onFamily F) =
      (actualFamilyTails h n F).image (fun x => d+x) := by
  classical
  simp only [actualFamilyTails, Motion.onFamily, Finset.image_biUnion,
    Finset.biUnion_image, gapTails_rotation]

theorem actualFamilyTails_reflection {h n : ℕ} [NeZero (h*n)]
    (b : ZMod (h*n)) (F : PhysicalFamily h n) :
    actualFamilyTails h n ((Motion.reflection b).onFamily F) =
      (actualFamilyTails h n F).image (fun x => b - (n : ZMod (h*n)) - x) := by
  classical
  simp only [actualFamilyTails, Motion.onFamily, Finset.image_biUnion,
    Finset.biUnion_image, gapTails_reflection]

/-- Both TailExtractor laws hold for actual consecutive physical gaps. -/
noncomputable def actualTailExtractor (h n : ℕ) [NeZero (h*n)] : TailExtractor h n where
  tails := actualFamilyTails h n
  rotation := actualFamilyTails_rotation
  reflection := actualFamilyTails_reflection

/-- A common tail set with a trivial rotational stabilizer excludes every
nonidentity physical motion between two unlabelled row families. -/
theorem family_motion_rigid_of_tail_rigid {h n : ℕ} (hn : 7 ≤ n)
    (E : TailExtractor h n) (P Q : PhysicalFamily h n)
    (T : Finset (ZMod (h*n))) (hP : E.tails P = T) (hQ : E.tails Q = T)
    (hres : T.image (residueMap h n) = residues n)
    (hrot : ∀ d, T.image (fun x => d+x) = T → d=0)
    (f : Motion (h*n)) (hf : f.onFamily P = Q) : f = .rotation 0 := by
  cases f with
  | rotation d =>
    have hT : T.image (fun x => d+x) = T := by
      calc
        T.image (fun x => d+x) = E.tails ((Motion.rotation d).onFamily P) := by
          simpa only [hP] using (E.rotation d P).symm
        _ = E.tails Q := congrArg E.tails hf
        _ = T := hQ
    have hd := hrot d hT
    simp [hd]
  | reflection b =>
    have hT : T.image (fun x => b - (n : ZMod (h*n)) - x) = T := by
      calc
        T.image (fun x => b - (n : ZMod (h*n)) - x) =
            E.tails ((Motion.reflection b).onFamily P) := by
          simpa only [hP] using (E.reflection b P).symm
        _ = E.tails Q := congrArg E.tails hf
        _ = T := hQ
    exact False.elim (physical_tail_reflection_impossible hn T hres b hT)

/-- Odd-tile marker case: a unique residue-2 tail forces full physical rigidity. -/
theorem family_motion_rigid_of_unique_tail {h n : ℕ} (hn : 7 ≤ n)
    (E : TailExtractor h n) (P Q : PhysicalFamily h n)
    (T : Finset (ZMod (h*n))) (hP : E.tails P = T) (hQ : E.tails Q = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n)) (ha : anchor ∈ T) (ha2 : residueMap h n anchor = 2)
    (hunique : ∀ x ∈ T, residueMap h n x = 2 → x = anchor)
    (f : Motion (h*n)) (hf : f.onFamily P = Q) : f = .rotation 0 := by
  apply family_motion_rigid_of_tail_rigid hn E P Q T hP hQ hres _ f hf
  intro d hrot
  exact physical_rotation_zero_of_unique_tail hn T hres anchor ha ha2 hunique d hrot

/-- Even-tile marker case: two residue-2 tails three phases apart do likewise. -/
theorem family_motion_rigid_of_two_tails {h n : ℕ} (hn : 7 ≤ n) (hh : 7 ≤ h)
    (E : TailExtractor h n) (P Q : PhysicalFamily h n)
    (T : Finset (ZMod (h*n))) (hP : E.tails P = T) (hQ : E.tails Q = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n))
    (hpair : T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3*n : ℕ) : ZMod (h*n))})
    (f : Motion (h*n)) (hf : f.onFamily P = Q) : f = .rotation 0 := by
  apply family_motion_rigid_of_tail_rigid hn E P Q T hP hQ hres _ f hf
  intro d hrot
  exact physical_rotation_zero_of_two_tails hn hh T hres anchor hpair d hrot

theorem asymmetric_of_unique_tail {h n : ℕ} (hn : 7 ≤ n)
    (E : TailExtractor h n) (P : PhysicalFamily h n)
    (T : Finset (ZMod (h*n))) (hP : E.tails P = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n)) (ha : anchor ∈ T) (ha2 : residueMap h n anchor = 2)
    (hunique : ∀ x ∈ T, residueMap h n x = 2 → x = anchor) :
    PhysicallyAsymmetric P := by
  intro f hf
  exact family_motion_rigid_of_unique_tail hn E P P T hP hP hres anchor ha ha2 hunique f hf

theorem asymmetric_of_two_tails {h n : ℕ} (hn : 7 ≤ n) (hh : 7 ≤ h)
    (E : TailExtractor h n) (P : PhysicalFamily h n)
    (T : Finset (ZMod (h*n))) (hP : E.tails P = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n))
    (hpair : T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3*n : ℕ) : ZMod (h*n))}) :
    PhysicallyAsymmetric P := by
  intro f hf
  exact family_motion_rigid_of_two_tails hn hh E P P T hP hP hres anchor hpair f hf

/-- The complete physical orbit, with unlabelled rows, under all translations
and reflections of the finite clock. -/
def physicalOrbit {h n : ℕ} [NeZero (h*n)] (P : PhysicalFamily h n) :
    Finset (PhysicalFamily h n) :=
  (Finset.univ.image (fun d : ZMod (h*n) => (Motion.rotation d).onFamily P)) ∪
  (Finset.univ.image (fun b : ZMod (h*n) => (Motion.reflection b).onFamily P))

theorem mem_own_physicalOrbit {h n : ℕ} [NeZero (h*n)] (P : PhysicalFamily h n) :
    P ∈ physicalOrbit P := by
  apply Finset.mem_union_left
  exact Finset.mem_image.mpr ⟨0, Finset.mem_univ _, by simp⟩

theorem physicalOrbit_eq_gives_motion {h n : ℕ} [NeZero (h*n)]
    (P Q : PhysicalFamily h n) (heq : physicalOrbit P = physicalOrbit Q) :
    ∃ f : Motion (h*n), f.onFamily P = Q := by
  have hm : Q ∈ physicalOrbit P := by rw [heq]; exact mem_own_physicalOrbit Q
  rcases Finset.mem_union.mp hm with hm | hm
  · obtain ⟨d, _, hd⟩ := Finset.mem_image.mp hm
    exact ⟨.rotation d, hd⟩
  · obtain ⟨b, _, hb⟩ := Finset.mem_image.mp hm
    exact ⟨.reflection b, hb⟩

/-- For any family whose only inter-member motion is the identity, the map
from its parameters to full physical dihedral orbits is injective. -/
theorem physicalOrbit_map_injective {h n : ℕ} [NeZero (h*n)] {α : Type*}
    (family : α → PhysicalFamily h n) (hinj : Function.Injective family)
    (hrigid : ∀ a b (f : Motion (h*n)), f.onFamily (family a) = family b → f = .rotation 0) :
    Function.Injective (fun a => physicalOrbit (family a)) := by
  intro a b heq
  obtain ⟨f, hf⟩ := physicalOrbit_eq_gives_motion _ _ heq
  have hf0 := hrigid a b f hf
  rw [hf0] at hf
  apply hinj
  simpa using hf

/-- Consequently the family meets exactly one full physical orbit for
each parameter; the finite type may later be instantiated by Latin choices. -/
theorem physicalOrbit_image_card {h n : ℕ} [NeZero (h*n)]
    {α : Type*} [Fintype α] (family : α → PhysicalFamily h n)
    (hinj : Function.Injective family)
    (hrigid : ∀ a b (f : Motion (h*n)), f.onFamily (family a) = family b → f = .rotation 0) :
    (Finset.univ.image (fun a => physicalOrbit (family a))).card = Fintype.card α := by
  classical
  rw [Finset.card_image_of_injective _ (physicalOrbit_map_injective family hinj hrigid)]
  simp

theorem unique_tail_family_orbits {h n : ℕ} (hn : 7 ≤ n) [NeZero (h*n)]
    {α : Type*} [Fintype α] (E : TailExtractor h n)
    (family : α → PhysicalFamily h n) (hinj : Function.Injective family)
    (T : Finset (ZMod (h*n))) (hT : ∀ a, E.tails (family a) = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n)) (ha : anchor ∈ T) (ha2 : residueMap h n anchor = 2)
    (hunique : ∀ x ∈ T, residueMap h n x = 2 → x = anchor) :
    (Finset.univ.image (fun a => physicalOrbit (family a))).card = Fintype.card α ∧
      ∀ a, PhysicallyAsymmetric (family a) := by
  have hrigid : ∀ a b (f : Motion (h*n)), f.onFamily (family a) = family b → f = .rotation 0 := by
    intro a b f hf
    exact family_motion_rigid_of_unique_tail hn E _ _ T (hT a) (hT b)
      hres anchor ha ha2 hunique f hf
  constructor
  · exact physicalOrbit_image_card family hinj hrigid
  · intro a f hf
    exact hrigid a a f hf

theorem two_tail_family_orbits {h n : ℕ} (hn : 7 ≤ n) (hh : 7 ≤ h) [NeZero (h*n)]
    {α : Type*} [Fintype α] (E : TailExtractor h n)
    (family : α → PhysicalFamily h n) (hinj : Function.Injective family)
    (T : Finset (ZMod (h*n))) (hT : ∀ a, E.tails (family a) = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n))
    (hpair : T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3*n : ℕ) : ZMod (h*n))}) :
    (Finset.univ.image (fun a => physicalOrbit (family a))).card = Fintype.card α ∧
      ∀ a, PhysicallyAsymmetric (family a) := by
  have hrigid : ∀ a b (f : Motion (h*n)), f.onFamily (family a) = family b → f = .rotation 0 := by
    intro a b f hf
    exact family_motion_rigid_of_two_tails hn hh E _ _ T (hT a) (hT b)
      hres anchor hpair f hf
  constructor
  · exact physicalOrbit_image_card family hinj hrigid
  · intro a f hf
    exact hrigid a a f hf

open CorralFormalization.LatinTransfer

/-- There are finitely many fully labelled order-r Latin squares. -/
instance latinSquareFinite (r : ℕ) : Finite (LatinSquare r) := by
  apply Finite.of_injective (fun S : LatinSquare r => S.entry)
  intro S T h
  apply LatinSquare.ext
  intro j u
  exact congrFun (congrFun h j) u

noncomputable instance latinSquareFintype (r : ℕ) : Fintype (LatinSquare r) :=
  Fintype.ofFinite _

/-- This counts exactly the labelled Latin squares used in §8. -/
noncomputable def latinSquareCount (r : ℕ) : ℕ := Fintype.card (LatinSquare r)

theorem latinFamily_card (h r : ℕ) [NeZero h] :
    Fintype.card (Family h r) = latinSquareCount r ^ h := by
  classical
  simp [Family, latinSquareCount, ZMod.card]

/-- The concrete connectorPrefixCenterSite choices of this connector construction, with one common fixed skeleton. -/
noncomputable def connectorPrefixLatinFamily {h n r : ℕ} [NeZero h]
    (F : FixedSkeleton (connectorPrefixCenterSite h n r)) (L : Family h r) : PhysicalFamily h n :=
  unlabelledPartition (connectorPrefixCenterSite h n r) F (phaseOffset h r) L

theorem connectorPrefix_markerSizeBounds {h n r : ℕ} [NeZero h]
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n) :
    7 ≤ n ∧ 7 ≤ h := by
  have hp : 0 < h := Nat.pos_of_ne_zero (NeZero.ne h)
  have hn' : n+1 = 2*h := by omega
  have hrsq : 4 ≤ r*r := by nlinarith
  constructor <;> nlinarith

/-- If the actual common n-gap tails have the one-anchor structure, the
literal connectorPrefixCenterSite Latin family has exactly L_r^h full physical orbits, all asymmetric.
The common skeleton and the stated actual-tail structure remain hypotheses. -/
theorem connectorPrefixLatin_unique_tail_orbits {h n r : ℕ} [NeZero h] [NeZero (h*n)]
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (F : FixedSkeleton (connectorPrefixCenterSite h n r)) (T : Finset (ZMod (h*n)))
    (hT : ∀ L : Family h r, actualFamilyTails h n (connectorPrefixLatinFamily F L) = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n)) (ha : anchor ∈ T) (ha2 : residueMap h n anchor = 2)
    (hunique : ∀ x ∈ T, residueMap h n x = 2 → x = anchor) :
    (Finset.univ.image (fun L : Family h r => physicalOrbit (connectorPrefixLatinFamily F L))).card =
      latinSquareCount r ^ h ∧ ∀ L, PhysicallyAsymmetric (connectorPrefixLatinFamily F L) := by
  have hsmall := connectorPrefix_markerSizeBounds hr hn hlarge
  have hinj : Function.Injective (connectorPrefixLatinFamily F) :=
    connectorPrefix_unlabelledPartition_injective hr hn hlarge F
  have hc := unique_tail_family_orbits hsmall.1 (actualTailExtractor h n)
    (connectorPrefixLatinFamily F) hinj T hT hres anchor ha ha2 hunique
  exact ⟨hc.1.trans (latinFamily_card h r), hc.2⟩

/-- The same conclusion when the actual residue-2 tails form a pair three
physical phases apart. -/
theorem connectorPrefixLatin_two_tail_orbits {h n r : ℕ} [NeZero h] [NeZero (h*n)]
    (hr : 2 ≤ r) (hn : n = 2*h-1) (hlarge : 100*r*r ≤ n)
    (F : FixedSkeleton (connectorPrefixCenterSite h n r)) (T : Finset (ZMod (h*n)))
    (hT : ∀ L : Family h r, actualFamilyTails h n (connectorPrefixLatinFamily F L) = T)
    (hres : T.image (residueMap h n) = residues n)
    (anchor : ZMod (h*n))
    (hpair : T.filter (fun x => residueMap h n x = 2) =
      {anchor, anchor + ((3*n : ℕ) : ZMod (h*n))}) :
    (Finset.univ.image (fun L : Family h r => physicalOrbit (connectorPrefixLatinFamily F L))).card =
      latinSquareCount r ^ h ∧ ∀ L, PhysicallyAsymmetric (connectorPrefixLatinFamily F L) := by
  have hsmall := connectorPrefix_markerSizeBounds hr hn hlarge
  have hinj : Function.Injective (connectorPrefixLatinFamily F) :=
    connectorPrefix_unlabelledPartition_injective hr hn hlarge F
  have hc := two_tail_family_orbits hsmall.1 hsmall.2 (actualTailExtractor h n)
    (connectorPrefixLatinFamily F) hinj T hT hres anchor hpair
  exact ⟨hc.1.trans (latinFamily_card h r), hc.2⟩

end CorralLatinTailMarker
