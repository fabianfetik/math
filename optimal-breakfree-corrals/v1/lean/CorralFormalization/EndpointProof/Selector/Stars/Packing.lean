import CorralFormalization.EndpointProof.Selector.Stars.Basic

/-!
# Constructed fresh star parameters

The sufficient exceptional set has at most `1+4*k+3*k^2` parameters in an
odd finite commutative ring.  For `k≤3` this is at most forty.  All excluded
root signs and all inverse closures are included in these proved counts.
-/

open scoped Classical BigOperators

namespace EndpointSelector.Stars

set_option maxHeartbeats 1500000

variable {G : Type*} [CommRing G] [DecidableEq G] {k : ℕ}

def starLinearExceptions (a : Fin k → G) : Finset G :=
  ({0} ∪ Finset.univ.image (fun i ↦ -a i)) ∪ starRootSupport a ∪
    Finset.univ.biUnion (fun i ↦ (starRootSupport a).image (fun r ↦ -a i-r))

def starDoubleExceptions (a : Fin k → G) : Finset G :=
  Finset.univ.image (fun i ↦ -a i) ∪
    Finset.univ.image (fun ij : Fin k × Fin k ↦ -(a ij.1+a ij.2))

theorem starLinearExceptions_card_le (a : Fin k → G) :
    (starLinearExceptions a).card ≤ 1+3*k+2*k^2 := by
  have hi : (Finset.univ.image (fun i ↦ -a i)).card ≤ k :=
    Finset.card_image_le.trans (by simp)
  have hb : (Finset.univ.biUnion
      (fun i ↦ (starRootSupport a).image (fun r ↦ -a i-r))).card ≤ k*(2*k) := by
    simpa using Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin k))
      (fun i ↦ (starRootSupport a).image (fun r ↦ -a i-r)) (2*k)
      (fun _ _ ↦ Finset.card_image_le.trans (starRootSupport_card_le a))
  have h0 := Finset.card_union_le ({0} : Finset G) (Finset.univ.image (fun i ↦ -a i))
  have h1 := Finset.card_union_le
    (({0} : Finset G) ∪ Finset.univ.image (fun i ↦ -a i)) (starRootSupport a)
  have h2 := Finset.card_union_le
    ((({0} : Finset G) ∪ Finset.univ.image (fun i ↦ -a i)) ∪ starRootSupport a)
    (Finset.univ.biUnion (fun i ↦ (starRootSupport a).image (fun r ↦ -a i-r)))
  have hr := starRootSupport_card_le a
  simp only [Finset.card_singleton] at h0
  dsimp only [starLinearExceptions]
  nlinarith

theorem starDoubleExceptions_card_le (a : Fin k → G) :
    (starDoubleExceptions a).card ≤ k+k^2 := by
  have h1 : (Finset.univ.image (fun i ↦ -a i)).card ≤ k :=
    Finset.card_image_le.trans (by simp)
  have h2 : (Finset.univ.image (fun ij : Fin k × Fin k ↦ -(a ij.1+a ij.2))).card ≤ k^2 :=
    Finset.card_image_le.trans (by simp [pow_two])
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)

theorem starValid_of_avoids_exceptions (a : Fin k → G) (hr : StarRoots a) (u : G)
    (hl : u ∉ starLinearExceptions a) (hd : u+u ∉ starDoubleExceptions a) :
    StarValid a u := by
  have h0 : u ≠ 0 := fun h ↦ hl (by simp [starLinearExceptions,h])
  have hz (i : Fin k) : u ≠ -a i := by
    intro h
    apply hl
    exact Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h.symm⟩)))
  have hroot (r : G) (hr : r ∈ starRootSupport a) : u ≠ r := by
    intro h
    exact hl (Finset.mem_union_left _ (Finset.mem_union_right _ (h ▸ hr)))
  have hshift (i : Fin k) (r : G) (hr : r ∈ starRootSupport a) : u ≠ -a i-r := by
    intro h
    exact hl (Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨r,hr,h.symm⟩⟩))
  have hd1 (i : Fin k) : u+u ≠ -a i := by
    intro h
    exact hd (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,h.symm⟩))
  have hd2 (i j : Fin k) : u+u ≠ -(a i+a j) := by
    intro h
    exact hd (Finset.mem_union_right _
      (Finset.mem_image.mpr ⟨(i,j),Finset.mem_univ _,h.symm⟩))
  have hnonzero : ∀ j, starRepresentative a u j ≠ 0 := by
    rintro (_ | i)
    · exact h0
    · intro h
      apply hz i
      dsimp only [starRepresentative] at h
      linear_combination -h
  refine ⟨hnonzero,?_,?_⟩
  · rintro (_ | i) (_ | j) hij
    · exact False.elim (hij rfl)
    · constructor <;> intro h
      · apply hd1 j
        dsimp only [starRepresentative] at h
        linear_combination h
      · apply hr.1 j
        dsimp only [starRepresentative] at h
        linear_combination -h
    · constructor <;> intro h
      · apply hd1 i
        dsimp only [starRepresentative] at h
        linear_combination -h
      · apply hr.1 i
        dsimp only [starRepresentative] at h
        linear_combination -h
    · have hij' : i ≠ j := by simpa using hij
      constructor <;> intro h
      · apply (hr.2 i j hij').1
        dsimp only [starRepresentative] at h
        linear_combination -h
      · apply hd2 i j
        dsimp only [starRepresentative] at h
        linear_combination -h
  · apply Finset.disjoint_left.mpr
    intro x hx hxr
    have hnxr : -x ∈ starRootSupport a := by
      obtain ⟨i,h | h⟩ := (mem_starRootSupport a x).1 hxr
      · exact (mem_starRootSupport a (-x)).2 ⟨i,Or.inr (by rw [h])⟩
      · exact (mem_starRootSupport a (-x)).2 ⟨i,Or.inl (by rw [h,neg_neg])⟩
    obtain ⟨j,hx | hx⟩ := (mem_starSupport a u x).1 hx
    · cases j with
      | none => exact hroot x hxr hx.symm
      | some i =>
        apply hshift i x hxr
        dsimp only [starRepresentative] at hx
        linear_combination hx
    · cases j with
      | none =>
        apply hroot (-x) hnxr
        dsimp only [starRepresentative] at hx
        linear_combination hx
      | some i =>
        apply hshift i (-x) hnxr
        dsimp only [starRepresentative] at hx
        linear_combination -hx

omit [DecidableEq G] in
theorem starRepresentative_parameter_injective (a : Fin k → G) (j : Option (Fin k)) :
    Function.Injective (fun u ↦ starRepresentative a u j) := by
  intro u v h
  cases j <;> simpa [starRepresentative] using h

omit [DecidableEq G] in
theorem starSignedRepresentative_parameter_injective
    (a : Fin k → G) (jb : Option (Fin k) × Bool) :
    Function.Injective (fun u ↦ starSignedRepresentative a u jb) := by
  rcases jb with ⟨j,b⟩
  intro u v h
  apply starRepresentative_parameter_injective a j
  cases b <;> simpa [starSignedRepresentative] using h

section Finite

variable [Fintype G]

def starBadParameters (a : Fin k → G) : Finset G :=
  starLinearExceptions a ∪ Finset.univ.filter (fun u ↦ u+u ∈ starDoubleExceptions a)

theorem starBadParameters_card_le (a : Fin k → G) (hodd : Odd (Fintype.card G)) :
    (starBadParameters a).card ≤ 1+4*k+3*k^2 := by
  let D := Finset.univ.filter (fun u : G ↦ u+u ∈ starDoubleExceptions a)
  have hD : D.card ≤ k+k^2 := by
    have hs : D.image (fun u ↦ u+u) ⊆ starDoubleExceptions a := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    calc
      D.card = (D.image (fun u ↦ u+u)).card :=
        (Finset.card_image_of_injective D (doubling_injective_of_odd hodd)).symm
      _ ≤ (starDoubleExceptions a).card := Finset.card_le_card hs
      _ ≤ k+k^2 := starDoubleExceptions_card_le a
  have hL := starLinearExceptions_card_le a
  have hu := Finset.card_union_le (starLinearExceptions a) D
  change (starLinearExceptions a ∪ D).card ≤ _
  omega

theorem starValid_of_not_mem_badParameters (a : Fin k → G) (hr : StarRoots a) (u : G)
    (hu : u ∉ starBadParameters a) : StarValid a u := by
  apply starValid_of_avoids_exceptions a hr u
  · exact fun h ↦ hu (Finset.mem_union_left _ h)
  · exact fun h ↦ hu (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))

/-- The failure count concerns the real signed-validity predicate. -/
theorem starInvalidParameters_card_le (a : Fin k → G) (hr : StarRoots a)
    (hk : k ≤ 3) (hodd : Odd (Fintype.card G)) :
    (Finset.univ.filter (fun u ↦ ¬StarValid a u)).card ≤ 40 := by
  have hb : (Finset.univ.filter (fun u ↦ ¬StarValid a u)) ⊆ starBadParameters a := by
    intro u hu
    by_contra hn
    exact (Finset.mem_filter.mp hu).2 (starValid_of_not_mem_badParameters a hr u hn)
  apply (Finset.card_le_card hb).trans ((starBadParameters_card_le a hodd).trans ?_)
  interval_cases k <;> norm_num

def starHitParameters (a : Fin k → G) (F : Finset G) : Finset G :=
  Finset.univ.biUnion (fun jb : Option (Fin k) × Bool ↦
    Finset.univ.filter (fun u ↦ starSignedRepresentative a u jb ∈ F))

theorem mem_starHitParameters (a : Fin k → G) (F : Finset G) (u : G) :
    u ∈ starHitParameters a F ↔ ¬Disjoint (starSupport a u) F := by
  simp only [starHitParameters, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter,
    true_and, Finset.not_disjoint_iff, starSupport, Finset.mem_image]
  constructor
  · rintro ⟨jb,h⟩
    exact ⟨starSignedRepresentative a u jb,⟨jb,rfl⟩,h⟩
  · rintro ⟨x,⟨jb,rfl⟩,hx⟩
    exact ⟨jb,hx⟩

theorem starHitParameters_card_le (a : Fin k → G) (F : Finset G) :
    (starHitParameters a F).card ≤ (2*(k+1))*F.card := by
  have hslot (jb : Option (Fin k) × Bool) :
      (Finset.univ.filter (fun u ↦ starSignedRepresentative a u jb ∈ F)).card ≤ F.card := by
    let S := Finset.univ.filter (fun u ↦ starSignedRepresentative a u jb ∈ F)
    have hs : S.image (fun u ↦ starSignedRepresentative a u jb) ⊆ F := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    calc
      S.card = (S.image (fun u ↦ starSignedRepresentative a u jb)).card :=
        (Finset.card_image_of_injective S
          (starSignedRepresentative_parameter_injective a jb)).symm
      _ ≤ F.card := Finset.card_le_card hs
  calc
    (starHitParameters a F).card ≤
        ∑ jb : Option (Fin k) × Bool,
          (Finset.univ.filter (fun u ↦ starSignedRepresentative a u jb ∈ F)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _jb : Option (Fin k) × Bool, F.card := Finset.sum_le_sum (fun jb _ ↦ hslot jb)
    _ = (2*(k+1))*F.card := by simp [Nat.mul_comm]

/-- A real parameter avoiding an arbitrary numerical set chosen later. -/
theorem exists_star_valid_avoiding (a : Fin k → G) (hr : StarRoots a) (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (F : Finset G)
    (hsize : 40+8*F.card < Fintype.card G) :
    ∃ u, StarValid a u ∧ Disjoint (starSupport a u) F := by
  let B := Finset.univ.filter (fun u ↦ ¬StarValid a u)
  have hb : B.card ≤ 40 := starInvalidParameters_card_le a hr hk hodd
  have hh : (starHitParameters a F).card ≤ 8*F.card :=
    (starHitParameters_card_le a F).trans (Nat.mul_le_mul_right _ (by omega))
  have hc : (B ∪ starHitParameters a F).card < (Finset.univ : Finset G).card :=
    (Finset.card_union_le _ _).trans_lt (by simpa using lt_of_le_of_lt (Nat.add_le_add hb hh) hsize)
  obtain ⟨u,_,hu⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hv : StarValid a u := by
    by_contra hv
    exact hu (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩))
  refine ⟨u,hv,?_⟩
  by_contra hd
  exact hu (Finset.mem_union_right _ ((mem_starHitParameters a F u).2 hd))

theorem exists_star_disjoint_packing (a : Fin k → G) (hr : StarRoots a) (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (M : ℕ) (hsize : 40+64*M < Fintype.card G) :
    ∃ U : Finset G, U.card = M ∧ (∀ u ∈ U, StarValid a u) ∧
      (U : Set G).Pairwise (fun u v ↦ Disjoint (starSupport a u) (starSupport a v)) := by
  induction M with
  | zero => exact ⟨∅,rfl,by simp,by simp⟩
  | succ M ih =>
    obtain ⟨U,hU,hv,hp⟩ := ih (by omega)
    let F := U.biUnion (starSupport a)
    have hF : F.card ≤ 8*M := by
      have hh := Finset.card_biUnion_le_card_mul U (starSupport a) 8
        (fun u _ ↦ (starSupport_card_le a u).trans (by omega))
      simpa [F,hU,Nat.mul_comm] using hh
    obtain ⟨u,hu,hd⟩ := exists_star_valid_avoiding a hr hk hodd F (by omega)
    have huU : u ∉ U := by
      intro hum
      have hrep := starRepresentative_mem_support a u none
      exact Finset.disjoint_left.mp hd hrep (Finset.mem_biUnion.mpr ⟨u,hum,hrep⟩)
    have hud (v : G) (hv : v ∈ U) : Disjoint (starSupport a u) (starSupport a v) := by
      apply Finset.disjoint_left.mpr
      intro x hxu hxv
      exact Finset.disjoint_left.mp hd hxu (Finset.mem_biUnion.mpr ⟨v,hv,hxv⟩)
    refine ⟨insert u U,by simp [huU,hU],?_,?_⟩
    · intro v hvm
      rcases Finset.mem_insert.mp hvm with rfl | hvU
      · exact hu
      · exact hv v hvU
    · intro v hvm w hwm hvw
      rcases Finset.mem_insert.mp hvm with rfl | hvU
      · rcases Finset.mem_insert.mp hwm with rfl | hwU
        · exact False.elim (hvw rfl)
        · exact hud w hwU
      · rcases Finset.mem_insert.mp hwm with rfl | hwU
        · exact (hud v hvU).symm
        · exact hp hvU hwU hvw

theorem exists_star_linear_orbit_packing (a : Fin k → G) (hr : StarRoots a) (hk : k ≤ 3)
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G) :
    ∃ U : Finset G, U.card = Fintype.card G/1000 ∧ (∀ u ∈ U, StarValid a u) ∧
      (U : Set G).Pairwise (fun u v ↦ Disjoint (starSupport a u) (starSupport a v)) := by
  apply exists_star_disjoint_packing a hr hk hodd
  omega

end Finite
end EndpointSelector.Stars
