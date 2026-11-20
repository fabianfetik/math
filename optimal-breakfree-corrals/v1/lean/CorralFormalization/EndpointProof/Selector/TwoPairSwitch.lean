import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# The concrete two-pair selector in endpoint supplement selector

This file proves deterministic facts about the actual four affine coordinates
`u, u+a+b, -a-u, -b-u`. It does not assume a packing or a successful random
sample. The packing below is constructed from the parameter count.
-/

open scoped Classical BigOperators

namespace EndpointSelector

set_option maxHeartbeats 1500000

section Algebra

variable {G : Type*} [CommRing G] [DecidableEq G]

/-- The root condition means distinct nonzero inverse pairs. -/
def RootCondition (a b : G) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ a ≠ -b

/-- The four actual interior coordinates, in B,B,C,C order. -/
def representative (a b u : G) : Fin 4 → G :=
  ![u, u+a+b, -a-u, -b-u]

def roots (a b : G) : Finset G := {a, -a, b, -b}

def signedRepresentative (a b u : G) (jb : Fin 4 × Bool) : G :=
  if jb.2 then -representative a b u jb.1 else representative a b u jb.1

/-- Numerical support, including both signs even if only one sign is occupied. -/
def orbitSupport (a b u : G) : Finset G :=
  Finset.univ.image (signedRepresentative a b u)

@[simp] theorem mem_orbitSupport (a b u x : G) :
    x ∈ orbitSupport a b u ↔
      ∃ j, x = representative a b u j ∨ x = -representative a b u j := by
  simp only [orbitSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨j,t⟩, h⟩
    cases t
    · exact ⟨j, Or.inl (by simpa [signedRepresentative] using h.symm)⟩
    · exact ⟨j, Or.inr (by simpa [signedRepresentative] using h.symm)⟩
  · rintro ⟨j, h | h⟩
    · exact ⟨(j,false), by simpa [signedRepresentative] using h.symm⟩
    · exact ⟨(j,true), by simpa [signedRepresentative] using h.symm⟩

theorem representative_mem_support (a b u : G) (j : Fin 4) :
    representative a b u j ∈ orbitSupport a b u := by
  exact (mem_orbitSupport _ _ _ _).2 ⟨j, Or.inl rfl⟩

theorem orbitSupport_card_le (a b u : G) : (orbitSupport a b u).card ≤ 8 := by
  exact (Finset.card_image_le).trans (by simp)

/-- Freshness is numerical and includes every sign of both roots. -/
def Valid (a b u : G) : Prop :=
  (∀ j, representative a b u j ≠ 0) ∧
  (∀ i j : Fin 4, i ≠ j →
    representative a b u i ≠ representative a b u j ∧
    representative a b u i ≠ -representative a b u j) ∧
  Disjoint (orbitSupport a b u) (roots a b)

/-- Twelve explicit unit-coefficient exclusions suffice for zeros and roots. -/
def linearExceptions (a b : G) : Finset G :=
  ([0, -(a+b), -a, -b, a, b, -(a+a+b), -(a+b+b), -(a+a), b-a, a-b, -(b+b)] :
    List G).toFinset

/-- Five explicit double-coefficient exclusions suffice for signed collisions. -/
def doubleExceptions (a b : G) : Finset G :=
  ([-(a+b), -a, -b, -(a+a+b), -(a+b+b)] : List G).toFinset

theorem linearExceptions_card_le (a b : G) : (linearExceptions a b).card ≤ 12 := by
  exact ([0, -(a+b), -a, -b, a, b, -(a+a+b), -(a+b+b), -(a+a), b-a, a-b, -(b+b)] : List G).toFinset_card_le

theorem doubleExceptions_card_le (a b : G) : (doubleExceptions a b).card ≤ 5 := by
  exact ([-(a+b), -a, -b, -(a+a+b), -(a+b+b)] : List G).toFinset_card_le

/-- These are actual sufficient exclusions, not a count assumption. -/
theorem valid_of_avoids_exceptions (a b u : G) (hr : RootCondition a b)
    (hlinear : u ∉ linearExceptions a b)
    (hdouble : u+u ∉ doubleExceptions a b) : Valid a b u := by
  rcases hr with ⟨ha, hb, hab, han⟩
  simp only [linearExceptions, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hlinear
  rcases hlinear with ⟨hL0,hL1,hL2,hL3,hL4,hL5,hL6,hL7,hL8,hL9,hL10,hL11⟩
  simp only [doubleExceptions, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false, not_or] at hdouble
  rcases hdouble with ⟨hD0,hD1,hD2,hD3,hD4⟩
  have collision (i j : Fin 4) (hij : i ≠ j) :
      representative a b u i ≠ representative a b u j ∧
      representative a b u i ≠ -representative a b u j := by
    fin_cases i <;> fin_cases j <;> simp_all only [ne_eq, not_true_eq_false]
    all_goals constructor <;> intro h
    all_goals norm_num [representative] at h
    all_goals first
      | (apply ha; linear_combination h)
      | (apply ha; linear_combination -h)
      | (apply hb; linear_combination h)
      | (apply hb; linear_combination -h)
      | (apply hab; linear_combination h)
      | (apply hab; linear_combination -h)
      | (apply han; linear_combination h)
      | (apply han; linear_combination -h)
      | (apply hD0; linear_combination h)
      | (apply hD0; linear_combination -h)
      | (apply hD1; linear_combination h)
      | (apply hD1; linear_combination -h)
      | (apply hD2; linear_combination h)
      | (apply hD2; linear_combination -h)
      | (apply hD3; linear_combination h)
      | (apply hD3; linear_combination -h)
      | (apply hD4; linear_combination h)
      | (apply hD4; linear_combination -h)
  refine ⟨?_, collision, ?_⟩
  · intro j h
    fin_cases j
    all_goals norm_num [representative] at h
    · exact hL0 h
    · apply hL1; linear_combination h
    · apply hL2; linear_combination -h
    · apply hL3; linear_combination -h
  · apply Finset.disjoint_left.mpr
    intro x hx hroot
    obtain ⟨j, hx | hx⟩ := (mem_orbitSupport _ _ _ _).mp hx
    all_goals fin_cases j
    all_goals simp only [roots, Finset.mem_insert, Finset.mem_singleton] at hroot
    all_goals rcases hroot with hroot | hroot | hroot | hroot
    all_goals norm_num [representative] at hx
    all_goals have h := hx.symm.trans hroot
    all_goals first
      | (apply hL0; linear_combination h)
      | (apply hL0; linear_combination -h)
      | (apply hL1; linear_combination h)
      | (apply hL1; linear_combination -h)
      | (apply hL2; linear_combination h)
      | (apply hL2; linear_combination -h)
      | (apply hL3; linear_combination h)
      | (apply hL3; linear_combination -h)
      | (apply hL4; linear_combination h)
      | (apply hL4; linear_combination -h)
      | (apply hL5; linear_combination h)
      | (apply hL5; linear_combination -h)
      | (apply hL6; linear_combination h)
      | (apply hL6; linear_combination -h)
      | (apply hL7; linear_combination h)
      | (apply hL7; linear_combination -h)
      | (apply hL8; linear_combination h)
      | (apply hL8; linear_combination -h)
      | (apply hL9; linear_combination h)
      | (apply hL9; linear_combination -h)
      | (apply hL10; linear_combination h)
      | (apply hL10; linear_combination -h)
      | (apply hL11; linear_combination h)
      | (apply hL11; linear_combination -h)

omit [DecidableEq G] in
theorem representative_parameter_injective (a b : G) (j : Fin 4) :
    Function.Injective (fun u ↦ representative a b u j) := by
  intro u v h
  fin_cases j
  all_goals norm_num [representative] at h
  all_goals exact h

theorem signedRepresentative_parameter_injective (a b : G) (jb : Fin 4 × Bool) :
    Function.Injective (fun u ↦ signedRepresentative a b u jb) := by
  rcases jb with ⟨j,t⟩
  intro u v h
  apply representative_parameter_injective a b j
  cases t <;> simpa [signedRepresentative] using h

section Counting

variable [Fintype G]

omit [DecidableEq G] in
theorem doubling_injective_of_odd (hodd : Odd (Fintype.card G)) :
    Function.Injective (fun x : G ↦ x+x) := by
  have hc : (Nat.card G).Coprime 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hodd.coprime_two_right
  simpa only [two_nsmul] using hc.nsmul_right_bijective.injective

def badParameters (a b : G) : Finset G :=
  linearExceptions a b ∪
    Finset.univ.filter (fun u ↦ u+u ∈ doubleExceptions a b)

/-- The explicit exceptional set has size at most 17 over every finite odd ring. -/
theorem badParameters_card_le (a b : G) (hodd : Odd (Fintype.card G)) :
    (badParameters a b).card ≤ 17 := by
  let D := Finset.univ.filter (fun u : G ↦ u+u ∈ doubleExceptions a b)
  have hD : D.card ≤ 5 := by
    have hs : D.image (fun u ↦ u+u) ⊆ doubleExceptions a b := by
      intro x hx
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    calc
      D.card = (D.image (fun u ↦ u+u)).card :=
        (Finset.card_image_of_injective D (doubling_injective_of_odd hodd)).symm
      _ ≤ (doubleExceptions a b).card := Finset.card_le_card hs
      _ ≤ 5 := doubleExceptions_card_le a b
  exact (Finset.card_union_le _ _).trans (by
    have hL := linearExceptions_card_le a b
    change (linearExceptions a b).card + D.card ≤ 17
    omega)

theorem valid_of_not_mem_badParameters (a b u : G) (hr : RootCondition a b)
    (hu : u ∉ badParameters a b) : Valid a b u := by
  apply valid_of_avoids_exceptions a b u hr
  · intro h
    exact hu (Finset.mem_union_left _ h)
  · intro h
    apply hu
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)

/-- This bound concerns the failure of the actual validity predicate. -/
theorem invalidParameters_card_le (a b : G) (hr : RootCondition a b)
    (hodd : Odd (Fintype.card G)) :
    (Finset.univ.filter (fun u ↦ ¬Valid a b u)).card ≤ 17 := by
  apply (Finset.card_le_card ?_).trans (badParameters_card_le a b hodd)
  intro u hu
  by_contra hbad
  exact (Finset.mem_filter.mp hu).2 (valid_of_not_mem_badParameters a b u hr hbad)

def hitParameters (a b : G) (F : Finset G) : Finset G :=
  Finset.univ.biUnion (fun jb : Fin 4 × Bool ↦
    Finset.univ.filter (fun u ↦ signedRepresentative a b u jb ∈ F))

theorem mem_hitParameters (a b u : G) (F : Finset G) :
    u ∈ hitParameters a b F ↔ ¬Disjoint (orbitSupport a b u) F := by
  simp only [hitParameters, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter,
    true_and, Finset.not_disjoint_iff, orbitSupport, Finset.mem_image]
  constructor
  · rintro ⟨jb,h⟩
    exact ⟨signedRepresentative a b u jb, ⟨jb, rfl⟩, h⟩
  · rintro ⟨x, ⟨jb,rfl⟩,hx⟩
    exact ⟨jb,hx⟩

/-- Forbidding any numerical set costs at most eight parameters per coordinate. -/
theorem hitParameters_card_le (a b : G) (F : Finset G) :
    (hitParameters a b F).card ≤ 8 * F.card := by
  have hslot (jb : Fin 4 × Bool) :
      (Finset.univ.filter (fun u ↦ signedRepresentative a b u jb ∈ F)).card ≤ F.card := by
    let S := Finset.univ.filter (fun u ↦ signedRepresentative a b u jb ∈ F)
    have hs : S.image (fun u ↦ signedRepresentative a b u jb) ⊆ F := by
      intro x hx
      obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_filter.mp hu).2
    calc
      S.card = (S.image (fun u ↦ signedRepresentative a b u jb)).card :=
        (Finset.card_image_of_injective S
          (signedRepresentative_parameter_injective a b jb)).symm
      _ ≤ F.card := Finset.card_le_card hs
  calc
    (hitParameters a b F).card ≤
        ∑ jb : Fin 4 × Bool,
          (Finset.univ.filter (fun u ↦ signedRepresentative a b u jb ∈ F)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _jb : Fin 4 × Bool, F.card := Finset.sum_le_sum (fun jb _ ↦ hslot jb)
    _ = 8 * F.card := by simp

/-- A real fresh switch parameter, with every excluded coordinate charged. -/
theorem exists_valid_avoiding (a b : G) (hr : RootCondition a b)
    (hodd : Odd (Fintype.card G)) (F : Finset G)
    (hsize : 17 + 8 * F.card < Fintype.card G) :
    ∃ u, Valid a b u ∧ Disjoint (orbitSupport a b u) F := by
  have hc : (badParameters a b ∪ hitParameters a b F).card < (Finset.univ : Finset G).card := by
    apply lt_of_le_of_lt (Finset.card_union_le _ _) ?_
    exact lt_of_le_of_lt (Nat.add_le_add (badParameters_card_le a b hodd)
      (hitParameters_card_le a b F)) (by simpa using hsize)
  obtain ⟨u, _, hu⟩ := Finset.exists_mem_notMem_of_card_lt_card hc
  have hb : u ∉ badParameters a b := fun h ↦ hu (Finset.mem_union_left _ h)
  have hh : u ∉ hitParameters a b F := fun h ↦ hu (Finset.mem_union_right _ h)
  exact ⟨u, valid_of_not_mem_badParameters a b u hr hb,
    by simpa [mem_hitParameters] using hh⟩

/-- The actual parameter supply, with no packing or local-degree premise.
The conservative numerical-support accounting costs 64 per earlier switch. -/
theorem exists_disjoint_packing (a b : G) (hr : RootCondition a b)
    (hodd : Odd (Fintype.card G)) (M : ℕ)
    (hsize : 17 + 64 * M < Fintype.card G) :
    ∃ U : Finset G, U.card = M ∧
      (∀ u ∈ U, Valid a b u) ∧
      (U : Set G).Pairwise (fun u v ↦ Disjoint (orbitSupport a b u) (orbitSupport a b v)) := by
  induction M with
  | zero => exact ⟨∅, rfl, by simp, by simp⟩
  | succ M ih =>
    obtain ⟨U,hU,hvalid,hpair⟩ := ih (by omega)
    let F := U.biUnion (orbitSupport a b)
    have hF : F.card ≤ 8 * M := by
      have hh := Finset.card_biUnion_le_card_mul U (orbitSupport a b) 8
        (fun u _ ↦ orbitSupport_card_le a b u)
      simpa [F,hU,Nat.mul_comm] using hh
    obtain ⟨u, hu, hd⟩ := exists_valid_avoiding a b hr hodd F (by omega)
    have huU : u ∉ U := by
      intro hum
      have hrep := representative_mem_support a b u 0
      exact Finset.disjoint_left.mp hd hrep (Finset.mem_biUnion.mpr ⟨u,hum,hrep⟩)
    have hud (v : G) (hv : v ∈ U) :
        Disjoint (orbitSupport a b u) (orbitSupport a b v) := by
      apply Finset.disjoint_left.mpr
      intro x hxu hxv
      exact Finset.disjoint_left.mp hd hxu (Finset.mem_biUnion.mpr ⟨v,hv,hxv⟩)
    refine ⟨insert u U, by simp [huU,hU], ?_, ?_⟩
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact hu
      · exact hvalid v hv
    · intro v hv w hw hvw
      rcases Finset.mem_insert.mp hv with rfl | hvU
      · rcases Finset.mem_insert.mp hw with rfl | hwU
        · exact False.elim (hvw rfl)
        · exact hud w hwU
      · rcases Finset.mem_insert.mp hw with rfl | hwU
        · exact (hud v hvU).symm
        · exact hpair hvU hwU hvw

/-- In particular the supplement's requested floor(n/1000) is really supplied. -/
theorem exists_linear_orbit_packing (a b : G) (hr : RootCondition a b)
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G) :
    ∃ U : Finset G, U.card = Fintype.card G / 1000 ∧
      (∀ u ∈ U, Valid a b u) ∧
      (U : Set G).Pairwise (fun u v ↦ Disjoint (orbitSupport a b u) (orbitSupport a b v)) := by
  apply exists_disjoint_packing a b hr hodd
  omega

end Counting

end Algebra

section Matchings

variable {G : Type*} [CommRing G] [DecidableEq G]

abbrev Vertex (G : Type*) := Fin 3 × G

/-- A tagged tripartite edge in the supplement's zero-sum hypergraph. -/
def edge (x y z : G) : Finset (Vertex G) := {(0,x),(1,y),(2,z)}

def IsHyperedge (E : Finset (Vertex G)) : Prop :=
  ∃ x y z : G, x+y+z = 0 ∧ E = edge x y z

def interior (a b u : G) : Finset (Vertex G) :=
  {(1,u),(1,u+a+b),(2,-a-u),(2,-b-u)}

def target (a : G) : Finset (Vertex G) := {(0,a),(0,-a)}

def leftState (a b u : G) : Fin 2 → Finset (Vertex G) :=
  ![edge a u (-a-u), edge (-a) (u+a+b) (-b-u)]

def rightState (a b u : G) : Fin 2 → Finset (Vertex G) :=
  ![edge b u (-b-u), edge (-b) (u+a+b) (-a-u)]

/-- Two actual hyperedges, pairwise disjoint, covering exactly the stated set. -/
def IsTwoEdgeMatchingOn (E : Fin 2 → Finset (Vertex G))
    (S : Finset (Vertex G)) : Prop :=
  (∀ i, IsHyperedge (E i)) ∧ Disjoint (E 0) (E 1) ∧ E 0 ∪ E 1 = S

omit [CommRing G] in
theorem edge_disjoint_iff (x y z x' y' z' : G) :
    Disjoint (edge x y z) (edge x' y' z') ↔ x ≠ x' ∧ y ≠ y' ∧ z ≠ z' := by
  simp [edge, Finset.disjoint_left]

theorem leftState_edges (a b u : G) (i : Fin 2) : IsHyperedge (leftState a b u i) := by
  fin_cases i
  · exact ⟨a,u,-a-u,by ring,rfl⟩
  · exact ⟨-a,u+a+b,-b-u,by ring,rfl⟩

theorem rightState_edges (a b u : G) (i : Fin 2) : IsHyperedge (rightState a b u i) := by
  fin_cases i
  · exact ⟨b,u,-b-u,by ring,rfl⟩
  · exact ⟨-b,u+a+b,-a-u,by ring,rfl⟩

theorem leftState_cover (a b u : G) :
    leftState a b u 0 ∪ leftState a b u 1 = interior a b u ∪ target a := by
  ext x
  simp [leftState,edge,interior,target]
  tauto

theorem rightState_cover (a b u : G) :
    rightState a b u 0 ∪ rightState a b u 1 = interior a b u ∪ target b := by
  ext x
  simp [rightState,edge,interior,target]
  tauto

theorem interior_disjoint_target (a b u c : G) :
    Disjoint (interior a b u) (target c) := by
  simp [interior,target,Finset.disjoint_left]

/-- Exactly the full inverse closure of occupied interior coordinates is reserved. -/
theorem interior_inverse_closure (a b u : G) :
    (interior a b u).image Prod.snd ∪ (interior a b u).image (fun x ↦ -x.2) =
      orbitSupport a b u := by
  ext x
  simp [mem_orbitSupport, interior, representative, Fin.exists_fin_succ]
  tauto

theorem interior_card (a b u : G) (hv : Valid a b u) : (interior a b u).card = 4 := by
  have hB : u ≠ u+a+b := (hv.2.1 0 1 (by decide)).1
  have hC : -a-u ≠ -b-u := (hv.2.1 2 3 (by decide)).1
  simp [interior, hB,hC]

theorem ne_neg_of_odd [Fintype G] (hodd : Odd (Fintype.card G))
    {x : G} (hx : x ≠ 0) : x ≠ -x := by
  intro h
  apply hx
  apply doubling_injective_of_odd hodd
  calc
    x+x = x+(-x) := congrArg (fun y ↦ x+y) h
    _ = 0+0 := by simp

/-- Both switch choices give exact matchings on one common four-vertex interior. -/
theorem two_pair_switch [Fintype G] (a b u : G)
    (hr : RootCondition a b) (hodd : Odd (Fintype.card G)) (hv : Valid a b u) :
    (interior a b u).card = 4 ∧
    Disjoint (interior a b u) (target a) ∧
    Disjoint (interior a b u) (target b) ∧
    IsTwoEdgeMatchingOn (leftState a b u) (interior a b u ∪ target a) ∧
    IsTwoEdgeMatchingOn (rightState a b u) (interior a b u ∪ target b) := by
  have hB : u ≠ u+a+b := (hv.2.1 0 1 (by decide)).1
  have hC : -a-u ≠ -b-u := (hv.2.1 2 3 (by decide)).1
  refine ⟨interior_card a b u hv, interior_disjoint_target a b u a,
    interior_disjoint_target a b u b, ?_, ?_⟩
  · refine ⟨leftState_edges a b u, ?_, leftState_cover a b u⟩
    change Disjoint (edge a u (-a-u)) (edge (-a) (u+a+b) (-b-u))
    exact (edge_disjoint_iff _ _ _ _ _ _).2 ⟨ne_neg_of_odd hodd hr.1,hB,hC⟩
  · refine ⟨rightState_edges a b u, ?_, rightState_cover a b u⟩
    change Disjoint (edge b u (-b-u)) (edge (-b) (u+a+b) (-a-u))
    exact (edge_disjoint_iff _ _ _ _ _ _).2 ⟨ne_neg_of_odd hodd hr.2.1,hB,(Ne.symm hC)⟩

end Matchings

theorem cyclic_switch_supply {n : ℕ} [NeZero n] (hodd : Odd n) (hn : 1000 ≤ n)
    (a b : ZMod n) (hr : RootCondition a b) :
    ∃ U : Finset (ZMod n), U.card = n / 1000 ∧
      (∀ u ∈ U, Valid a b u ∧
        IsTwoEdgeMatchingOn (leftState a b u) (interior a b u ∪ target a) ∧
        IsTwoEdgeMatchingOn (rightState a b u) (interior a b u ∪ target b)) ∧
      (U : Set (ZMod n)).Pairwise
        (fun u v ↦ Disjoint (orbitSupport a b u) (orbitSupport a b v)) := by
  have ho : Odd (Fintype.card (ZMod n)) := by simpa only [ZMod.card] using hodd
  obtain ⟨U,hU,hvalid,hdisj⟩ := exists_linear_orbit_packing a b hr ho (by simpa using hn)
  refine ⟨U, by simpa only [ZMod.card] using hU, ?_, hdisj⟩
  intro u hu
  have hv := hvalid u hu
  have hm := two_pair_switch a b u hr ho hv
  exact ⟨hv,hm.2.2.2⟩

end EndpointSelector
