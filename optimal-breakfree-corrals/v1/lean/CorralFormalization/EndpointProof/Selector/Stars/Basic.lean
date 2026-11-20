import CorralFormalization.EndpointProof.Selector.TwoPairSwitch

/-!
# The actual small stars of endpoint supplement selector

A star on `k` A-root pairs occupies one B-pair and `k` C-pairs.  Its state
`i` covers only the common B-pair, C-pair `i`, and A-root pair `i`; the
other C-pairs are deliberately left for the independently supplied switches.
The full inverse support is numerical, and is disjoint from *all* A roots.
-/

open scoped Classical BigOperators

namespace EndpointSelector.Stars

variable {G : Type*} [CommRing G] [DecidableEq G] {k : ℕ}

/-- Distinct nonzero inverse pairs, with an explicit representative per pair. -/
def StarRoots (a : Fin k → G) : Prop :=
  (∀ i, a i ≠ 0) ∧ ∀ i j, i ≠ j → a i ≠ a j ∧ a i ≠ -a j

/-- `none` is the common B representative; `some i` is the C representative. -/
def starRepresentative (a : Fin k → G) (u : G) : Option (Fin k) → G
  | none => u
  | some i => -a i-u

def starSignedRepresentative (a : Fin k → G) (u : G)
    (jb : Option (Fin k) × Bool) : G :=
  if jb.2 then -starRepresentative a u jb.1 else starRepresentative a u jb.1

def starRootSupport (a : Fin k → G) : Finset G :=
  Finset.univ.image (fun ib : Fin k × Bool ↦ if ib.2 then -a ib.1 else a ib.1)

/-- Both signs of every newly inspected orbit, including unoccupied signs. -/
def starSupport (a : Fin k → G) (u : G) : Finset G :=
  Finset.univ.image (starSignedRepresentative a u)

@[simp] theorem mem_starRootSupport (a : Fin k → G) (x : G) :
    x ∈ starRootSupport a ↔ ∃ i, x = a i ∨ x = -a i := by
  simp only [starRootSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i,b⟩,h⟩
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
    · exact ⟨i,Or.inl h.symm⟩
    · exact ⟨i,Or.inr h.symm⟩
  · rintro ⟨i,h | h⟩
    · exact ⟨(i,false),by simpa using h.symm⟩
    · exact ⟨(i,true),by simpa using h.symm⟩

@[simp] theorem mem_starSupport (a : Fin k → G) (u x : G) :
    x ∈ starSupport a u ↔
      ∃ j, x = starRepresentative a u j ∨ x = -starRepresentative a u j := by
  simp only [starSupport, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨i,b⟩,h⟩
    cases b <;> simp only [starSignedRepresentative, Bool.false_eq_true, ↓reduceIte] at h
    · exact ⟨i,Or.inl h.symm⟩
    · exact ⟨i,Or.inr h.symm⟩
  · rintro ⟨i,h | h⟩
    · exact ⟨(i,false),by simpa [starSignedRepresentative] using h.symm⟩
    · exact ⟨(i,true),by simpa [starSignedRepresentative] using h.symm⟩

theorem starRepresentative_mem_support (a : Fin k → G) (u : G) (j : Option (Fin k)) :
    starRepresentative a u j ∈ starSupport a u :=
  (mem_starSupport a u _).2 ⟨j,Or.inl rfl⟩

theorem starSupport_neg_closed (a : Fin k → G) (u x : G) :
    -x ∈ starSupport a u ↔ x ∈ starSupport a u := by
  simp only [mem_starSupport]
  constructor <;> rintro ⟨j,h | h⟩
  · exact ⟨j,Or.inr (by simpa using congrArg Neg.neg h)⟩
  · exact ⟨j,Or.inl (by simpa using congrArg Neg.neg h)⟩
  · exact ⟨j,Or.inr (by simp [h])⟩
  · exact ⟨j,Or.inl (by simp [h])⟩

theorem starSupport_card_le (a : Fin k → G) (u : G) :
    (starSupport a u).card ≤ 2*(k+1) := by
  exact Finset.card_image_le.trans (by simp [Nat.mul_comm])

theorem starRootSupport_card_le (a : Fin k → G) :
    (starRootSupport a).card ≤ 2*k := by
  exact Finset.card_image_le.trans (by simp [Nat.mul_comm])

/-- Exact signed freshness, also from every target pair. -/
def StarValid (a : Fin k → G) (u : G) : Prop :=
  (∀ j, starRepresentative a u j ≠ 0) ∧
  (∀ i j, i ≠ j → starRepresentative a u i ≠ starRepresentative a u j ∧
    starRepresentative a u i ≠ -starRepresentative a u j) ∧
  Disjoint (starSupport a u) (starRootSupport a)

def starCommonPair (u : G) : Finset (Vertex G) := {(1,u),(1,-u)}

def starPair (a : Fin k → G) (u : G) (i : Fin k) : Finset (Vertex G) :=
  {(2,-a i-u),(2,a i+u)}

def starInterior (a : Fin k → G) (u : G) : Finset (Vertex G) :=
  starCommonPair u ∪ Finset.univ.biUnion (starPair a u)

def starState (a : Fin k → G) (u : G) (i : Fin k) :
    Fin 2 → Finset (Vertex G) :=
  ![edge (a i) u (-a i-u), edge (-a i) (-u) (a i+u)]

theorem starState_edges (a : Fin k → G) (u : G) (i : Fin k) (j : Fin 2) :
    IsHyperedge (starState a u i j) := by
  fin_cases j
  · exact ⟨a i,u,-a i-u,by ring,rfl⟩
  · exact ⟨-a i,-u,a i+u,by ring,rfl⟩

theorem starState_cover (a : Fin k → G) (u : G) (i : Fin k) :
    starState a u i 0 ∪ starState a u i 1 =
      (starCommonPair u ∪ starPair a u i) ∪ target (a i) := by
  ext x
  simp [starState,edge,starCommonPair,starPair,target]
  tauto

theorem starCommonPair_card [Fintype G] (hodd : Odd (Fintype.card G))
    (a : Fin k → G) (u : G) (hv : StarValid a u) : (starCommonPair u).card = 2 := by
  have hu : u ≠ -u := ne_neg_of_odd hodd (hv.1 none)
  simp [starCommonPair,hu]

theorem starPair_card [Fintype G] (hodd : Odd (Fintype.card G))
    (a : Fin k → G) (u : G) (hv : StarValid a u) (i : Fin k) :
    (starPair a u i).card = 2 := by
  have hc := ne_neg_of_odd hodd (hv.1 (some i))
  have hcc : -a i-u ≠ a i+u := by simpa [starRepresentative,add_comm] using hc
  simp [starPair,hcc]

theorem starInterior_card_le (a : Fin k → G) (u : G) :
    (starInterior a u).card ≤ 2+2*k := by
  have hB : (starCommonPair u).card ≤ 2 := Finset.card_le_two
  have hC : (Finset.univ.biUnion (starPair a u)).card ≤ 2*k := by
    simpa [Nat.mul_comm] using Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin k)) (starPair a u) 2
      (fun i _ ↦ Finset.card_le_two)
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add hB hC)

theorem starCommonPair_subset_interior (a : Fin k → G) (u : G) :
    starCommonPair u ⊆ starInterior a u := Finset.subset_union_left

theorem starPair_subset_interior (a : Fin k → G) (u : G) (i : Fin k) :
    starPair a u i ⊆ starInterior a u := by
  intro v hv
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hv⟩)

theorem starInterior_disjoint_target (a : Fin k → G) (u c : G) :
    Disjoint (starInterior a u) (target c) := by
  apply Finset.disjoint_left.mpr
  intro v hv ht
  simp only [starInterior, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, starCommonPair, starPair,
    Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | ⟨i,hv⟩
  · rcases hv with rfl | rfl <;> simp [target] at ht
  · rcases hv with rfl | rfl <;> simp [target] at ht

theorem starInterior_coordinates (a : Fin k → G) (u : G) {v : Vertex G}
    (hv : v ∈ starInterior a u) : v.2 ∈ starSupport a u := by
  simp only [starInterior, Finset.mem_union, Finset.mem_biUnion,
    Finset.mem_univ, true_and, starCommonPair, starPair,
    Finset.mem_insert, Finset.mem_singleton] at hv
  rcases hv with hv | ⟨i,hv⟩
  · rcases hv with rfl | rfl
    · exact (mem_starSupport _ _ _).2 ⟨none,Or.inl rfl⟩
    · exact (mem_starSupport _ _ _).2 ⟨none,Or.inr rfl⟩
  · rcases hv with rfl | rfl
    · exact (mem_starSupport _ _ _).2 ⟨some i,Or.inl rfl⟩
    · exact (mem_starSupport _ _ _).2 ⟨some i,Or.inr (by simp [starRepresentative,add_comm])⟩

/-- The occupied star is itself closed under numerical inverses. -/
theorem starInterior_inverse_closure (a : Fin k → G) (u : G) :
    (starInterior a u).image Prod.snd ∪
      (starInterior a u).image (fun x ↦ -x.2) = starSupport a u := by
  ext x
  constructor
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
      exact starInterior_coordinates a u hv
    · obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hx
      exact (starSupport_neg_closed _ _ _).2 (starInterior_coordinates a u hv)
  · intro hx
    obtain ⟨j,hx | hx⟩ := (mem_starSupport _ _ _).1 hx
    all_goals cases j with
    | none =>
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      first
      | exact ⟨(1,u),starCommonPair_subset_interior a u (by simp [starCommonPair]),hx.symm⟩
      | exact ⟨(1,-u),starCommonPair_subset_interior a u (by simp [starCommonPair]),hx.symm⟩
    | some i =>
      apply Finset.mem_union_left
      apply Finset.mem_image.mpr
      first
      | exact ⟨(2,-a i-u),starPair_subset_interior a u i (by simp [starPair]),hx.symm⟩
      | exact ⟨(2,a i+u),starPair_subset_interior a u i (by simp [starPair]),
          by simpa [starRepresentative,add_comm] using hx.symm⟩

theorem starPair_rootCondition (a : Fin k → G) (u : G) (hv : StarValid a u)
    (i j : Fin k) (hij : i ≠ j) : RootCondition (-a i-u) (-a j-u) :=
  ⟨hv.1 (some i),hv.1 (some j),
    (hv.2.1 (some i) (some j) (by simpa using hij)).1,
    (hv.2.1 (some i) (some j) (by simpa using hij)).2⟩

/-- The star state is a real matching on its unique selected C pair and A root.
Switches must cover the other C pairs. -/
theorem star_state_matching [Fintype G] (hodd : Odd (Fintype.card G))
    (a : Fin k → G) (hr : StarRoots a) (u : G) (hv : StarValid a u) (i : Fin k) :
    IsTwoEdgeMatchingOn (starState a u i)
      ((starCommonPair u ∪ starPair a u i) ∪ target (a i)) := by
  refine ⟨starState_edges a u i,?_,starState_cover a u i⟩
  change Disjoint (edge (a i) u (-a i-u)) (edge (-a i) (-u) (a i+u))
  apply (edge_disjoint_iff _ _ _ _ _ _).2
  refine ⟨ne_neg_of_odd hodd (hr.1 i),ne_neg_of_odd hodd (hv.1 none),?_⟩
  simpa [starRepresentative,add_comm] using ne_neg_of_odd hodd (hv.1 (some i))

end EndpointSelector.Stars
