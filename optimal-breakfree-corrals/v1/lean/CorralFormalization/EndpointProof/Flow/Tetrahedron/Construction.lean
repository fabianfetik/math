import CorralFormalization.EndpointProof.Matching.UniversalCore.BufferMatching

open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open EndpointMatching.AbsorptionAssembly
open EndpointMatching.UniversalCore
noncomputable section

abbrev Slot := Fin 3 × Fin 10

def rootSlots : Finset Slot := {(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)}
def addedSlots : Finset Slot := Finset.univ.filter (fun v => 2 ≤ v.2.val)
def outputSlots : Finset Slot := {(0,2),(1,4),(2,2)}

def edgeSlots : Fin 9 → Finset Slot := ![
  {(0,3),(1,3),(2,0)},
  {(0,5),(1,5),(2,1)},
  {(0,7),(1,0),(2,3)},
  {(0,9),(1,1),(2,5)},
  {(0,0),(1,7),(2,7)},
  {(0,1),(1,9),(2,9)},
  {(0,8),(1,2),(2,6)},
  {(0,4),(1,8),(2,4)},
  {(0,6),(1,6),(2,8)}]

theorem slots_partition :
    Finset.univ.biUnion edgeSlots = (rootSlots ∪ addedSlots) \ outputSlots := by
  decide

theorem slots_disjoint : ∀ i j : Fin 9, i ≠ j → Disjoint (edgeSlots i) (edgeSlots j) := by
  decide

theorem output_sub_added : outputSlots ⊆ addedSlots := by decide

theorem addedSlots_card : addedSlots.card = 24 := by decide

def slotFlip (s : Slot) : Slot := (s.1, (![0,1,3,2,5,4,7,6,9,8] : Fin 10 → Fin 10) s.2)

theorem slotFlip_added (s : Slot) (hs : s ∈ addedSlots) : slotFlip s ∈ addedSlots := by
  rcases s with ⟨p,j⟩
  fin_cases p <;> fin_cases j <;> simp_all [addedSlots, slotFlip]

theorem slotFlip_ne (s : Slot) (hs : s ∈ addedSlots) : slotFlip s ≠ s := by
  rcases s with ⟨p,j⟩
  fin_cases p <;> fin_cases j <;> simp_all [addedSlots, slotFlip]

variable {G : Type*} [AddCommGroup G]

/-- Coordinates for the twelve inverse-pair representatives in (PC4).
Index 0,1 in each part are the two roots; the remaining coordinates occur
in positive/negative pairs. -/
def coordinate (a1 a2 b1 b2 c1 c2 x y z : G) : Fin 3 → Fin 10 → G := ![
 ![a1,a2,c1+x+y,-(c1+x+y),x-z-b2,-(x-z-b2),y+z-a1-a2,-(y+z-a1-a2),x,-x],
 ![b1,b2,-x-y,-(-x-y),c2+b2-x+z,-(c2+b2-x+z),a1-y,-(a1-y),z,-z],
 ![c1,c2,b1+a1+a2-y-z,-(b1+a1+a2-y-z),b2-x,-(b2-x),y,-y,a2-z,-(a2-z)]
]

def place (a1 a2 b1 b2 c1 c2 x y z : G) (s : Slot) : Vertex G :=
  (s.1, coordinate a1 a2 b1 b2 c1 c2 x y z s.1 s.2)

theorem coordinate_flip (a1 a2 b1 b2 c1 c2 x y z : G)
    (s : Slot) (hs : s ∈ addedSlots) :
    place a1 a2 b1 b2 c1 c2 x y z (slotFlip s) =
      ((place a1 a2 b1 b2 c1 c2 x y z s).1,
        -(place a1 a2 b1 b2 c1 c2 x y z s).2) := by
  rcases s with ⟨p,j⟩
  fin_cases p <;> fin_cases j <;> simp_all [addedSlots, slotFlip, place, coordinate]
  all_goals abel

theorem actual_edges (a1 a2 b1 b2 c1 c2 x y z : G) (i : Fin 9) :
    Hyperedge ((edgeSlots i).image (place a1 a2 b1 b2 c1 c2 x y z)) := by
  fin_cases i <;> refine ⟨_,_,_,?_,rfl⟩ <;> simp [coordinate] <;> abel

/-- Physical roots, the 24 added tagged vertices, and the three outputs. -/
def roots (a1 a2 b1 b2 c1 c2 x y z : G) : Finset (Vertex G) :=
  rootSlots.image (place a1 a2 b1 b2 c1 c2 x y z)

def added (a1 a2 b1 b2 c1 c2 x y z : G) : Finset (Vertex G) :=
  addedSlots.image (place a1 a2 b1 b2 c1 c2 x y z)

def output (a1 a2 b1 b2 c1 c2 x y z : G) : Finset (Vertex G) :=
  outputSlots.image (place a1 a2 b1 b2 c1 c2 x y z)

theorem output_subset_added (a1 a2 b1 b2 c1 c2 x y z : G) :
    output a1 a2 b1 b2 c1 c2 x y z ⊆ added a1 a2 b1 b2 c1 c2 x y z :=
  Finset.image_subset_image output_sub_added

theorem added_paired (a1 a2 b1 b2 c1 c2 x y z : G) :
    ∀ v ∈ added a1 a2 b1 b2 c1 c2 x y z,
      (v.1,-v.2) ∈ added a1 a2 b1 b2 c1 c2 x y z := by
  intro v hv
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
  exact Finset.mem_image.mpr ⟨slotFlip s, slotFlip_added s hs,
    coordinate_flip a1 a2 b1 b2 c1 c2 x y z s hs⟩

theorem added_card (a1 a2 b1 b2 c1 c2 x y z : G)
    (hinj : Function.Injective (place a1 a2 b1 b2 c1 c2 x y z)) :
    (added a1 a2 b1 b2 c1 c2 x y z).card = 24 := by
  rw [added, Finset.card_image_of_injective _ hinj, addedSlots_card]

theorem roots_formula (a1 a2 b1 b2 c1 c2 x y z : G) :
    roots a1 a2 b1 b2 c1 c2 x y z =
      {(0,a1),(0,a2),(1,b1),(1,b2),(2,c1),(2,c2)} := by
  simp [roots, rootSlots, place, coordinate]

theorem output_formula (a1 a2 b1 b2 c1 c2 x y z : G) :
    output a1 a2 b1 b2 c1 c2 x y z =
      {(0,c1+x+y),(1,c2+b2-x+z),(2,b1+a1+a2-y-z)} := by
  simp [output, outputSlots, place, coordinate]

theorem output_onePerPart (a1 a2 b1 b2 c1 c2 x y z : G) :
    OnePerPart (output a1 a2 b1 b2 c1 c2 x y z) := by
  intro p
  fin_cases p <;> simp [output_formula]

theorem added_slice_card (a1 a2 b1 b2 c1 c2 x y z : G)
    (hinj : Function.Injective (place a1 a2 b1 b2 c1 c2 x y z))
    (p : Fin 3) : (slice (added a1 a2 b1 b2 c1 c2 x y z) p).card = 8 := by
  let f := place a1 a2 b1 b2 c1 c2 x y z
  have heq : slice (added a1 a2 b1 b2 c1 c2 x y z) p =
      (addedSlots.filter (fun s => s.1 = p)).image f := by
    ext v
    simp only [slice, added, Finset.mem_filter, Finset.mem_image]
    constructor
    · rintro ⟨⟨s,hs,rfl⟩,hv⟩
      exact ⟨s, ⟨hs,hv⟩, rfl⟩
    · rintro ⟨s,⟨hs,hp⟩,rfl⟩
      exact ⟨⟨s,hs,rfl⟩,hp⟩
  rw [heq, Finset.card_image_of_injective _ hinj]
  fin_cases p <;> decide

theorem added_nonzero_of_injective (a1 a2 b1 b2 c1 c2 x y z : G)
    (hinj : Function.Injective (place a1 a2 b1 b2 c1 c2 x y z)) :
    ∀ v ∈ added a1 a2 b1 b2 c1 c2 x y z, v.2 ≠ 0 := by
  intro v hv
  obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
  intro hz
  have he : place a1 a2 b1 b2 c1 c2 x y z (slotFlip s) =
      place a1 a2 b1 b2 c1 c2 x y z s := by
    rw [coordinate_flip a1 a2 b1 b2 c1 c2 x y z s hs]
    apply Prod.ext <;> simp [hz]
  exact slotFlip_ne s hs (hinj he)

/-- The nine actual zero-sum edges partition the six roots and all 24 new
vertices except the indicated output triple. -/
theorem matching_nine_edges (a1 a2 b1 b2 c1 c2 x y z : G)
    (hinj : Function.Injective (place a1 a2 b1 b2 c1 c2 x y z)) :
    Nonempty (Matching ((roots a1 a2 b1 b2 c1 c2 x y z ∪
      added a1 a2 b1 b2 c1 c2 x y z) \ output a1 a2 b1 b2 c1 c2 x y z)) := by
  let f := place a1 a2 b1 b2 c1 c2 x y z
  let V : Fin 9 → Finset (Vertex G) := fun i => (edgeSlots i).image f
  have hdis : ∀ i ∈ (Finset.univ : Finset (Fin 9)), ∀ j ∈ (Finset.univ : Finset (Fin 9)),
      i ≠ j → Disjoint (V i) (V j) := by
    intro i _ j _ hij
    apply Finset.disjoint_left.mpr
    intro v hv hv'
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp hv'
    have hst : t = s := hinj he
    subst t
    exact Finset.disjoint_left.mp (slots_disjoint i j hij) hs ht
  have hmatch : ∀ i ∈ (Finset.univ : Finset (Fin 9)), Nonempty (Matching (V i)) := by
    intro i _
    exact ⟨oneEdgeMatching _ (actual_edges a1 a2 b1 b2 c1 c2 x y z i)⟩
  obtain ⟨M⟩ := matching_biUnion Finset.univ V hdis hmatch
  have hcover : Finset.univ.biUnion V =
      (roots a1 a2 b1 b2 c1 c2 x y z ∪ added a1 a2 b1 b2 c1 c2 x y z) \
        output a1 a2 b1 b2 c1 c2 x y z := by
    change Finset.univ.biUnion (fun i => (edgeSlots i).image f) = _
    rw [← Finset.biUnion_image, slots_partition, Finset.image_sdiff _ _ hinj,
      Finset.image_union]
    rfl
  exact ⟨hcover ▸ M⟩

theorem output_sum (a1 a2 b1 b2 c1 c2 x y z : G) :
    (c1+x+y) + (c2+b2-x+z) + (b1+a1+a2-y-z) =
      a1+a2+b1+b2+c1+c2 := by abel

theorem output_coordinate_sum (a1 a2 b1 b2 c1 c2 x y z : G) :
    (∑ v ∈ output a1 a2 b1 b2 c1 c2 x y z, v.2) =
      a1+a2+b1+b2+c1+c2 := by
  rw [output_formula]
  simp only [Finset.sum_insert, Finset.sum_singleton, Finset.mem_insert,
    Finset.mem_singleton, Prod.mk.injEq, Fin.reduceEq, false_and, or_false,
    not_false_eq_true]
  abel

theorem roots_coordinate_sum (a1 a2 b1 b2 c1 c2 x y z : G)
    (hinj : Function.Injective (place a1 a2 b1 b2 c1 c2 x y z)) :
    (∑ v ∈ roots a1 a2 b1 b2 c1 c2 x y z, v.2) =
      a1+a2+b1+b2+c1+c2 := by
  have ha : a1 ≠ a2 := by
    intro h
    have he : ((0,0) : Slot) = (0,1) := hinj (by simp [place,coordinate,h])
    exact (by decide : (0 : Fin 10) ≠ 1) (congrArg Prod.snd he)
  have hb : b1 ≠ b2 := by
    intro h
    have he : ((1,0) : Slot) = (1,1) := hinj (by simp [place,coordinate,h])
    exact (by decide : (0 : Fin 10) ≠ 1) (congrArg Prod.snd he)
  have hc : c1 ≠ c2 := by
    intro h
    have he : ((2,0) : Slot) = (2,1) := hinj (by simp [place,coordinate,h])
    exact (by decide : (0 : Fin 10) ≠ 1) (congrArg Prod.snd he)
  rw [roots_formula]
  simp [ha,hb,hc]
  abel

/-- A single merge with four inverse pairs in each of the three parts.
Its Q-membership and freshness still come from a separately supplied valid
parameter triple. -/
structure FourPairMerge (Q : Vertex G → Prop) (R : Finset (Vertex G))
    (F : Finset G) where
  added : Finset (Vertex G)
  output : Finset (Vertex G)
  added_Q : ∀ v ∈ added, Q v
  added_paired : ∀ v ∈ added, (v.1,-v.2) ∈ added
  added_nonzero : ∀ v ∈ added, v.2 ≠ 0
  added_card : added.card = 24
  part_card : ∀ p : Fin 3, (slice added p).card = 8
  roots_fresh : Disjoint (support added) (support R)
  avoids : Disjoint (support added) F
  output_subset : output ⊆ added
  output_onePerPart : OnePerPart output
  output_sum : (∑ v ∈ output, v.2) = ∑ v ∈ R, v.2
  matching : Matching ((R ∪ added) \ output)

def tetrahedronMerge (Q : Vertex G → Prop) (F : Finset G)
    (a1 a2 b1 b2 c1 c2 x y z : G)
    (hinj : Function.Injective (place a1 a2 b1 b2 c1 c2 x y z))
    (hQ : ∀ v ∈ added a1 a2 b1 b2 c1 c2 x y z, Q v)
    (hfresh : Disjoint (support (added a1 a2 b1 b2 c1 c2 x y z))
      (support (roots a1 a2 b1 b2 c1 c2 x y z)))
    (havoid : Disjoint (support (added a1 a2 b1 b2 c1 c2 x y z)) F) :
    FourPairMerge Q (roots a1 a2 b1 b2 c1 c2 x y z) F where
  added := added a1 a2 b1 b2 c1 c2 x y z
  output := output a1 a2 b1 b2 c1 c2 x y z
  added_Q := hQ
  added_paired := added_paired a1 a2 b1 b2 c1 c2 x y z
  added_nonzero := added_nonzero_of_injective a1 a2 b1 b2 c1 c2 x y z hinj
  added_card := added_card a1 a2 b1 b2 c1 c2 x y z hinj
  part_card := added_slice_card a1 a2 b1 b2 c1 c2 x y z hinj
  roots_fresh := hfresh
  avoids := havoid
  output_subset := output_subset_added a1 a2 b1 b2 c1 c2 x y z
  output_onePerPart := output_onePerPart a1 a2 b1 b2 c1 c2 x y z
  output_sum := (output_coordinate_sum a1 a2 b1 b2 c1 c2 x y z).trans
    (roots_coordinate_sum a1 a2 b1 b2 c1 c2 x y z hinj).symm
  matching := Classical.choice (matching_nine_edges a1 a2 b1 b2 c1 c2 x y z hinj)

/-- A uniform supply of 24-vertex merges for every later admissible pair
of one-per-part root triples and every forbidden set within the budget. -/
def FourPairSupplier (Q : Vertex G → Prop) (budget : ℕ) : Prop :=
  ∀ (O X : Finset (Vertex G)) (F : Finset G),
    OnePerPart O → OnePerPart X → Disjoint O X →
    (∀ v ∈ O, v.2 ≠ 0) → (∀ v ∈ X, v.2 ≠ 0) → F.card ≤ budget →
      Nonempty (FourPairMerge Q (O ∪ X) F)

end
end EndpointMatching.Tetrahedron
