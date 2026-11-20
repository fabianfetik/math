import CorralFormalization.EndpointProof.Flow.Tetrahedron.ValidityCounts
open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open EndpointFlow.AbelianTransport
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

omit [Fintype G] in
theorem geometricallyValid_pair (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (h : geometricallyValid r t) (i j : Fin 12) (hij : i ≠ j) :
    tetrahedronRepresentative r i t ≠ tetrahedronRepresentative r j t ∧
      tetrahedronRepresentative r i t ≠ -tetrahedronRepresentative r j t := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact h.2.1 i j hlt
  · have hp := h.2.1 j i hgt
    constructor
    · exact hp.1.symm
    · intro he
      apply hp.2
      simpa using (congrArg Neg.neg he).symm

theorem signed_representatives_injective (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (h : geometricallyValid r t) :
    Function.Injective (fun ib : Fin 12 × Bool =>
      flipGroup ib.2 (tetrahedronRepresentative r ib.1 t)) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  by_cases hij : i = j
  · subst j
    have hn := ne_neg_of_odd hodd (h.1 i)
    cases b <;> cases c <;> simp_all [flipGroup, neg_eq_iff_eq_neg]
  · have hp := geometricallyValid_pair r t h i j hij
    cases b <;> cases c <;> simp_all [flipGroup, neg_eq_iff_eq_neg]

def rootSlot : Fin 6 → Slot := ![(0,0),(0,1),(1,0),(1,1),(2,0),(2,1)]

theorem rootSlots_eq_image : (Finset.univ : Finset (Fin 6)).image rootSlot = rootSlots := by decide

theorem rootSlot_injective : Function.Injective rootSlot := by decide

theorem allSlots_partition : rootSlots ∪ addedSlots = Finset.univ := by decide

theorem rootSlots_disjoint_addedSlots : Disjoint rootSlots addedSlots := by decide

omit [Fintype G] in
theorem rootSlot_coordinate (r : TetrahedronRoots G) (t : TetrahedronParameters G) (k : Fin 6) :
    (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (rootSlot k)).2 =
      rootCoordinate r k := by
  fin_cases k <;> simp [place, coordinate, rootSlot, rootCoordinate]

omit [Fintype G] in
theorem rootSlot_place_injective (r : TetrahedronRoots G) (hr : admissibleRoots r)
    (t : TetrahedronParameters G) :
    Function.Injective (fun k : Fin 6 =>
      place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (rootSlot k)) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all [place, coordinate, rootSlot, admissibleRoots]

omit [Fintype G] in
theorem signedSlot_coordinate (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (ib : Fin 12 × Bool) :
    (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (signedSlot ib)).2 =
      flipGroup ib.2 (tetrahedronRepresentative r ib.1 t) := by
  rcases ib with ⟨i,b⟩
  cases b
  · simpa [signedSlot, flipGroup] using representativeSlot_value r t i
  · have hflip := congrArg Prod.snd (coordinate_flip r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂
      t.1 t.2.1 t.2.2 (representativeSlot i) (representativeSlot_mem_added i))
    simpa only [signedSlot, flipGroup, ↓reduceIte, representativeSlot_value] using hflip

omit [Fintype G] in
theorem signed_rep_ne_signed_root (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (h : geometricallyValid r t) (i : Fin 12) (k : Fin 6) (b c : Bool) :
    flipGroup b (tetrahedronRepresentative r i t) ≠ flipGroup c (rootCoordinate r k) := by
  have hp := h.2.2 i k
  cases b <;> cases c <;> simp_all [flipGroup, neg_eq_iff_eq_neg]

omit [Fintype G] in
/-- A valid new signed representative cannot share a numerical coordinate
with any of the six roots. -/
theorem added_root_coordinates_disjoint (r : TetrahedronRoots G)
    (t : TetrahedronParameters G) (h : geometricallyValid r t)
    (s u : Slot) (hs : s ∈ addedSlots) (hu : u ∈ rootSlots) :
    (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 s).2 ≠
      (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 u).2 := by
  rw [← signedSlots_eq_added] at hs
  obtain ⟨⟨i,b⟩,_,rfl⟩ := Finset.mem_image.mp hs
  rw [← rootSlots_eq_image] at hu
  obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hu
  rw [signedSlot_coordinate, rootSlot_coordinate]
  simpa [flipGroup] using signed_rep_ne_signed_root r t h i k b false

/-- The 30 tagged positions in PC4 are injective under the strong geometric
validity conditions and the paper's admissible-root assumptions. -/
theorem geometricallyValid_place_injective (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (t : TetrahedronParameters G)
    (h : geometricallyValid r t) :
    Function.Injective (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) := by
  intro s u he
  have hrOrAdded (v : Slot) : v ∈ rootSlots ∨ v ∈ addedSlots := by
    have hv : v ∈ rootSlots ∪ addedSlots := by rw [allSlots_partition]; simp
    exact Finset.mem_union.mp hv
  by_cases hs : s ∈ addedSlots
  · by_cases hu : u ∈ addedSlots
    · rw [← signedSlots_eq_added] at hs hu
      obtain ⟨ib,_,rfl⟩ := Finset.mem_image.mp hs
      obtain ⟨jb,_,rfl⟩ := Finset.mem_image.mp hu
      have hv := congrArg Prod.snd he
      rw [signedSlot_coordinate, signedSlot_coordinate] at hv
      have hij : ib = jb := signed_representatives_injective hodd r t h hv
      subst jb
      rfl
    · have hroot : u ∈ rootSlots := (hrOrAdded u).resolve_right hu
      exact False.elim ((added_root_coordinates_disjoint r t h s u hs hroot) (congrArg Prod.snd he))
  · have hsroot : s ∈ rootSlots := (hrOrAdded s).resolve_right hs
    by_cases hu : u ∈ addedSlots
    · exact False.elim ((added_root_coordinates_disjoint r t h u s hu hsroot)
        (congrArg Prod.snd he).symm)
    · have huroot : u ∈ rootSlots := (hrOrAdded u).resolve_right hu
      rw [← rootSlots_eq_image] at hsroot huroot
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hsroot
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp huroot
      have hij := rootSlot_place_injective r hr t he
      subst j
      rfl

omit [Fintype G] in
theorem roots_support_as_signed (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (g : G) (hg : g ∈ support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2)) :
    ∃ (k : Fin 6) (b : Bool), g = flipGroup b (rootCoordinate r k) := by
  rcases Finset.mem_union.mp hg with hg | hg
  · obtain ⟨v,hv,hvg⟩ := Finset.mem_image.mp hg
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    rw [← rootSlots_eq_image] at hs
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨k,false,?_⟩
    simpa [flipGroup, rootSlot_coordinate] using hvg.symm
  · obtain ⟨v,hv,hvg⟩ := Finset.mem_image.mp hg
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hv
    rw [← rootSlots_eq_image] at hs
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hs
    refine ⟨k,true,?_⟩
    simpa [flipGroup, rootSlot_coordinate] using hvg.symm

omit [Fintype G] in
theorem geometricallyValid_fresh_roots (r : TetrahedronRoots G)
    (t : TetrahedronParameters G) (h : geometricallyValid r t) :
    Disjoint (support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2))
      (support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2)) := by
  apply Finset.disjoint_left.mpr
  intro g hgA hgR
  rw [concrete_support_eq_twelvePairSupport r t] at hgA
  obtain ⟨⟨i,b⟩,_,hig⟩ := Finset.mem_image.mp hgA
  obtain ⟨k,c,hg⟩ := roots_support_as_signed r t g hgR
  have he : flipGroup b (tetrahedronRepresentative r i t) = flipGroup c (rootCoordinate r k) := by
    calc
      _ = g := by simpa [flipGroup] using hig
      _ = _ := hg
  exact signed_rep_ne_signed_root r t h i k b c he

/-- The counted strong-valid triples satisfy the exact placement and
freshness conditions used in `goodCandidates`, before imposing Q labels. -/
theorem geometricallyValid_supplies_candidate_geometry
    (hodd : Odd (Fintype.card G)) (r : TetrahedronRoots G) (hr : admissibleRoots r)
    (t : TetrahedronParameters G) (h : geometricallyValid r t) :
    Function.Injective (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) ∧
      Disjoint (support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2))
        (support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2)) :=
  ⟨geometricallyValid_place_injective hodd r hr t h, geometricallyValid_fresh_roots r t h⟩

/-- Every counted valid triple is a Q-success exactly when its twelve
representatives have their required Q labels. -/
theorem validParameter_mem_goodCandidates_iff (hodd : Odd (Fintype.card G))
    (Q : Vertex G → Prop) (hQ : EndpointSelector.FixedCardinality.PairReservoir Q)
    (r : TetrahedronRoots G) (hr : admissibleRoots r) (t : TetrahedronParameters G)
    (ht : t ∈ validParameterSet r) :
    (t ∈ goodCandidates Q r) ↔
      ∀ i : Fin 12,
        Q (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot i)) := by
  have hg := geometricallyValid_supplies_candidate_geometry hodd r hr t (Finset.mem_filter.mp ht).2
  have hlabels := added_Q_iff_representatives Q hQ r t
  simp only [goodCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => hlabels.mp h.2.1, fun h => ⟨hg.1,hlabels.mpr h,hg.2⟩⟩

/-- At the paper's n≥1152 threshold, at least three quarters of all
parameter triples pass the stronger geometric validity test. -/
theorem validParameterSet_three_quarters (hodd : Odd (Fintype.card G))
    (r : TetrahedronRoots G) (hr : admissibleRoots r)
    (hn : 1152 ≤ Fintype.card G) :
    3 * (Fintype.card G)^3 ≤ 4 * (validParameterSet r).card := by
  have hvalid := validParameterSet_card_lower hodd r hr
  have htotal : (Fintype.card G)^3 ≤
      (validParameterSet r).card + 288 * (Fintype.card G)^2 :=
    Nat.sub_le_iff_le_add.mp hvalid
  have hbad : 1152 * (Fintype.card G)^2 ≤ (Fintype.card G)^3 := by
    calc
      _ ≤ (Fintype.card G) * (Fintype.card G)^2 := Nat.mul_le_mul_right _ hn
      _ = _ := by ring
  omega

/-- On the actual categorical reservoir, a successful candidate is already
strongly geometrically valid: Q labels rule out cross-part orbit collisions. -/
theorem sampled_goodCandidate_geometricallyValid (ω : EndpointFullProduct.FullSample G)
    (r : TetrahedronRoots G) (t : TetrahedronParameters G)
    (ht : t ∈ goodCandidates (ReservoirVertex ω true) r) : geometricallyValid r t := by
  have ht' := (Finset.mem_filter.mp ht).2
  have hinj := ht'.1
  have hQ := ht'.2.1
  have hfresh := ht'.2.2
  have hnonzero := added_nonzero_of_injective r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂
    t.1 t.2.1 t.2.2 hinj
  have hpairs := sampled_representative_orbits_distinct ω r t hinj hQ
  have hrepA (i : Fin 12) : tetrahedronRepresentative r i t ∈
      support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) := by
    rw [concrete_support_eq_twelvePairSupport r t]
    exact Finset.mem_image.mpr ⟨(i,false), Finset.mem_univ _, by simp⟩
  have hroot (k : Fin 6) : rootCoordinate r k ∈
      support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) := by
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    refine ⟨place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (rootSlot k), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨rootSlot k, ?_, rfl⟩
      rw [←rootSlots_eq_image]
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    · exact rootSlot_coordinate r t k
  have hrootneg (k : Fin 6) : -rootCoordinate r k ∈
      support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) := by
    apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (rootSlot k), ?_, ?_⟩
    · apply Finset.mem_image.mpr
      refine ⟨rootSlot k, ?_, rfl⟩
      rw [←rootSlots_eq_image]
      exact Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩
    · simp [rootSlot_coordinate]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have h := hnonzero (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot i))
      (Finset.mem_image.mpr ⟨representativeSlot i,representativeSlot_mem_added i,rfl⟩)
    simpa [representativeSlot_value] using h
  · intro i j hij
    exact hpairs i j (ne_of_lt hij)
  · intro i k
    constructor
    · intro he
      apply Finset.disjoint_left.mp hfresh (hrepA i)
      simpa [←he] using hroot k
    · intro he
      apply Finset.disjoint_left.mp hfresh (hrepA i)
      simpa [←he] using hrootneg k

theorem sampled_goodCandidates_subset_valid (ω : EndpointFullProduct.FullSample G)
    (r : TetrahedronRoots G) : goodCandidates (ReservoirVertex ω true) r ⊆ validParameterSet r := by
  intro t ht
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,sampled_goodCandidate_geometricallyValid ω r t ht⟩

end
end EndpointMatching.Tetrahedron
