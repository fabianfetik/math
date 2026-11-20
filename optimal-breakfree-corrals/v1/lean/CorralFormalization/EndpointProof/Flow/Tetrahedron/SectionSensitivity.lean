import CorralFormalization.EndpointProof.Flow.Tetrahedron.Sensitivity
open scoped Classical BigOperators
namespace EndpointMatching.Tetrahedron
open CorralFormalization.EndpointProof.Probability.QuadraticDeletion
open EndpointFlow.AbelianTransport
open EndpointFullProduct EndpointOriginalReservoir
noncomputable section
variable {G : Type*} [AddCommGroup G] [Fintype G]

def sectionFreeCoordinate (i j : Fin 6) (t : TetrahedronParameters G) : G :=
  let k : Fin 3 := ![![0,2,1,2,1,2], ![2,0,0,2,2,0], ![1,0,0,1,1,0],
    ![2,2,1,0,2,2], ![1,2,1,2,0,2], ![2,0,0,2,2,0]] i j
  ![t.1,t.2.1,t.2.2] k


/-- Explicit inversion of two different directions and their remaining
free coordinate. Every coefficient is 0 or ±1. -/
def recoverAscending (i j : Fin 6) (g h w : G) : TetrahedronParameters G :=
  match i.val, j.val with
  | 0,1 => (g,h,w)
  | 0,2 => (g,w,h)
  | 0,3 => (g,h-g,w)
  | 0,4 => (g,w,h+g)
  | 0,5 => (g,-h-w,w)
  | 1,2 => (w,g,h)
  | 1,3 => (h-g,g,w)
  | 1,4 => (w-h,g,w)
  | 1,5 => (w,g,-h-g)
  | 2,3 => (h-w,w,g)
  | 2,4 => (g-h,w,g)
  | 2,5 => (w,-h-g,g)
  | 3,4 => (w-h,g-w+h,w)
  | 3,5 => (g+h+w,-h-w,w)
  | 4,5 => (w-g,-h-w,w)
  | _,_ => (0,0,0)

def recoverSections (i j : Fin 6) (g h w : G) : TetrahedronParameters G :=
  if i.val < j.val then recoverAscending i j g h w else recoverAscending j i h g w

omit [Fintype G] in
theorem recoverSections_correct (i j : Fin 6) (hij : i ≠ j)
    (t : TetrahedronParameters G) :
    recoverSections i j (tetrahedronDirection i t) (tetrahedronDirection j t)
      (sectionFreeCoordinate i j t) = t := by
  rcases t with ⟨a,b,c⟩
  fin_cases i <;> fin_cases j <;>
    simp_all [recoverSections, recoverAscending, tetrahedronDirection, sectionFreeCoordinate]
  all_goals abel

theorem twoSections_free_injective (i j : Fin 6) (hij : i ≠ j) (g h : G) :
    Set.InjOn (sectionFreeCoordinate i j)
      (↑((Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => tetrahedronDirection i t = g ∧ tetrahedronDirection j t = h)) :
          Set (TetrahedronParameters G)) := by
  intro t ht u hu he
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  calc
    t = recoverSections i j (tetrahedronDirection i t) (tetrahedronDirection j t)
        (sectionFreeCoordinate i j t) := (recoverSections_correct i j hij t).symm
    _ = recoverSections i j (tetrahedronDirection i u) (tetrahedronDirection j u)
        (sectionFreeCoordinate i j u) := by rw [ht'.1,ht'.2,hu'.1,hu'.2,he]
    _ = u := recoverSections_correct i j hij u

/-- Intersecting two distinct direction sections leaves at most one free
group coordinate, so its cardinality is at most |G|. -/
theorem twoDirections_section_card_le (i j : Fin 6) (hij : i ≠ j) (g h : G) :
    ((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronDirection i t = g ∧ tetrahedronDirection j t = h)).card ≤
      Fintype.card G := by
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronDirection i t = g ∧ tetrahedronDirection j t = h))
    (t := (Finset.univ : Finset G)) (sectionFreeCoordinate i j)
    (by intro t ht; simp) (twoSections_free_injective i j hij g h)
  simpa using hc

/-- On one fixed section, every nonparallel representative assumes a fixed
value for at most |G| parameter triples. -/
theorem representative_on_section_card_le (r : TetrahedronRoots G)
    (i : Fin 6) (j : Fin 12) (hij : tetrahedronDirectionIndex j ≠ i) (g h : G) :
    ((((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronDirection i t = g)).filter
      (fun t => tetrahedronRepresentative r j t = h)).card : ℝ) ≤ Fintype.card G := by
  let C : Finset (TetrahedronParameters G) := Finset.univ.filter
    (fun t => tetrahedronDirection i t = g)
  let f : G → G := fun x =>
    (if tetrahedronNegative j then -x else x) + tetrahedronOffset r j
  have hf : Function.Injective f := by
    intro x y hxy
    have he : (if tetrahedronNegative j then -x else x) =
        (if tetrahedronNegative j then -y else y) := add_right_cancel hxy
    split_ifs at he
    · exact neg_injective he
    · exact he
  have hsection : ∀ z,
      ((C.filter (fun t => tetrahedronDirection (tetrahedronDirectionIndex j) t = z)).card : ℝ)
        ≤ Fintype.card G := by
    intro z
    have heq : C.filter (fun t => tetrahedronDirection (tetrahedronDirectionIndex j) t = z) =
        (Finset.univ : Finset (TetrahedronParameters G)).filter
          (fun t => tetrahedronDirection i t = g ∧
            tetrahedronDirection (tetrahedronDirectionIndex j) t = z) := by
      ext t; simp [C]
    rw [heq]
    exact_mod_cast twoDirections_section_card_le i (tetrahedronDirectionIndex j) hij.symm g z
  exact section_bound_of_injective C (tetrahedronDirection (tetrahedronDirectionIndex j))
    f hf (Fintype.card G : ℝ) (by positivity) hsection h

/-- Each direction occurs exactly twice among the twelve representatives. -/
def activeRepresentatives (i : Fin 6) : Finset (Fin 12) :=
  Finset.univ.filter (fun j => tetrahedronDirectionIndex j ≠ i)

theorem activeRepresentatives_card (i : Fin 6) : (activeRepresentatives i).card = 10 := by
  fin_cases i <;> decide

def activePairSupport (r : TetrahedronRoots G) (i : Fin 6)
    (t : TetrahedronParameters G) : Finset G :=
  ((activeRepresentatives i) ×ˢ (Finset.univ : Finset Bool)).image (fun j =>
    if j.2 then -tetrahedronRepresentative r j.1 t else tetrahedronRepresentative r j.1 t)

/-- In a fixed direction section, one inverse orbit appears in at most
20|G| of the candidates after omitting the two constant representatives. -/
theorem active_orbit_incidence_on_section (r : TetrahedronRoots G) (i : Fin 6) (g z : G) :
    (((Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronDirection i t = g ∧ z ∈ activePairSupport r i t)).card : ℝ)
        ≤ 20 * (Fintype.card G : ℝ) := by
  let C : Finset (TetrahedronParameters G) := Finset.univ.filter
    (fun t => tetrahedronDirection i t = g)
  let D : Finset (Fin 12 × Bool) := (activeRepresentatives i) ×ˢ Finset.univ
  let hit (j : Fin 12 × Bool) : Finset (TetrahedronParameters G) :=
    C.filter (fun t => (if j.2 then -tetrahedronRepresentative r j.1 t else
      tetrahedronRepresentative r j.1 t) = z)
  have hhit : ∀ j ∈ D, ((hit j).card : ℝ) ≤ (Fintype.card G : ℝ) := by
    rintro ⟨j,b⟩ hj
    have hj' : tetrahedronDirectionIndex j ≠ i :=
      (Finset.mem_filter.mp (Finset.mem_product.mp hj).1).2
    cases b with
    | false => exact representative_on_section_card_le r i j hj' g z
    | true =>
      have heq : hit (j,true) = C.filter (fun t => tetrahedronRepresentative r j t = -z) := by
        ext t; simp only [hit, Finset.mem_filter, ↓reduceIte, neg_eq_iff_eq_neg]
      rw [heq]
      exact representative_on_section_card_le r i j hj' g (-z)
  have hsub : (Finset.univ : Finset (TetrahedronParameters G)).filter
      (fun t => tetrahedronDirection i t = g ∧ z ∈ activePairSupport r i t) ⊆
      D.biUnion hit := by
    intro t ht
    obtain ⟨htdir,htsupp⟩ := by simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using ht
    obtain ⟨j,hj,hjt⟩ := Finset.mem_image.mp htsupp
    exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,htdir⟩,hjt⟩⟩
  have hD : D.card = 20 := by simp [D, activeRepresentatives_card]
  calc
    _ ≤ ((D.biUnion hit).card : ℝ) := Nat.cast_le.mpr (Finset.card_le_card hsub)
    _ ≤ ∑ j ∈ D, ((hit j).card : ℝ) := by exact_mod_cast (Finset.card_biUnion_le (s := D) (t := hit))
    _ ≤ ∑ _j ∈ D, (Fintype.card G : ℝ) := Finset.sum_le_sum hhit
    _ = _ := by simp [hD]

/-- The larger count used in the paper on a fixed section: omit the two
constant Q-label requirements, but keep all placement/freshness conditions. -/
def reducedSectionCandidates (Q : Vertex G → Prop) (r : TetrahedronRoots G)
    (i : Fin 6) (g : G) : Finset (TetrahedronParameters G) :=
  ((Finset.univ : Finset (TetrahedronParameters G)).filter
    (fun t => tetrahedronDirection i t = g)).filter (fun t =>
      Function.Injective (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2) ∧
      Disjoint (support (added r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2))
        (support (roots r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2)) ∧
      ∀ j ∈ activeRepresentatives i,
        Q (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j)))

theorem goodCandidates_section_subset_reduced (Q : Vertex G → Prop)
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    (goodCandidates Q r).filter (fun t => tetrahedronDirection i t = g) ⊆
      reducedSectionCandidates Q r i g := by
  intro t ht
  obtain ⟨ht, hdir⟩ := Finset.mem_filter.mp ht
  have hv := (Finset.mem_filter.mp ht).2
  refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hdir⟩,
    hv.1, hv.2.2, ?_⟩
  intro j hj
  apply hv.2.1
  exact Finset.mem_image.mpr ⟨representativeSlot j, representativeSlot_mem_added j, rfl⟩

theorem reducedSection_mem_congr_off_orbit (Q Q' : Vertex G → Prop)
    (r : TetrahedronRoots G) (i : Fin 6) (g z : G) (t : TetrahedronParameters G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v))
    (hz : z ∉ activePairSupport r i t) :
    t ∈ reducedSectionCandidates Q r i g ↔ t ∈ reducedSectionCandidates Q' r i g := by
  have hvQ (j : Fin 12) (hj : j ∈ activeRepresentatives i) :
      Q (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j)) ↔
      Q' (place r.a₁ r.a₂ r.b₁ r.b₂ r.c₁ r.c₂ t.1 t.2.1 t.2.2 (representativeSlot j)) := by
    apply hQeq
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      refine ⟨(j,false), Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩, ?_⟩
      simpa [representativeSlot_value] using he
    · intro he
      apply hz
      apply Finset.mem_image.mpr
      refine ⟨(j,true), Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩, ?_⟩
      have he' : tetrahedronRepresentative r j t = -z := by
        simpa [representativeSlot_value] using he
      simp [he']
  simp only [reducedSectionCandidates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor <;> rintro ⟨hdir,hinj,hfresh,hlabels⟩ <;> refine ⟨hdir,hinj,hfresh,?_⟩
  · intro j hj
    exact (hvQ j hj).mp (hlabels j hj)
  · intro j hj
    exact (hvQ j hj).mpr (hlabels j hj)

def reducedChangedCandidates (Q Q' : Vertex G → Prop) (r : TetrahedronRoots G)
    (i : Fin 6) (g : G) : Finset (TetrahedronParameters G) :=
  (reducedSectionCandidates Q r i g \ reducedSectionCandidates Q' r i g) ∪
    (reducedSectionCandidates Q' r i g \ reducedSectionCandidates Q r i g)

/-- One-orbit changes modify at most 20|G| of the reduced section count.
This is the deterministic input to the paper's section concentration. -/
theorem reducedSection_count_change_le (Q Q' : Vertex G → Prop)
    (r : TetrahedronRoots G) (i : Fin 6) (g z : G)
    (hQeq : ∀ v, v.2 ≠ z → v.2 ≠ -z → (Q v ↔ Q' v)) :
    |((reducedSectionCandidates Q r i g).card : ℝ) -
      ((reducedSectionCandidates Q' r i g).card : ℝ)| ≤ 20 * (Fintype.card G : ℝ) := by
  let A := reducedSectionCandidates Q r i g
  let B := reducedSectionCandidates Q' r i g
  let N := 20 * Fintype.card G
  have hchanged : (reducedChangedCandidates Q Q' r i g).card ≤ N := by
    have hsub : reducedChangedCandidates Q Q' r i g ⊆
        (Finset.univ : Finset (TetrahedronParameters G)).filter
          (fun t => tetrahedronDirection i t = g ∧ z ∈ activePairSupport r i t) := by
      intro t ht
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · rcases Finset.mem_union.mp ht with ht | ht
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1).2
        · exact (Finset.mem_filter.mp (Finset.mem_filter.mp (Finset.mem_sdiff.mp ht).1).1).2
      · by_contra hz
        have heq := reducedSection_mem_congr_off_orbit Q Q' r i g z t hQeq hz
        rcases Finset.mem_union.mp ht with ht | ht
        · exact (Finset.mem_sdiff.mp ht).2 (heq.mp (Finset.mem_sdiff.mp ht).1)
        · exact (Finset.mem_sdiff.mp ht).2 (heq.mpr (Finset.mem_sdiff.mp ht).1)
    have hinc := active_orbit_incidence_on_section r i g z
    have hn : (((Finset.univ : Finset (TetrahedronParameters G)).filter
        (fun t => tetrahedronDirection i t = g ∧ z ∈ activePairSupport r i t)).card) ≤ N := by
      dsimp [N]
      exact_mod_cast hinc
    exact (Finset.card_le_card hsub).trans hn
  have hleft : A.card ≤ B.card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := A \ B) (t := reducedChangedCandidates Q Q' r i g)
      Finset.subset_union_left
    rw [Finset.inter_comm B A] at h₂
    omega
  have hright : B.card ≤ A.card + N := by
    have h₁ := Finset.card_sdiff_add_card_inter A B
    have h₂ := Finset.card_sdiff_add_card_inter B A
    have hd := Finset.card_le_card (s := B \ A) (t := reducedChangedCandidates Q Q' r i g)
      Finset.subset_union_right
    rw [Finset.inter_comm B A] at h₂
    omega
  have hl' : (A.card : ℝ) ≤ (B.card : ℝ) + 20 * (Fintype.card G : ℝ) := by
    dsimp [N] at hleft; exact_mod_cast hleft
  have hr' : (B.card : ℝ) ≤ (A.card : ℝ) + 20 * (Fintype.card G : ℝ) := by
    dsimp [N] at hright; exact_mod_cast hright
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem sampled_reducedSection_count_change_le
    (ω ω' : FullSample G) (o : OddOrbit G)
    (hchild : ∀ o' : OddOrbit G, o' ≠ o →
      childLabel ((regroup ω).1 o') = childLabel ((regroup ω').1 o'))
    (r : TetrahedronRoots G) (i : Fin 6) (g : G) :
    |((reducedSectionCandidates (ReservoirVertex ω true) r i g).card : ℝ) -
      ((reducedSectionCandidates (ReservoirVertex ω' true) r i g).card : ℝ)| ≤
        20 * (Fintype.card G : ℝ) :=
  reducedSection_count_change_le (ReservoirVertex ω true) (ReservoirVertex ω' true)
    r i g (orbitPlace (o,false)) (sampled_reservoir_agrees_off_orbit ω ω' o hchild)

end
end EndpointMatching.Tetrahedron
