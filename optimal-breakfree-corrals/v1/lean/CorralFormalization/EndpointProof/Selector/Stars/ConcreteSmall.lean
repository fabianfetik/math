import CorralFormalization.EndpointProof.Selector.Assembly.StarPath
import CorralFormalization.EndpointProof.Selector.Assembly.TaggedPairs
import CorralFormalization.EndpointProof.Selector.PrimitiveAvailability

/-!
# Actual small selectors on one primitive sample

This file joins a concrete star to independently fresh, actually available
two-pair switches. Every forbidden numerical inverse closure is paid before
the next query. It discharges the small-supplier premise of the general
selector assembly; it does not add a selector-existence assumption.
-/

open scoped Classical BigOperators

namespace EndpointSelector.Stars

open EndpointSelector.Assembly

noncomputable section

set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

variable {G : Type*} [CommRing G] [Fintype G]

theorem star_available_of_primitive_events
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : ∀ i, selectorPrimitiveEvents hodd hn budget i ω)
    (k : ℕ) (hk0 : 1 ≤ k) (hk : k ≤ 3) :
    EndpointFullProduct.FullAvailable (rotatedStarQueryEmbedding hk hodd hn)
      (fun r _ ↦ rotatedStarDemand r.1) budget ω := by
  interval_cases k
  · simpa [selectorPrimitiveEvents] using hgood 1
  · simpa [selectorPrimitiveEvents] using hgood 2
  · simpa [selectorPrimitiveEvents] using hgood 3

omit [Fintype G] in
theorem numericalSupport_star (a : Fin k → G) (u : G) :
    numericalSupport (starInterior a u) = starSupport a u :=
  starInterior_inverse_closure a u

omit [Fintype G] in
theorem numericalSupport_switch (a b u : G) :
    numericalSupport (interior a b u) = orbitSupport a b u :=
  interior_inverse_closure a b u

omit [Fintype G] in
theorem numericalSupport_biUnion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Finset (Vertex G)) :
    numericalSupport (s.biUnion S) = s.biUnion (fun i ↦ numericalSupport (S i)) := by
  ext x
  simp only [numericalSupport,Finset.mem_union,Finset.mem_image,Finset.mem_biUnion]
  aesop

omit [Fintype G] in
theorem starPair_eq_pair (a : Fin k → G) (u : G) (i : Fin k) :
    starPair a u i = pair 2 (-a i-u) := by
  simp [starPair,pair,add_comm]

omit [Fintype G] in
theorem pair_disjoint_of_rootCondition (p : Fin 3) {a b : G} (hr : RootCondition a b) :
    Disjoint (pair p a) (pair p b) := by
  rcases hr with ⟨ha,hb,hab,han⟩
  simp only [pair,Finset.disjoint_left,Finset.mem_insert,Finset.mem_singleton]
  intro x hx hy
  rcases hx with rfl | rfl <;> rcases hy with hy | hy
  · exact hab (congrArg Prod.snd hy)
  · exact han (congrArg Prod.snd hy)
  · apply han
    simpa using congrArg (fun v ↦ -v.2) hy
  · exact hab (neg_injective (congrArg Prod.snd hy))

omit [Fintype G] in
theorem starPairs_disjoint (a : Fin k → G) (u : G) (hv : StarValid a u) :
    Pairwise (fun i j ↦ Disjoint (starPair a u i) (starPair a u j)) := by
  intro i j hij
  rw [starPair_eq_pair,starPair_eq_pair]
  exact pair_disjoint_of_rootCondition 2 (starPair_rootCondition a u hv i j hij)

/-- Concrete outputs of an actual switch query, with all inverse signs charged. -/
def SwitchPieceData (P : Vertex G → Prop) (L R : Finset (Vertex G))
    (F : Finset G) (J : Finset (Vertex G)) : Prop :=
  (∀ v ∈ J, P v) ∧ J.card ≤ 4 ∧ Disjoint (numericalSupport J) F ∧
    Nonempty (MatchingOn (J ∪ L)) ∧ Nonempty (MatchingOn (J ∪ R))

/-- Greedy use of the actual common event. No disjoint switch family is assumed.
The harmless `8*n` charge also covers the final, unused next-stage reserve. -/
theorem exists_fresh_switch_path
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : AllRotatedSwitches hodd hn budget ω)
    {n : ℕ} (c : Fin (n+1) → G)
    (hr : ∀ j : Fin n, RootCondition (c j.castSucc) (c j.succ))
    (τ : Equiv.Perm (Fin 3)) (F : Finset G)
    (hbudget : F.card+8*n ≤ budget) :
    ∃ J : Fin n → Finset (Vertex G),
      (∀ j, SwitchPieceData (PVertex ω)
        (rotate τ (target (c j.castSucc))) (rotate τ (target (c j.succ))) F (J j)) ∧
      Pairwise (fun i j ↦ Disjoint (numericalSupport (J i)) (numericalSupport (J j))) := by
  have main : ∀ s : Finset (Fin n), ∃ J : Fin n → Finset (Vertex G),
      (∀ j ∈ s, SwitchPieceData (PVertex ω)
        (rotate τ (target (c j.castSucc))) (rotate τ (target (c j.succ))) F (J j)) ∧
      (s : Set (Fin n)).Pairwise
        (fun i j ↦ Disjoint (numericalSupport (J i)) (numericalSupport (J j))) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ ↦ ∅,by simp,by simp⟩
    | @insert j s hjs ih =>
      obtain ⟨J,hJ,hdJ⟩ := ih
      let Fnext := F ∪ s.biUnion (fun i ↦ numericalSupport (J i))
      have hsc : s.card ≤ n := by simpa using Finset.card_le_univ s
      have hsup : (s.biUnion (fun i ↦ numericalSupport (J i))).card ≤ 8*s.card := by
        have hh := Finset.card_biUnion_le_card_mul s (fun i ↦ numericalSupport (J i)) 8
          (fun i hi ↦ (numericalSupport_card_le (J i)).trans (by have := (hJ i hi).2.1; omega))
        simpa [Nat.mul_comm] using hh
      have hFnext : Fnext.card ≤ budget := by
        have hh := Finset.card_union_le F (s.biUnion (fun i ↦ numericalSupport (J i)))
        dsimp only [Fnext]
        omega
      let r : RootQuery G := ⟨(c j.castSucc,c j.succ),hr j⟩
      obtain ⟨u,hv,hd,hP,hcard,hl,hrt⟩ :=
        rotated_switch_of_fullAvailable hodd hn budget τ ω (hgood τ) r Fnext hFnext
      let U := rotate τ (interior (c j.castSucc) (c j.succ) u)
      have hUF : Disjoint (numericalSupport U) Fnext := by
        simpa [U,numericalSupport_switch] using hd
      have hdata : SwitchPieceData (PVertex ω)
          (rotate τ (target (c j.castSucc))) (rotate τ (target (c j.succ))) F U :=
        ⟨hP,hcard.le,hUF.mono_right Finset.subset_union_left,hl,hrt⟩
      have hUd (i : Fin n) (hi : i ∈ s) :
          Disjoint (numericalSupport U) (numericalSupport (J i)) := by
        apply hUF.mono_right
        intro x hx
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i,hi,hx⟩)
      refine ⟨Function.update J j U,?_,?_⟩
      · intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · simpa using hdata
        · have hij : i ≠ j := fun he ↦ hjs (he ▸ hi)
          simpa [Function.update_of_ne hij] using hJ i hi
      · intro i hi l hl hil
        by_cases hij : i = j
        · subst i
          have hlj : l ≠ j := Ne.symm hil
          have hlS : l ∈ s := (Finset.mem_insert.mp hl).resolve_left hlj
          simpa [Function.update_of_ne hlj] using hUd l hlS
        · have hiS : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hij
          by_cases hlj : l = j
          · subst l
            simpa [Function.update_of_ne hij] using (hUd i hiS).symm
          · have hlS : l ∈ s := (Finset.mem_insert.mp hl).resolve_left hlj
            simpa [Function.update_of_ne hij,Function.update_of_ne hlj] using hdJ hiS hlS hil
  obtain ⟨J,hJ,hdJ⟩ := main Finset.univ
  exact ⟨J,fun j ↦ hJ j (Finset.mem_univ _),fun _ _ h ↦ hdJ (Finset.mem_univ _) (Finset.mem_univ _) h⟩

/-- The actual star and fresh concrete switches form a genuine small selector.
The internal budget is explicitly charged by at most thirty extra coordinates. -/
theorem exists_small_selector_for_roots
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : ∀ i, selectorPrimitiveEvents hodd hn budget i ω)
    {n : ℕ} (hn2 : n ≤ 2) (a : Fin (n+1) → G) (hr : StarRoots a)
    (σ : Equiv.Perm (Fin 3)) (F : Finset G) (hbudget : F.card+32 ≤ budget) :
    ∃ S : SelectorOn (PVertex ω) (Finset.univ.image (fun i ↦ rotate σ (target (a i)))),
      S.interior.card ≤ 16 ∧ Disjoint (numericalSupport S.interior) F := by
  have hsw : AllRotatedSwitches hodd hn budget ω := by
    simpa [selectorPrimitiveEvents] using hgood 0
  have hs := star_available_of_primitive_events hodd hn budget ω hgood (n+1) (by omega) (by omega)
  let r : StarQuery G (n+1) := ⟨a,hr⟩
  obtain ⟨u,hv,hUF,hP,_,hm⟩ := successful_rotated_star_of_fullAvailable
    (by omega : n+1 ≤ 3) hodd hn budget ω hs r σ F (by omega)
  change StarValid a u at hv
  change Disjoint (starSupport a u) F at hUF
  change ∀ v ∈ starInterior a u, PVertex ω (σ v.1,v.2) ∧ _ at hP
  change ∀ i, IsTwoEdgeMatchingOn (starState a u i)
    ((starCommonPair u ∪ starPair a u i) ∪ target (a i)) at hm
  let Fbase := (F ∪ starRootSupport a) ∪ starSupport a u
  have hFbase : Fbase.card+8*n ≤ budget := by
    have hrsize := starRootSupport_card_le a
    have hssize := starSupport_card_le a u
    have h₁ := Finset.card_union_le F (starRootSupport a)
    have h₂ := Finset.card_union_le (F ∪ starRootSupport a) (starSupport a u)
    dsimp only [Fbase]
    omega
  let c : Fin (n+1) → G := fun i ↦ -a i-u
  let τ : Equiv.Perm (Fin 3) := (Equiv.swap 0 2).trans σ
  have hportEq (i : Fin (n+1)) :
      rotate τ (target (c i)) = rotate σ (starPair a u i) := by
    change rotate τ (pair 0 (-a i-u)) = rotate σ (starPair a u i)
    rw [starPair_eq_pair,rotate_pair,rotate_pair]
    simp [τ]
  obtain ⟨J,hJ,hdJ⟩ := exists_fresh_switch_path hodd hn budget ω hsw c
    (fun j ↦ starPair_rootCondition a u hv j.castSucc j.succ (by
      intro h
      have he := congrArg Fin.val h
      simp only [Fin.val_castSucc,Fin.val_succ] at he
      omega)) τ Fbase hFbase
  have hcommonSupport : numericalSupport (rotate σ (starCommonPair u)) ⊆ starSupport a u := by
    rw [numericalSupport_rotate,← numericalSupport_star a u]
    exact numericalSupport_mono (starCommonPair_subset_interior a u)
  have hportSupport (i : Fin (n+1)) :
      numericalSupport (rotate σ (starPair a u i)) ⊆ starSupport a u := by
    rw [numericalSupport_rotate,← numericalSupport_star a u]
    exact numericalSupport_mono (starPair_subset_interior a u i)
  have hrootSupport (i : Fin (n+1)) :
      numericalSupport (rotate σ (target (a i))) ⊆ starRootSupport a := by
    rw [numericalSupport_rotate]
    change numericalSupport (pair 0 (a i)) ⊆ _
    rw [numericalSupport_pair]
    intro x hx
    rcases Finset.mem_insert.mp hx with hx | hx
    · exact (mem_starRootSupport _ _).2 ⟨i,Or.inl hx⟩
    · exact (mem_starRootSupport _ _).2 ⟨i,Or.inr (Finset.mem_singleton.mp hx)⟩
  have hswitchStar (j : Fin n) : Disjoint (numericalSupport (J j)) (starSupport a u) :=
    (hJ j).2.2.1.mono_right Finset.subset_union_right
  have hswitchRoot (j : Fin n) : Disjoint (numericalSupport (J j)) (starRootSupport a) :=
    (hJ j).2.2.1.mono_right (Finset.subset_union_right.trans Finset.subset_union_left)
  have hswitchF (j : Fin n) : Disjoint (numericalSupport (J j)) F :=
    (hJ j).2.2.1.mono_right (Finset.subset_union_left.trans Finset.subset_union_left)
  let S : StarPath (PVertex ω) n := {
    common := rotate σ (starCommonPair u)
    port := fun i ↦ rotate σ (starPair a u i)
    root := fun i ↦ rotate σ (target (a i))
    switchInterior := J
    common_inside := by
      intro v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      rcases w with ⟨p,x⟩
      simpa [tagEquiv] using (hP (p,x) (starCommonPair_subset_interior a u hw)).1
    port_inside := by
      intro i v hv
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
      rcases w with ⟨p,x⟩
      simpa [tagEquiv] using (hP (p,x) (starPair_subset_interior a u i hw)).1
    switch_inside := fun j ↦ (hJ j).1
    common_port := fun i ↦ rotate_disjoint σ (by
      simp [starCommonPair,starPair,Finset.disjoint_left])
    ports := fun i j hij ↦ rotate_disjoint σ (starPairs_disjoint a u hv hij)
    root_common := fun i ↦ rotate_disjoint σ (by
      simp [target,starCommonPair,Finset.disjoint_left])
    root_port := fun i j ↦ rotate_disjoint σ (by
      simp [target,starPair,Finset.disjoint_left])
    switch_common := fun j ↦ disjoint_of_numericalSupport ((hswitchStar j).mono_right hcommonSupport)
    switch_port := fun j i ↦ disjoint_of_numericalSupport ((hswitchStar j).mono_right (hportSupport i))
    switch_root := fun j i ↦ disjoint_of_numericalSupport ((hswitchRoot j).mono_right (hrootSupport i))
    switches := fun i j hij ↦ disjoint_of_numericalSupport (hdJ hij)
    star_matching := fun i ↦ ⟨by simpa using (MatchingOn.two (hm i)).rotated σ⟩
    switch_left := fun j ↦ by simpa only [hportEq] using (hJ j).2.2.2.1
    switch_right := fun j ↦ by simpa only [hportEq] using (hJ j).2.2.2.2 }
  have hcard : S.interior.card ≤ 16 := by
    have hh := S.interior_card_le (by simpa [S,starCommonPair] using (Finset.card_le_two (a := (1,u)) (b := (1,-u))))
      (fun i ↦ by simpa [S,starPair] using
        (Finset.card_le_two (a := (2,-a i-u)) (b := (2,a i+u))))
      (fun j ↦ (hJ j).2.1)
    omega
  have hd : Disjoint (numericalSupport S.interior) F := by
    change Disjoint (numericalSupport
      ((rotate σ (starCommonPair u) ∪ Finset.univ.biUnion (fun i ↦ rotate σ (starPair a u i))) ∪
        Finset.univ.biUnion J)) F
    rw [numericalSupport_union,numericalSupport_union,numericalSupport_biUnion,numericalSupport_biUnion]
    apply Finset.disjoint_union_left.mpr
    refine ⟨Finset.disjoint_union_left.mpr ⟨hUF.mono_left hcommonSupport,?_⟩,?_⟩
    · apply Finset.disjoint_left.mpr
      intro x hx hxF
      obtain ⟨i,_,hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.disjoint_left.mp hUF (hportSupport i hx) hxF
    · apply Finset.disjoint_left.mpr
      intro x hx hxF
      obtain ⟨j,_,hx⟩ := Finset.mem_biUnion.mp hx
      exact Finset.disjoint_left.mp (hswitchF j) hx hxF
  exact ⟨S.selector,hcard,hd⟩

theorem exists_small_selector_for_arity
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : ∀ i, selectorPrimitiveEvents hodd hn budget i ω)
    {k : ℕ} (hk0 : 1 ≤ k) (hk3 : k ≤ 3) (a : Fin k → G) (hr : StarRoots a)
    (σ : Equiv.Perm (Fin 3)) (F : Finset G) (hbudget : F.card+32 ≤ budget) :
    ∃ S : SelectorOn (PVertex ω) (Finset.univ.image (fun i ↦ rotate σ (target (a i)))),
      S.interior.card ≤ 16 ∧ Disjoint (numericalSupport S.interior) F := by
  cases k with
  | zero => omega
  | succ n =>
    exact exists_small_selector_for_roots hodd hn budget ω hgood (by omega) a hr σ F hbudget

/-- The concrete common primitive event discharges the actual small-supply
premise of `ManySelectors`, for every later target family and forbidden set.
The fixed thirty-two-coordinate reserve pays all roots and every inverse sign. -/
theorem smallSupply_of_selectorPrimitiveEvents
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : ∀ i, selectorPrimitiveEvents hodd hn budget i ω) (p : Fin 3) :
    SmallSupply (PVertex ω) (LegalPair p) budget := by
  intro R F hne hcard hlegal hbudget
  obtain ⟨a,hr,heq⟩ := exists_root_enumeration p R hlegal
  let σ : Equiv.Perm (Fin 3) := Equiv.swap 0 p
  have htargets : Finset.univ.image (fun i ↦ rotate σ (target (a i))) = R := by
    calc
      _ = Finset.univ.image (fun i ↦ pair p (a i)) := by
        congr 1
        funext i
        change rotate σ (pair 0 (a i)) = pair p (a i)
        rw [rotate_pair]
        simp [σ]
      _ = R := heq
  have hk0 : 1 ≤ R.card := Finset.card_pos.mpr hne
  obtain ⟨S,hS,hd⟩ := exists_small_selector_for_arity hodd hn budget ω hgood hk0 hcard a hr σ F hbudget
  exact Eq.mp (congrArg (fun Q ↦ ∃ S : SelectorOn (PVertex ω) Q,
    S.interior.card ≤ 16 ∧ Disjoint (numericalSupport S.interior) F) htargets) ⟨S,hS,hd⟩

end
end EndpointSelector.Stars
