import CorralFormalization.EndpointProof.Selector.Assembly.Splice
import CorralFormalization.EndpointProof.Selector.Stars.Basic

/-!
The deterministic small-selector path in the coloured selector construction, for a star with n+1 arms and
n independent switches. Fin.succAbove chooses exactly the C ports other
than the port covered by the chosen star state.
-/

open scoped Classical BigOperators

namespace EndpointSelector.Assembly

noncomputable section

variable {G : Type*} [CommRing G] [DecidableEq G]

theorem matching_biUnion {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (S : ι → Finset (Vertex G))
    (hm : ∀ i ∈ s, Nonempty (MatchingOn (S i)))
    (hd : (s : Set ι).Pairwise (fun i j ↦ Disjoint (S i) (S j))) :
    Nonempty (MatchingOn (s.biUnion S)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨by simpa using (MatchingOn.empty (G := G))⟩
  | @insert i s hi ih =>
    obtain ⟨M⟩ := hm i (Finset.mem_insert_self _ _)
    obtain ⟨N⟩ := ih (fun j hj ↦ hm j (Finset.mem_insert_of_mem hj))
      (fun _ hj _ hk hne ↦ hd (Finset.mem_insert_of_mem hj) (Finset.mem_insert_of_mem hk) hne)
    have hdisj : Disjoint (S i) (s.biUnion S) := by
      apply Finset.disjoint_left.mpr
      intro v hv hv'
      obtain ⟨j,hj,hvj⟩ := Finset.mem_biUnion.mp hv'
      exact Finset.disjoint_left.mp
        (hd (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hj) (fun he ↦ hi (he ▸ hj))) hv hvj
    exact ⟨by simpa using M.union N hdisj⟩

/-- A star plus a path of selectors between its C ports. All geometric and
reservoir facts are explicit fields; exact matchings are constructed below. -/
structure StarPath (P : Vertex G → Prop) (n : ℕ) where
  common : Finset (Vertex G)
  port : Fin (n+1) → Finset (Vertex G)
  root : Fin (n+1) → Finset (Vertex G)
  switchInterior : Fin n → Finset (Vertex G)
  common_inside : ∀ v ∈ common, P v
  port_inside : ∀ i v, v ∈ port i → P v
  switch_inside : ∀ i v, v ∈ switchInterior i → P v
  common_port : ∀ i, Disjoint common (port i)
  ports : Pairwise (fun i j ↦ Disjoint (port i) (port j))
  root_common : ∀ i, Disjoint (root i) common
  root_port : ∀ i j, Disjoint (root i) (port j)
  switch_common : ∀ j, Disjoint (switchInterior j) common
  switch_port : ∀ j i, Disjoint (switchInterior j) (port i)
  switch_root : ∀ j i, Disjoint (switchInterior j) (root i)
  switches : Pairwise (fun i j ↦ Disjoint (switchInterior i) (switchInterior j))
  star_matching : ∀ i, Nonempty (MatchingOn ((common ∪ port i) ∪ root i))
  switch_left : ∀ j, Nonempty (MatchingOn (switchInterior j ∪ port j.castSucc))
  switch_right : ∀ j, Nonempty (MatchingOn (switchInterior j ∪ port j.succ))

def StarPath.interior {P : Vertex G → Prop} {n : ℕ} (S : StarPath P n) : Finset (Vertex G) :=
  (S.common ∪ Finset.univ.biUnion S.port) ∪ Finset.univ.biUnion S.switchInterior

def StarPath.targets {P : Vertex G → Prop} {n : ℕ} (S : StarPath P n) :
    Finset (Finset (Vertex G)) := Finset.univ.image S.root

def StarPath.selector {P : Vertex G → Prop} {n : ℕ} (S : StarPath P n) :
    SelectorOn P S.targets where
  interior := S.interior
  inside := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact S.common_inside v hv
      · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
        exact S.port_inside i v hi
    · obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hv
      exact S.switch_inside i v hi
  fresh := by
    intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    apply Finset.disjoint_left.mpr
    intro v hv hr
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact Finset.disjoint_left.mp (S.root_common i) hr hv
      · obtain ⟨j,_,hv⟩ := Finset.mem_biUnion.mp hv
        exact Finset.disjoint_left.mp (S.root_port i j) hr hv
    · obtain ⟨j,_,hv⟩ := Finset.mem_biUnion.mp hv
      exact Finset.disjoint_left.mp (S.switch_root j i) hv hr
  matching := by
    intro T hT
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hT
    let W := fun j : Fin n ↦ S.switchInterior j ∪ S.port (i.succAbove j)
    have hwm : ∀ j ∈ (Finset.univ : Finset (Fin n)), Nonempty (MatchingOn (W j)) := by
      intro j _
      by_cases hj : j.castSucc < i
      · simpa only [W,Fin.succAbove_of_castSucc_lt _ _ hj] using S.switch_left j
      · simpa only [W,Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt hj)] using S.switch_right j
    have hwd : Pairwise (fun j k ↦ Disjoint (W j) (W k)) := by
      intro j k hjk
      simp only [W,Finset.disjoint_union_left,Finset.disjoint_union_right]
      exact ⟨⟨S.switches hjk,(S.switch_port k (i.succAbove j)).symm⟩,
        ⟨S.switch_port j (i.succAbove k),
          S.ports (fun he ↦ hjk (Fin.succAbove_right_injective he))⟩⟩
    obtain ⟨M⟩ := matching_biUnion Finset.univ W hwm (fun _ _ _ _ h ↦ hwd h)
    obtain ⟨N⟩ := S.star_matching i
    have hd : Disjoint ((S.common ∪ S.port i) ∪ S.root i) (Finset.univ.biUnion W) := by
      apply Finset.disjoint_left.mpr
      intro v hv hw
      obtain ⟨j,_,hvj⟩ := Finset.mem_biUnion.mp hw
      rcases Finset.mem_union.mp hvj with hvj | hvj
      · rcases Finset.mem_union.mp hv with hv | hv
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact Finset.disjoint_left.mp (S.switch_common j) hvj hv
          · exact Finset.disjoint_left.mp (S.switch_port j i) hvj hv
        · exact Finset.disjoint_left.mp (S.switch_root j i) hvj hv
      · rcases Finset.mem_union.mp hv with hv | hv
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact Finset.disjoint_left.mp (S.common_port (i.succAbove j)) hv hvj
          · exact Finset.disjoint_left.mp (S.ports (Fin.ne_succAbove i j)) hv hvj
        · exact Finset.disjoint_left.mp (S.root_port i (i.succAbove j)) hv hvj
    have heq : (((S.common ∪ S.port i) ∪ S.root i) ∪ Finset.univ.biUnion W) =
        S.interior ∪ S.root i := by
      ext v
      simp only [StarPath.interior,Finset.mem_union,Finset.mem_biUnion,Finset.mem_univ,
        true_and,W]
      constructor
      · rintro (((hv | hv) | hv) | ⟨j,hv | hv⟩)
        · exact Or.inl (Or.inl (Or.inl hv))
        · exact Or.inl (Or.inl (Or.inr ⟨i,hv⟩))
        · exact Or.inr hv
        · exact Or.inl (Or.inr ⟨j,hv⟩)
        · exact Or.inl (Or.inl (Or.inr ⟨_,hv⟩))
      · rintro (((hv | ⟨j,hv⟩) | ⟨j,hv⟩) | hv)
        · exact Or.inl (Or.inl (Or.inl hv))
        · by_cases hj : j = i
          · subst j; exact Or.inl (Or.inl (Or.inr hv))
          · obtain ⟨l,hl⟩ := Fin.exists_succAbove_eq hj
            exact Or.inr ⟨l,Or.inr (hl ▸ hv)⟩
        · exact Or.inr ⟨j,Or.inl hv⟩
        · exact Or.inl (Or.inr hv)
    exact ⟨heq ▸ N.union M hd⟩

theorem StarPath.interior_card_le {P : Vertex G → Prop} {n : ℕ} (S : StarPath P n)
    (hc : S.common.card ≤ 2) (hp : ∀ i, (S.port i).card ≤ 2)
    (hs : ∀ j, (S.switchInterior j).card ≤ 4) :
    S.interior.card ≤ 6*(n+1)-2 := by
  have hport : (Finset.univ.biUnion S.port).card ≤ 2*(n+1) := by
    simpa [Nat.mul_comm] using Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin (n+1))) S.port 2 (fun i _ ↦ hp i)
  have hswitch : (Finset.univ.biUnion S.switchInterior).card ≤ 4*n := by
    simpa [Nat.mul_comm] using Finset.card_biUnion_le_card_mul
      (Finset.univ : Finset (Fin n)) S.switchInterior 4 (fun i _ ↦ hs i)
  have h₁ := Finset.card_union_le S.common (Finset.univ.biUnion S.port)
  have h₂ := Finset.card_union_le (S.common ∪ Finset.univ.biUnion S.port)
    (Finset.univ.biUnion S.switchInterior)
  change ((S.common ∪ Finset.univ.biUnion S.port) ∪ Finset.univ.biUnion S.switchInterior).card ≤ _
  omega

end
end EndpointSelector.Assembly
