import CorralFormalization.DiversityCompletion.LatinConnectorPrefix

namespace CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy

open Finset LatinTransfer TerraceLift LatinPrefix

/-- Counting selection lemma for two injective color maps and at most one
candidate making their colors equal. All forbidden sets are actual Finsets. -/
theorem exists_fresh_of_card {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S V : Finset α) (D : Finset β) (f g : α → β)
    (hf : Set.InjOn f S) (hg : Set.InjOn g S)
    (heq : ∀ x ∈ S, ∀ y ∈ S, f x=g x → f y=g y → x=y)
    (hcount : (S ∩ V).card+2*D.card+1 < S.card) :
    ∃ y ∈ S, y ∉ V ∧ f y ∉ D ∧ g y ∉ D ∧ f y ≠ g y := by
  classical
  let F := S.filter (fun x => f x ∈ D)
  let G := S.filter (fun x => g x ∈ D)
  let E := S.filter (fun x => f x = g x)
  have hF : F.card ≤ D.card := by
    apply card_le_card_of_injOn f
    · intro x hx
      exact (mem_filter.mp hx).2
    · exact hf.mono (fun _ hx => (mem_filter.mp hx).1)
  have hG : G.card ≤ D.card := by
    apply card_le_card_of_injOn g
    · intro x hx
      exact (mem_filter.mp hx).2
    · exact hg.mono (fun _ hx => (mem_filter.mp hx).1)
  have hE : E.card ≤ 1 := by
    apply card_le_one.mpr
    intro x hx y hy
    exact heq x (mem_filter.mp hx).1 y (mem_filter.mp hy).1
      (mem_filter.mp hx).2 (mem_filter.mp hy).2
  have hb : ((S ∩ V) ∪ F ∪ G ∪ E).card < S.card := by
    have h1 := card_union_le (S ∩ V) F
    have h2 := card_union_le ((S ∩ V) ∪ F) G
    have h3 := card_union_le ((S ∩ V) ∪ F ∪ G) E
    omega
  obtain ⟨y,hy,hbad⟩ := exists_mem_notMem_of_card_lt_card hb
  refine ⟨y,hy,?_,?_,?_,?_⟩
  · intro hv
    exact hbad (mem_union_left _ (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨hy,hv⟩))))
  · intro hd
    exact hbad (mem_union_left _ (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hy,hd⟩))))
  · intro hd
    exact hbad (mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hy,hd⟩)))
  · intro he
    exact hbad (mem_union_right _ (mem_filter.mpr ⟨hy,he⟩))

/-- Genuine one-step connector selection from consumed vertices and colors.
No connector family, global path, or rainbow-extension conclusion is assumed. -/
theorem exists_two_wrap_connector (n P N : ℕ) (S V D : Finset ℕ)
    (horder : ∀ y ∈ S, P<y ∧ y<N ∧ N<n)
    (hcount : (S ∩ V).card+2*D.card+1 < S.card) :
    ∃ y ∈ S, y ∉ V ∧ wrapOut n y N ∉ D ∧ wrapIn n y P ∉ D ∧
      wrapOut n y N ≠ wrapIn n y P ∧
      0 < wrapOut n y N ∧ wrapOut n y N < n ∧
      0 < wrapIn n y P ∧ wrapIn n y P < n := by
  have hf : Set.InjOn (fun y => wrapOut n y N) S := by
    intro x hx y hy he
    obtain ⟨_,_,hN⟩ := horder x hx
    dsimp [wrapOut] at he
    omega
  have hg : Set.InjOn (fun y => wrapIn n y P) S := by
    intro x hx y hy he
    obtain ⟨_,hxN,hN⟩ := horder x hx
    obtain ⟨_,hyN,_⟩ := horder y hy
    dsimp [wrapIn] at he
    omega
  have heq : ∀ x ∈ S, ∀ y ∈ S,
      wrapOut n x N=wrapIn n x P → wrapOut n y N=wrapIn n y P → x=y := by
    intro x hx y hy hxEq hyEq
    obtain ⟨_,hxN,hN⟩ := horder x hx
    obtain ⟨_,hyN,_⟩ := horder y hy
    dsimp [wrapOut,wrapIn] at hxEq hyEq
    omega
  obtain ⟨y,hy,hv,hfD,hgD,hne⟩ := exists_fresh_of_card S V D
    (fun y => wrapOut n y N) (fun y => wrapIn n y P) hf hg heq hcount
  obtain ⟨hP,hyN,hN⟩ := horder y hy
  obtain ⟨ho0,hoN,hi0,hiN,_⟩ := two_wrap_geometry n P N y hP hyN hN
  exact ⟨y,hy,hv,hfD,hgD,hne,ho0,hoN,hi0,hiN⟩

end CorralFormalization.LatinCompletion.LatinPrefixSupply.ConnectorGreedy
