import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Merge
import CorralFormalization.EndpointProof.Factor.OrdinaryFragments.Donors

/-!
# Attach every extra component to a distinct original primary donor

The finite induction concatenates actual path lists. A selected source
component is primary and the selected target is extra, so they cannot be
the same component. Both physical simplicity and rainbow colour use are
maintained at every join.
-/

open scoped Classical BigOperators symmDiff
namespace EndpointFactor.OrdinaryFragments
noncomputable section
universe u v
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

namespace Family

/-- Complete attachment for any finite family of extra starts. Every
chosen donor is an actual original primary end. The output inventories
state exactly which starts, ends and colours were changed. -/
theorem attach_all {I : Type v} [DecidableEq I] (s : Finset I)
    (g a : I → G) :
    ∀ F : Family G, ∀ B : Finset G,
    Set.InjOn g (s : Set I) → Set.InjOn a (s : Set I) →
    Set.InjOn (fun e => g e-a e) (s : Set I) →
    F.starts = B ∪ s.image g → Disjoint B (s.image g) →
    (∀ e ∈ s, a e ∈ F.primaryEnds B) →
    (∀ e ∈ s, g e-a e ∉ F.colors) →
    ∃ F' : Family G, F'.vertices = F.vertices ∧
      F'.colors = F.colors ∪ s.image (fun e => g e-a e) ∧
      F'.starts = B ∧ F'.ends = F.ends \ s.image a := by
  induction s using Finset.induction with
  | empty =>
    intro F B _ _ _ hstarts _ _ _
    exact ⟨F, rfl, by simp, by simpa using hstarts, by simp⟩
  | @insert e s he ih =>
    intro F B hg ha hc hstarts hBg hdonor hfresh
    have hem : e ∈ insert e s := Finset.mem_insert_self _ _
    have hnotB : g e ∉ B := by
      intro h
      exact Finset.disjoint_left.mp hBg h (Finset.mem_image.mpr ⟨e, hem, rfl⟩)
    have hnotg : g e ∉ s.image g := by
      rintro h
      obtain ⟨k, hk, hkg⟩ := Finset.mem_image.mp h
      exact he ((hg (Finset.mem_insert_of_mem hk) hem hkg) ▸ hk)
    obtain ⟨i, hiB, hia⟩ := (F.mem_primaryEnds B (a e)).mp (hdonor e hem)
    have hge : g e ∈ F.starts := by
      rw [hstarts]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, hem, rfl⟩)
    obtain ⟨j, hjg⟩ := (F.mem_starts _).mp hge
    have hjB : F.first j ∉ B := by simpa [hjg] using hnotB
    have hij : i ≠ j := by intro h; exact hjB (h ▸ hiB)
    have hcolor : F.joinColor i j = g e-a e := by simp only [joinColor, hjg, hia]
    have hcf : F.joinColor i j ∉ F.colors := by rw [hcolor]; exact hfresh e hem
    let F₁ := F.merge i j hij hcf
    have hV₁ : F₁.vertices = F.vertices := F.merge_vertices i j hij hcf
    have hC₁ : F₁.colors = insert (g e-a e) F.colors := by
      rw [Family.merge_colors, hcolor]
    have hS₁ : F₁.starts = B ∪ s.image g := by
      rw [Family.merge_starts, hjg, hstarts, Finset.image_insert,
        Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnotB, Finset.erase_insert hnotg]
    have hE₁ : F₁.ends = F.ends.erase (a e) := by rw [Family.merge_ends, hia]
    have hsub : (s : Set I) ⊆ (↑(insert e s) : Set I) := by
      intro k hk
      exact Finset.mem_insert_of_mem hk
    have hBg₁ : Disjoint B (s.image g) :=
      Finset.disjoint_of_subset_right (Finset.image_subset_image (Finset.subset_insert _ _)) hBg
    have hdonor₁ : ∀ k ∈ s, a k ∈ F₁.primaryEnds B := by
      intro k hk
      apply F.merge_preserves_primaryEnds i j hij hcf B hjB (hdonor k (Finset.mem_insert_of_mem hk))
      intro h
      have hke : k = e := ha (Finset.mem_insert_of_mem hk) hem (h.trans hia)
      exact he (hke ▸ hk)
    have hfresh₁ : ∀ k ∈ s, g k-a k ∉ F₁.colors := by
      intro k hk h
      rw [hC₁, Finset.mem_insert] at h
      rcases h with h | h
      · have hke : k = e := hc (Finset.mem_insert_of_mem hk) hem h
        exact he (hke ▸ hk)
      · exact hfresh k (Finset.mem_insert_of_mem hk) h
    obtain ⟨F₂, hV₂, hC₂, hS₂, hE₂⟩ := ih F₁ B (hg.mono hsub) (ha.mono hsub)
      (hc.mono hsub) hS₁ hBg₁ hdonor₁ hfresh₁
    refine ⟨F₂, hV₂.trans hV₁, ?_, hS₂, ?_⟩
    · rw [hC₂, hC₁, Finset.image_insert]
      ext c
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    · rw [hE₂, hE₁, Finset.image_insert]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_erase, Finset.mem_insert]
      tauto

/-- The actual extra start inventory is a bijective image of the original
extra keys, rather than an arbitrary list with the same length. -/
theorem starts_eq_primary_union_extras (F : Family G) (B : Finset G)
    (hB : B ⊆ F.starts) :
    F.starts = B ∪ (F.extras B).image F.first := by
  ext x
  rw [Finset.mem_union, Finset.mem_image, F.mem_starts]
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hiB : F.first i ∈ B
    · exact Or.inl hiB
    · exact Or.inr ⟨i, (F.mem_extras B i).mpr hiB, rfl⟩
  · rintro (hx | ⟨i, _, hi⟩)
    · exact (F.mem_starts x).mp (hB hx)
    · exact ⟨i, hi⟩

theorem primary_disjoint_extra_starts (F : Family G) (B : Finset G) :
    Disjoint B ((F.extras B).image F.first) := by
  apply Finset.disjoint_left.mpr
  intro x hx hx'
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx'
  exact (F.mem_extras B i).mp hi hx

/-- Attach all genuine extras using the donors produced from the original
bank. Every original prescribed `Y` end survives because it is explicitly
excluded from the donor inventory. -/
theorem attach_extras (F : Family G) (B Z Y H₀ : Finset G)
    (hB : B ⊆ F.starts) (hZ : Z ⊆ F.primaryEnds B) (hY : Y ⊆ F.ends)
    (hH : Disjoint H₀ F.colors)
    (a : F.extras B → G)
    (ha : ∀ e, a e ∈ Z ∧ a e ∉ Y ∧ F.first e.val-a e ∈ H₀)
    (hainj : Function.Injective a)
    (hcinj : Function.Injective (fun e => F.first e.val-a e)) :
    ∃ F' : Family G,
      F'.vertices = F.vertices ∧
      F'.colors = F.colors ∪ Finset.univ.image (fun e => F.first e.val-a e) ∧
      F'.starts = B ∧
      F'.ends = F.ends \ Finset.univ.image a ∧ Y ⊆ F'.ends ∧
      Fintype.card F'.Index = B.card ∧
      (Finset.univ.image a).card = (F.extras B).card ∧
      (Finset.univ.image (fun e => F.first e.val-a e)).card = (F.extras B).card := by
  let g : F.extras B → G := fun e => F.first e.val
  have hg : Function.Injective g := by
    intro e f h
    exact Subtype.ext (F.first_injective h)
  have hstarts : F.starts = B ∪ Finset.univ.image g := by
    have he : Finset.univ.image g = (F.extras B).image F.first := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, g]
      constructor
      · rintro ⟨e, he⟩
        exact ⟨e.val, e.property, he⟩
      · rintro ⟨e, he, hex⟩
        exact ⟨⟨e, he⟩, hex⟩
    rw [he]
    exact F.starts_eq_primary_union_extras B hB
  have hBg : Disjoint B (Finset.univ.image g) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hx'
    exact (F.mem_extras B e.val).mp e.property hx
  obtain ⟨F', hV, hC, hS, hE⟩ := attach_all Finset.univ g a F B hg.injOn hainj.injOn hcinj.injOn
    hstarts hBg (fun e _ => hZ (ha e).1)
    (fun e _ h => Finset.disjoint_left.mp hH (ha e).2.2 h)
  refine ⟨F', hV, hC, hS, hE, ?_, ?_, ?_, ?_⟩
  · rw [hE]
    intro y hy
    apply Finset.mem_sdiff.mpr
    refine ⟨hY hy, ?_⟩
    rintro h
    obtain ⟨e, _, he⟩ := Finset.mem_image.mp h
    exact (ha e).2.1 (he.symm ▸ hy)
  · rw [← F'.starts_card, hS]
  · rw [Finset.card_image_of_injective _ hainj, Finset.card_univ, Fintype.card_coe]
  · rw [Finset.card_image_of_injective _ hcinj, Finset.card_univ, Fintype.card_coe]

end Family
end
end EndpointFactor.OrdinaryFragments
