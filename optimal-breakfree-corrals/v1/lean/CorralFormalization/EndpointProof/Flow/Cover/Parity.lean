import CorralFormalization.EndpointProof.Flow.Cover.Partition

/-!
An odd-order, nonzero paired set has an even number of vertices in each
part. Together with balance and the paired-cover size bound, this gives the exact
`m`-pairs-per-part and `m ≤ |S|` conclusion.
-/

open scoped Classical

namespace EndpointFlow.Cover

open EndpointSelector

noncomputable section

/-- A finite set stable under a fixed-point-free involution has even size. -/
theorem even_card_of_free_involution {α : Type*} [DecidableEq α]
    (S : Finset α) (f : α → α) (hf : Function.Involutive f)
    (hmem : ∀ x ∈ S, f x ∈ S) (hfree : ∀ x ∈ S, f x ≠ x) : Even S.card := by
  revert hmem hfree
  induction S using Finset.strongInduction with
  | H S ih =>
    intro hmem hfree
    by_cases hS : S = ∅
    · simp [hS]
    · obtain ⟨x,hx⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      have hfx : f x ∈ S := hmem x hx
      have hne : f x ≠ x := hfree x hx
      let R := (S.erase x).erase (f x)
      have hRsub : R ⊆ S := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      have hRlt : R ⊂ S := by
        apply (Finset.ssubset_iff_of_subset hRsub).2
        exact ⟨x,hx,by simp [R]⟩
      have hmemR : ∀ y ∈ R, f y ∈ R := by
        intro y hy
        have hyfx : y ≠ f x := (Finset.mem_erase.mp hy).1
        have hyx : y ≠ x := (Finset.mem_erase.mp (Finset.mem_erase.mp hy).2).1
        have hyS : y ∈ S := hRsub hy
        have hf_ne_x : f y ≠ x := by
          intro he
          have : y = f x := by rw [← he, hf y]
          exact hyfx this
        have hf_ne_fx : f y ≠ f x := fun he ↦ hyx (hf.injective he)
        apply Finset.mem_erase.mpr
        refine ⟨hf_ne_fx,?_⟩
        exact Finset.mem_erase.mpr ⟨hf_ne_x,hmem y hyS⟩
      have hfreeR : ∀ y ∈ R, f y ≠ y := fun y hy ↦ hfree y (hRsub hy)
      obtain ⟨m,hm⟩ := ih R hRlt hmemR hfreeR
      have hfxerase : f x ∈ S.erase x := Finset.mem_erase.mpr ⟨hne,hfx⟩
      have hcard : R.card + 2 = S.card := by
        dsimp [R]
        rw [Finset.card_erase_of_mem hfxerase, Finset.card_erase_of_mem hx]
        have hpos : 0 < (S.erase x).card := Finset.card_pos.mpr ⟨f x,hfxerase⟩
        rw [Finset.card_erase_of_mem hx] at hpos
        omega
      refine ⟨m+1,?_⟩
      omega

variable {G : Type*} [CommRing G] [Fintype G]

theorem paired_part_card_even (hodd : Odd (Fintype.card G))
    (T : Finset (Vertex G))
    (hpair : ∀ v ∈ T, (v.1,-v.2) ∈ T)
    (hnonzero : ∀ v ∈ T, v.2 ≠ 0) (p : Fin 3) :
    Even (partSlice T p).card := by
  apply even_card_of_free_involution (partSlice T p) (fun v ↦ (v.1,-v.2))
  · intro v; simp
  · intro v hv
    have hv' := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨hpair v hv'.1,hv'.2⟩
  · intro v hv heq
    have hvT := (Finset.mem_filter.mp hv).1
    exact (ne_neg_of_odd hodd (hnonzero v hvT)) (congrArg Prod.snd heq).symm

/-- Every part contains exactly `m` inverse pairs and the number of pairs
per part is at most the size of the original balanced set. -/
theorem paired_balanced_pair_count (hodd : Odd (Fintype.card G))
    (T : Finset (Vertex G)) (hb : Balanced T)
    (hpair : ∀ v ∈ T, (v.1,-v.2) ∈ T)
    (hnonzero : ∀ v ∈ T, v.2 ≠ 0) (s : ℕ) (hsize : T.card ≤ 6*s) :
    ∃ m : ℕ, (∀ p : Fin 3, (partSlice T p).card = 2*m) ∧ m ≤ s := by
  obtain ⟨m,hm⟩ := paired_part_card_even hodd T hpair hnonzero 0
  refine ⟨m,?_,?_⟩
  · intro p
    have hp := hb p
    omega
  · have htotal := balanced_card T hb
    omega

end
end EndpointFlow.Cover
