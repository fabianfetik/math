import CorralFormalization.EndpointProof.Selector.Stars.RotatedSampling

/-! The one-target rotated star supplies genuine fresh P helper pairs. -/

open scoped Classical

namespace EndpointSelector.Stars

open EndpointOriginalReservoir

noncomputable section

variable {G : Type*} [CommRing G] [Fintype G]

/-- No separate P-count event is needed for one fresh helper inverse pair.
The fixed nonzero A-root is chosen before the later star query, and both signs
of the common pair receive the requested actual P-part label. -/
theorem exists_P_pair_of_rotated_star_available
    (hodd : Odd (Fintype.card G)) (hn : 1000 ≤ Fintype.card G)
    (budget : ℕ) (ω : EndpointFullProduct.FullSample G)
    (hgood : EndpointFullProduct.FullAvailable
      (rotatedStarQueryEmbedding (k := 1) (by omega) hodd hn)
      (fun r _ ↦ rotatedStarDemand r.1) budget ω)
    (p : Part) (F : Finset G) (hF : F.card ≤ budget) :
    ∃ u : G, u ≠ 0 ∧ Disjoint ({u,-u} : Finset G) F ∧
      PVertex ω (p,u) ∧ PVertex ω (p,-u) := by
  have hnonzero : ∃ a : G, a ≠ 0 := by
    by_contra hall
    push Not at hall
    have hcard : Fintype.card G ≤ 1 := by
      simpa using Fintype.card_le_of_injective (fun _ : G ↦ ())
        (by intro x y _; rw [hall x,hall y])
    omega
  obtain ⟨a,ha⟩ := hnonzero
  let r : StarQuery G 1 := ⟨fun _ ↦ a,by
    refine ⟨fun _ ↦ ha,?_⟩
    intro i j hij
    exact False.elim (hij (Subsingleton.elim i j))⟩
  let σ : Equiv.Perm Part := Equiv.swap 1 p
  obtain ⟨u,hv,hd,hP,_,_⟩ :=
    successful_rotated_star_of_fullAvailable (by omega : 1 ≤ 3)
      hodd hn budget ω hgood r σ F hF
  refine ⟨u,hv.1 none,?_,?_,?_⟩
  · apply Finset.disjoint_left.mpr
    intro x hx hxF
    have hxs : x ∈ starSupport r.val u := by
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact (mem_starSupport _ _ _).2 ⟨none,Or.inl rfl⟩
      · have he : x = -u := Finset.mem_singleton.mp hx
        exact (mem_starSupport _ _ _).2 ⟨none,Or.inr he⟩
    exact Finset.disjoint_left.mp hd hxs hxF
  · have hp := (hP (1,u) (starCommonPair_subset_interior r.val u
      (by simp [starCommonPair]))).1
    simpa [σ] using hp
  · have hp := (hP (1,-u) (starCommonPair_subset_interior r.val u
      (by simp [starCommonPair]))).1
    simpa [σ] using hp

end
end EndpointSelector.Stars
