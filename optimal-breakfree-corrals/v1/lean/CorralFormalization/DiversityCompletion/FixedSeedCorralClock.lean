import CorralFormalization.DiversityCompletion.FixedSeedAssembly

/-! The fixed-seed construction on a clock given by an explicit equality
`width n = M`, without relying on definitional equality of the clocks. -/

namespace CorralFormalization.PhysicalCorral

theorem fixedSeed_to_corralRows_clock {J A : Type*} [Fintype J] {n M : ℕ} [NeZero M]
    (hclock : width n = M) (D : FixedSeedSupport (ZMod M) J A) (t : J → A)
    (hcard : ∀ j a, (D.letters j a).card = 2)
    (hfixed : ∀ S ∈ D.fixedRows, ∀ V ∈ D.fixedRows, S ≠ V → Disjoint S V)
    (hlocal : ∀ j a S, S ∈ D.letters j a →
      ∀ V, V ∈ D.letters j a → S ≠ V → Disjoint S V)
    (hfixedgap : ∀ S ∈ D.fixedRows,
      finiteCyclicGapInventory M (S.image ZMod.val) = Multiset.ofList (fullGapList n))
    (hgap : ∀ j a S, S ∈ D.letters j a →
      finiteCyclicGapInventory M (S.image ZMod.val) = Multiset.ofList (fullGapList n)) :
    ∃ R : CorralRows (D.fixedRows.card + Fintype.card J * 2) n,
      Finset.univ.image R.sites = (D.assembleFixed t).image (fun S => S.image ZMod.val) := by
  subst M
  obtain ⟨R, hR⟩ := fixedSeed_to_corralRows D t hcard hfixed hlocal hfixedgap hgap
  refine ⟨R, ?_⟩
  rw [← hR, physicalFamily, Finset.image_image]
  apply Finset.image_congr
  intro i _
  exact (physicalSites_decode _ (R.bounded i)).symm

end CorralFormalization.PhysicalCorral
