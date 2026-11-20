import CorralFormalization.DiversityCompletion.FixedSeedCorralClock
import CorralFormalization.DiversityCompletion.EvenLabelCount

/-! Realize each locally valid fixed-seed assembly as an actual optimal
CorralRows object, retaining exactly the physical unordered row family. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

def physicalCorralFamily (m : ℕ) (R : CorralRows (height m) (order m)) :
    Finset (Finset (ZMod (clock m))) :=
  Finset.univ.image (fun i => physicalSites (clock m) (R.sites i))

theorem fixedSeed_realization (m : ℕ)
    (D : FixedSeedSupport (ZMod (clock m)) (NonzeroPhase m) (EvenLetter m))
    (hseedcard : D.fixedRows.card = 2)
    (hcard : ∀ j a, (D.letters j a).card = 2)
    (hfixed : ∀ S ∈ D.fixedRows, ∀ V ∈ D.fixedRows, S ≠ V → Disjoint S V)
    (hlocal : ∀ j a S, S ∈ D.letters j a →
      ∀ V, V ∈ D.letters j a → S ≠ V → Disjoint S V)
    (hfixedgap : ∀ S ∈ D.fixedRows,
      finiteCyclicGapInventory (clock m) (S.image ZMod.val) = Multiset.ofList (fullGapList (order m)))
    (hgap : ∀ j a S, S ∈ D.letters j a →
      finiteCyclicGapInventory (clock m) (S.image ZMod.val) = Multiset.ofList (fullGapList (order m))) :
    ∃ C : (NonzeroPhase m → EvenLetter m) → CorralRows (height m) (order m),
      ∀ t, physicalCorralFamily m (C t) = D.assembleFixed t := by
  classical
  let : NeZero (clock m) := ⟨by unfold clock height order; positivity⟩
  have hc := Fintype.card_congr (phaseEquiv m)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
  have hp : Fintype.card (NonzeroPhase m) = 2*m := by omega
  have hsize : D.fixedRows.card + Fintype.card (NonzeroPhase m)*2 = height m := by
    rw [hseedcard, hp]
    unfold height
    omega
  have heach (t : NonzeroPhase m → EvenLetter m) :
      ∃ R : CorralRows (height m) (order m),
        Finset.univ.image R.sites = (D.assembleFixed t).image (fun S => S.image ZMod.val) := by
    rw [← hsize]
    exact fixedSeed_to_corralRows_clock (optimal_width m) D t hcard hfixed hlocal hfixedgap hgap
  choose C hC using heach
  refine ⟨C, ?_⟩
  intro t
  have hp := congrArg (fun F : Finset (Finset ℕ) =>
    F.image (fun S => physicalSites (clock m) S)) (hC t)
  simpa only [physicalCorralFamily, Finset.image_image, Function.comp_def,
    physicalSites_encode, Finset.image_id'] using hp

end CorralFormalization.EvenSwitches
