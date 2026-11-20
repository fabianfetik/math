import CorralFormalization.DiversityCompletion.EvenConcreteAssembly
import CorralFormalization.DiversityCompletion.EvenPhysicalRealization

/-! Every member of the literal fixed-seed switching family is an actual
optimal CorralRows object, with exactly the constructed unlabelled rows. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry EvenSupportPartition

theorem concrete_seed_gap_inventory (m : ℕ) :
    finiteCyclicGapInventory (clock m) ((baseRow m).image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  have h := evenConstructionSeed_inventory (2*m+1) (by omega)
  unfold evenConstructionSeed at h
  rw [← switchClock_eq_evenConstructionClock m] at h
  have ho : 4*(2*m+1)-1 = order m := by unfold order; omega
  simpa only [baseRow, ho] using h

theorem concrete_reflected_seed_gap_inventory (m : ℕ) :
    finiteCyclicGapInventory (clock m)
      (((Motion.reflection ((height m)^2-1 : ℕ)).onRow (baseRow m)).image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  have hW : 0 < clock m := by unfold clock height order; positivity
  have ho : 4*(2*m+1)-1 = order m := by unfold order; omega
  have hperm : (evenConstructionGapWord (2*m+1)).Perm (fullGapList (order m)) := by
    simpa only [ho] using evenConstructionGapWord_perm_full (2*m+1) (by omega)
  have hsum : (evenConstructionGapWord (2*m+1)).sum = clock m := by
    rw [← evenConstructionClock_eq_sum (2*m+1) (by omega), ← switchClock_eq_evenConstructionClock m]
  have hp : ∀ x ∈ evenConstructionGapWord (2*m+1), 0 < x := by
    intro x hx
    exact ((fullGapList_mem _ _).mp (hperm.mem_iff.mp hx)).1
  have hcomp : (Motion.reflection ((height m)^2-1 : ℕ) : Motion (clock m)) =
      (Motion.rotation ((height m)^2-1 : ℕ)).compose (Motion.reflection 0) := by
    simp [Motion.compose]
  rw [baseRow, evenConstructionRawPrefixSet, hcomp, Motion.onRow_compose,
    reflected_prefix_eq_reverse _ _ hW hsum hp]
  exact shifted_word_inventory (clock m) (order m) _ hW (by simpa using hsum)
    ((List.reverse_perm _).trans hperm) _

theorem concreteSeedRows_gap_inventory (m : ℕ) (S : Finset (ZMod (clock m)))
    (hS : S ∈ concreteSeedRows m) :
    finiteCyclicGapInventory (clock m) (S.image ZMod.val) =
      Multiset.ofList (fullGapList (order m)) := by
  simp only [concreteSeedRows, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · exact concrete_seed_gap_inventory m
  · exact concrete_reflected_seed_gap_inventory m

/-- Full unconditional realization of all independent actual letter choices
as optimal corrals. The equality retains the exact physical row family. -/
theorem concreteData_realization (m : ℕ) (hm : 1 ≤ m) :
    ∃ F : (NonzeroPhase m → EvenLetter m) → CorralRows (height m) (order m),
      ∀ t, physicalCorralFamily m (F t) = (concreteData m hm).assembleFixed t := by
  apply fixedSeed_realization m (concreteData m hm)
  · exact concreteSeedRows_card m
  · intro j ab
    exact translatedLetter_card m hm j.val.val ab
  · exact concreteSeedRows_disjoint m
  · intro j ab
    exact translatedLetter_rows_disjoint m hm j.val.val ab
  · exact concreteSeedRows_gap_inventory m
  · intro j ab
    exact translatedLetter_gap_inventory m hm j.val.val ab

/-- Count the actual distinct physical partitions before quotienting by
common translations and reflections. No row labels are counted. -/
theorem concreteData_physical_count (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.image (concreteData m hm).assembleFixed).card = 2^(4*m*m) := by
  classical
  rw [Finset.card_image_of_injective _ (concreteData m hm).assembleFixed_injective,
    Finset.card_univ]
  exact evenLabels_total m hm

end CorralFormalization.EvenSwitches
