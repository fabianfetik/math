import CorralFormalization.DiversityCompletion.EvenAlphabetValidity
import CorralFormalization.DiversityCompletion.CarrierEvenSupport
import CorralFormalization.DiversityCompletion.EvenLabelCount
import CorralFormalization.DiversityCompletion.FixedSeedCorralClock

/-! The actual fixed-seed support alphabet, with every support, local row,
gap inventory and decoding field supplied by the concrete construction. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral DiversitySymmetry EvenSupportPartition

instance concreteClockNonzero (m : ℕ) : NeZero (clock m) :=
  ⟨by unfold clock height order; positivity⟩

theorem concrete_period_eq (m : ℕ) : evenConstructionPeriod (2*m+1) = 2*order m := by
  unfold evenConstructionPeriod order
  omega

/-- The real old two-row support, translated by the physical period. -/
def concreteSupport (m : ℕ) (j : ZMod (2*m+1)) : Finset (ZMod (clock m)) :=
  (Motion.rotation (2*order m*j.val : ℕ)).onRow (oldCarrier m)

theorem concreteSupport_zero (m : ℕ) : concreteSupport m 0 = oldCarrier m := by
  simp [concreteSupport]

theorem concreteSupport_disjoint (m : ℕ) (i j : ZMod (2*m+1)) (hij : i ≠ j) :
    Disjoint (concreteSupport m i) (concreteSupport m j) := by
  have h := supportAt_disjoint m i j hij
  simp only [supportAt, periodStride_val, evenSupportCarrier, evenConstructionSeed,
    concrete_period_eq] at h
  rw [← switchClock_eq_evenConstructionClock m] at h
  simpa only [concreteSupport, oldCarrier, baseRow] using h

theorem concreteSupport_partition (m : ℕ) (x : ZMod (clock m)) :
    ∃! j : ZMod (2*m+1), x ∈ concreteSupport m j := by
  have h : ∀ y : ZMod (evenConstructionClock (2*m+1)), ∃! j, y ∈ supportAt m j :=
    fun y => supportAt_partition m y
  simp only [supportAt, periodStride_val, evenSupportCarrier, evenConstructionSeed, concrete_period_eq] at h
  rw [← switchClock_eq_evenConstructionClock m] at h
  simpa only [concreteSupport, oldCarrier, baseRow] using h x

theorem concreteSupport_coverage (m : ℕ) :
    Finset.univ.biUnion (concreteSupport m) = (Finset.univ : Finset (ZMod (clock m))) := by
  ext x
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
  obtain ⟨j, hj, _⟩ := concreteSupport_partition m x
  exact ⟨j, hj⟩

theorem oldCarrier_reflection (m : ℕ) :
    (Motion.reflection ((height m)^2-1 : ℕ)).onRow (oldCarrier m) = oldCarrier m := by
  unfold oldCarrier
  simp only [Motion.onRow, Finset.image_union]
  change (Motion.reflection ((height m)^2-1 : ℕ)).onRow (baseRow m) ∪
    (Motion.reflection ((height m)^2-1 : ℕ)).onRow
      ((Motion.reflection ((height m)^2-1 : ℕ)).onRow (baseRow m)) = _
  rw [Motion.reflection_onRow_involutive]
  exact Finset.union_comm _ _

theorem motion_family_union {M : ℕ} (f : Motion M) (F : Finset (Finset (ZMod M))) :
    (f.onFamily F).biUnion id = f.onRow (F.biUnion id) := by
  simp only [Motion.onFamily, Motion.onRow, Finset.image_biUnion, Finset.biUnion_image, id_eq]

theorem motion_family_disjoint {M : ℕ} (f : Motion M) (F : Finset (Finset (ZMod M)))
    (hF : ∀ S ∈ F, ∀ V ∈ F, S ≠ V → Disjoint S V) :
    ∀ S ∈ f.onFamily F, ∀ V ∈ f.onFamily F, S ≠ V → Disjoint S V := by
  intro S hS V hV hSV
  obtain ⟨R, hR, rfl⟩ := Finset.mem_image.mp hS
  obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hV
  exact (Finset.disjoint_image (Motion.act_injective f)).mpr
    (hF R hR T hT (fun hRT => hSV (congrArg f.onRow hRT)))

theorem baseLetter_coverage (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    (baseLetter m a).biUnion id = oldCarrier m := by
  simpa [baseLetter] using (physical_rows_partition_old m hm a).2

theorem baseLetter_rows_disjoint (m : ℕ) (hm : 1 ≤ m) (a : Choices m) :
    ∀ S ∈ baseLetter m a, ∀ V ∈ baseLetter m a, S ≠ V → Disjoint S V := by
  intro S hS V hV hSV
  simp only [baseLetter, Finset.mem_insert, Finset.mem_singleton] at hS hV
  rcases hS with rfl | rfl <;> rcases hV with rfl | rfl
  · exact (hSV rfl).elim
  · exact (physical_rows_partition_old m hm a).1
  · exact (physical_rows_partition_old m hm a).1.symm
  · exact (hSV rfl).elim

theorem alphabetLetter_coverage (m : ℕ) (hm : 1 ≤ m) (ab : EvenLetter m) :
    (alphabetLetter m ab).biUnion id = oldCarrier m := by
  rcases ab with ⟨a, b⟩
  cases b
  · exact baseLetter_coverage m hm a
  · change ((Motion.reflection ((height m)^2-1 : ℕ)).onFamily (baseLetter m a)).biUnion id = _
    rw [motion_family_union, baseLetter_coverage m hm a, oldCarrier_reflection]

theorem alphabetLetter_rows_disjoint (m : ℕ) (hm : 1 ≤ m) (ab : EvenLetter m) :
    ∀ S ∈ alphabetLetter m ab, ∀ V ∈ alphabetLetter m ab, S ≠ V → Disjoint S V := by
  rcases ab with ⟨a, b⟩
  cases b
  · exact baseLetter_rows_disjoint m hm a
  · exact motion_family_disjoint _ _ (baseLetter_rows_disjoint m hm a)

theorem translatedLetter_coverage (m : ℕ) (hm : 1 ≤ m)
    (j : ZMod (2*m+1)) (ab : EvenLetter m) :
    (translatedLetter m j.val ab).biUnion id = concreteSupport m j := by
  rw [translatedLetter, motion_family_union, alphabetLetter_coverage m hm ab]
  rfl

theorem translatedLetter_rows_disjoint (m : ℕ) (hm : 1 ≤ m)
    (j : ℕ) (ab : EvenLetter m) :
    ∀ S ∈ translatedLetter m j ab, ∀ V ∈ translatedLetter m j ab,
      S ≠ V → Disjoint S V :=
  motion_family_disjoint _ _ (alphabetLetter_rows_disjoint m hm ab)

def concreteSeedRows (m : ℕ) : Finset (Finset (ZMod (clock m))) :=
  {baseRow m, (Motion.reflection ((height m)^2-1 : ℕ)).onRow (baseRow m)}

theorem concreteSeedRows_nonempty (m : ℕ) :
    ∀ S ∈ concreteSeedRows m, S.Nonempty := by
  have hn : (baseRow m).Nonempty := Finset.card_pos.mp (by rw [baseRow_card]; unfold order; omega)
  intro S hS
  simp only [concreteSeedRows, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · exact hn
  · exact hn.image _

theorem concreteSeedRows_subset (m : ℕ) :
    ∀ S ∈ concreteSeedRows m, S ⊆ oldCarrier m := by
  intro S hS
  simp only [concreteSeedRows, Finset.mem_insert, Finset.mem_singleton] at hS
  rcases hS with rfl | rfl
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

theorem concreteSeedRows_disjoint (m : ℕ) :
    ∀ S ∈ concreteSeedRows m, ∀ V ∈ concreteSeedRows m, S ≠ V → Disjoint S V := by
  intro S hS V hV hSV
  simp only [concreteSeedRows, Finset.mem_insert, Finset.mem_singleton] at hS hV
  rcases hS with rfl | rfl <;> rcases hV with rfl | rfl
  · exact (hSV rfl).elim
  · exact old_seed_reflection_disjoint m
  · exact (old_seed_reflection_disjoint m).symm
  · exact (hSV rfl).elim

theorem concreteSeedRows_card (m : ℕ) : (concreteSeedRows m).card = 2 := by
  have hn : (baseRow m).Nonempty := Finset.card_pos.mp (by rw [baseRow_card]; unfold order; omega)
  have hne : baseRow m ≠ (Motion.reflection ((height m)^2-1 : ℕ)).onRow (baseRow m) := by
    intro he
    obtain ⟨x, hx⟩ := hn
    exact Finset.disjoint_left.mp (old_seed_reflection_disjoint m) hx (he ▸ hx)
  simp [concreteSeedRows, hne]

/-- All fields are proved for the literal supports and literal two-row
decompositions; no local-support, gap or decoder hypothesis is supplied. -/
def concreteData (m : ℕ) (hm : 1 ≤ m) :
    FixedSeedSupport (ZMod (clock m)) (NonzeroPhase m) (EvenLetter m) where
  support j := concreteSupport m j.val
  disjoint i j hij := concreteSupport_disjoint m i.val j.val
    (fun h => hij (Subtype.ext h))
  letters j ab := translatedLetter m j.val.val ab
  nonempty j ab S hS := translatedLetter_rows_nonempty m hm j.val.val ab S hS
  subset j ab S hS := by
    intro x hx
    have hx' : x ∈ (translatedLetter m j.val.val ab).biUnion id :=
      Finset.mem_biUnion.mpr ⟨S, hS, hx⟩
    simpa only [translatedLetter_coverage m hm j.val ab] using hx'
  distinct j := translatedLetter_injective m hm j.val.val
  fixedSupport := oldCarrier m
  fixedRows := concreteSeedRows m
  fixed_disjoint j := by
    rw [← concreteSupport_zero m]
    exact concreteSupport_disjoint m 0 j.val (Ne.symm j.property)
  fixed_nonempty := concreteSeedRows_nonempty m
  fixed_subset := concreteSeedRows_subset m

end CorralFormalization.EvenSwitches
