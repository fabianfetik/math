import CorralFormalization.Results.SwitchFamily.Counting.TileSemantics
import CorralFormalization.Results.SwitchFamily.Counting.Orbits
import CorralFormalization.Results.SwitchFamily.AsymmetricSwitchFamily

/-!
# Recovery of actual local-word layouts from physical switched families

Gap-two tails recover the two/three tile endpoints in every physical
row modification. This file connects that existing physical decoder to
`Counting.Layout`, the exact local-word model used in the orbit count.
This is an injectivity result for anchored physical families; the full
rotation-equivariance and orbit equivalence remain separate questions.
-/

namespace CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge

open CorralFormalization.LatinCompletion
open TerraceCompletion TerraceLift GeneralTiles DiversitySymmetry PhysicalCorral
open CorralFormalization.PhysicalCensus
open CorralFormalization.Results.PrimeHeight
open CorralFormalization.Results.SwitchFamily.Counting
open CorralFormalization.Results.SwitchFamily.Physical
open CorralFormalization.Results.SwitchFamily.FamilySwitches
open CorralFormalization.Results.SwitchFamily.MarkerIsolation
open CorralFormalization.Results.SwitchFamily.ConcreteMarkers
open CorralFormalization.Results.SwitchFamily.ConcreteOwners

noncomputable section

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]

theorem tileData_eq_starts (u : Layout h) :
    u.tileData = (u.toCyclicTiling.twoStarts.image (fun p => (p, TileSize.two))) ∪
      (u.toCyclicTiling.threeStarts.image (fun p => (p, TileSize.three))) := by
  classical
  ext ⟨p,s⟩
  cases s <;> simp [Layout.tileData, CyclicTiling.twoStarts, CyclicTiling.threeStarts,
    Layout.toCyclicTiling, Finset.mem_image, Prod.mk.injEq, and_comm]
  all_goals
    constructor
    · rintro ⟨a,b,hp,hs⟩
      exact ⟨a,b,hp,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs⟩⟩
    · rintro ⟨a,b,hp,hs⟩
      exact ⟨a,b,hp,(Finset.mem_filter.mp hs).2⟩

theorem words_eq_of_start_sets_eq (hh : 3 ≤ h) (u v : Layout h)
    (h2 : u.toCyclicTiling.twoStarts = v.toCyclicTiling.twoStarts)
    (h3 : u.toCyclicTiling.threeStarts = v.toCyclicTiling.threeStarts) : u = v := by
  apply Layout.tileData_injective hh
  rw [tileData_eq_starts, tileData_eq_starts, h2, h3]

theorem words_eq_of_rotated_start_sets (hh : 3 ≤ h) (u v : Layout h) (a : ZMod h)
    (h2 : u.toCyclicTiling.twoStarts.image (fun p => a+p) = v.toCyclicTiling.twoStarts)
    (h3 : u.toCyclicTiling.threeStarts.image (fun p => a+p) = v.toCyclicTiling.threeStarts) :
    LocalWord.rotate (-a) u = v := by
  classical
  apply Layout.tileData_injective hh
  rw [Layout.tileData_rotate, tileData_eq_starts, tileData_eq_starts, ← h2, ← h3]
  simp only [Finset.image_union, Finset.image_image, Function.comp_def, sub_neg_eq_add,
    add_comm]

/-- An unlabelled switched physical family uniquely determines its original
cyclic local-word layout, even across different supplied terraces. -/
theorem layout_recovered_from_physical_family (hh : 3 ≤ h) (hn : n = 2*h-1)
    (hsmall : 65 ≤ n) (u v : Layout h) (T U : CompletedTerrace n)
    (P : RowModification n (u.toCyclicTiling.family T))
    (Q : RowModification n (v.toCyclicTiling.family U))
    (heq : P.family = Q.family) : u = v := by
  classical
  obtain ⟨h2,h3⟩ := u.toCyclicTiling.modified_layout_reconstruction v.toCyclicTiling
    T U hn hsmall P Q (congrArg (fun F => familyTails F 2) heq)
  exact words_eq_of_start_sets_eq hh u v h2 h3

/-- Every physical isometry between such families is a translation by a
whole phase and carries the actual local-word layout accordingly. -/
theorem isometry_forces_layout_rotation (hh : 3 ≤ h) (hn : n = 2*h-1)
    (hsmall : 65 ≤ n) (u v : Layout h) (D E : DirectedTerrace n)
    (hD : HasSpecifiedPrefix D) (hE : HasSpecifiedPrefix E)
    (P : RowModification n (u.toCyclicTiling.family (completedOfSpecifiedPrefix D hsmall hD)))
    (Q : RowModification n (v.toCyclicTiling.family (completedOfSpecifiedPrefix E hsmall hE)))
    (f : Motion (h*n)) (hf : f.onFamily P.family = Q.family) :
    ∃ a : ZMod h, f = .rotation (zeroSite h n a) ∧
      LocalWord.rotate (-a) u = v := by
  classical
  obtain ⟨a,hf,h2,h3⟩ := explicit_modified_isometry D E hn hsmall hD hE
    u.toCyclicTiling v.toCyclicTiling P Q f hf
  exact ⟨a,hf,words_eq_of_rotated_start_sets hh u v a h2 h3⟩

variable [NeZero (2*h-1)] [NeZero (h*(2*h-1))]

/-- The actual, unlabelled anchored switched family determines both its
layout word and its set of switches. No arbitrary labelling of rows is used. -/
theorem anchored_family_recovers_layout_and_switches (hh : 33 ≤ h)
    (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (u v : Layout h)
    (T U : Finset (ZMod (h*(2*h-1)) × ZMod (h*(2*h-1))))
    (hT : T ∈ (explicitSwitchLayer hh).edges.toFinset.powerset)
    (hU : U ∈ (explicitSwitchLayer hh).edges.toFinset.powerset)
    (heq : switchedFamily (explicitSwitchLayer hh)
        (u.toCyclicTiling.family (completedOfSpecifiedPrefix D (by omega) hD.1)) T =
      switchedFamily (explicitSwitchLayer hh)
        (v.toCyclicTiling.family (completedOfSpecifiedPrefix D (by omega) hD.1)) U) :
    u = v ∧ T = U := by
  classical
  have hs : (5*switchMultiplicity (2*h-1)+8)^2 ≤ 2*h-1 := by
    change (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1
    exact Prefix.count_square_bound (by omega)
  obtain ⟨P,hP⟩ := explicit_actual_row_modification D rfl (by omega) hs hD u.toCyclicTiling T
  obtain ⟨Q,hQ⟩ := explicit_actual_row_modification D rfl (by omega) hs hD v.toCyclicTiling U
  have hw : u=v := layout_recovered_from_physical_family (by omega) rfl (by omega)
    u v _ _ P Q (hP.trans (heq.trans hQ.symm))
  subst v
  refine ⟨rfl,?_⟩
  let tiles := u.toCyclicTiling
  let base := tiles.family (completedOfSpecifiedPrefix D (by omega) hD.1)
  have hdis : ∀ R ∈ base, ∀ S ∈ base, R ≠ S → Disjoint R S := by
    intro R hR S hS hne
    exact tiles.disjoint _ rfl (by omega) R S hR hS hne
  have hm := concrete_gapN_markers (m:=switchMultiplicity (2*h-1)) tiles
    (completedOfSpecifiedPrefix D (by omega) hD.1) rfl (by omega) hs
  have ho := concrete_switch_owners (m:=switchMultiplicity (2*h-1)) D rfl (by omega) hD.1 tiles hs
  exact switchedFamily_injective_on_choices (explicitSwitchLayer hh) base gapNMarker hdis hm ho
    hT hU heq

abbrev SwitchChoice (hh : 33 ≤ h) := ↥((explicitSwitchLayer hh).edges.toFinset.powerset)

/-- The family indexed by a cyclic word and its actual physical switch set. -/
def anchoredFamily (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (x : Layout h × SwitchChoice hh) : Finset (Finset (ZMod (h*(2*h-1)))) :=
  switchedFamily (explicitSwitchLayer hh)
    (x.1.toCyclicTiling.family (completedOfSpecifiedPrefix D (by omega) hD.1)) x.2.1

theorem anchoredFamily_injective (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    Function.Injective (anchoredFamily hh D hD) := by
  intro ⟨u,T⟩ ⟨v,U⟩ heq
  have hs := anchored_family_recovers_layout_and_switches hh D hD u v T.1 U.1 T.2 U.2 heq
  exact Prod.ext hs.1 (Subtype.ext hs.2)

/-- Every member counted below is an actual optimal corral family with
the complete paper gap palette. -/
theorem anchoredFamily_valid (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (x : Layout h × SwitchChoice hh) :
    anchoredFamily hh D hD x ∈ validOptimalFamilies h (2*h-1) := by
  classical
  have hs : (5*switchMultiplicity (2*h-1)+8)^2 ≤ 2*h-1 := by
    change (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1
    exact Prefix.count_square_bound (by omega)
  let tiles := x.1.toCyclicTiling
  let base := tiles.family (completedOfSpecifiedPrefix D (by omega) hD.1)
  have hdis : ∀ R ∈ base, ∀ S ∈ base, R ≠ S → Disjoint R S := by
    intro R hR S hS hne
    exact tiles.disjoint _ rfl (by omega) R S hR hS hne
  obtain ⟨P,hP⟩ := explicit_actual_row_modification D rfl (by omega) hs hD tiles x.2.1
  have hw : width (2*h-1) = h*(2*h-1) :=
    LatinTransfer.optimal_width (NeZero.pos h) rfl
  apply (mem_validOptimalFamilies_iff_local (by omega) hw (anchoredFamily hh D hD x)).mpr
  refine ⟨?_,?_,?_⟩
  · change (imageFamily base (selectedMotion (explicitSwitchLayer hh) x.2.1)).card = h
    rw [imageFamily_card]
    exact tiles.card _ rfl (by omega)
  · exact imageFamily_disjoint base (selectedMotion (explicitSwitchLayer hh) x.2.1) hdis
  · intro R hR
    change R ∈ switchedFamily (switchLayer hs)
      (tiles.family (completedOfSpecifiedPrefix D (by omega) hD.1)) x.2.1 at hR
    rw [← hP] at hR
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hR
    exact P.palette r

/-- Exact number of distinct anchored physical families, before quotienting
by physical isometries. This is the `C_h 2^(hm)` step in A.3. -/
theorem anchoredFamily_card (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    (Finset.univ.image (anchoredFamily hh D hD)).card =
      C h * 2^(h*switchMultiplicity (2*h-1)) := by
  classical
  rw [Finset.card_image_of_injective _ (anchoredFamily_injective hh D hD),
    Finset.card_univ, Fintype.card_prod, Fintype.card_coe, Finset.card_powerset,
    List.toFinset_card_of_nodup (explicitSwitchLayer hh).nodup, explicitSwitchLayer_length]
  rw [C, Nat.card_eq_fintype_card]

end
end CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge
