import CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge
import CorralFormalization.Results.SwitchFamily.LayoutCountAsymptotic

/-!
# From an exact physical classifier to physical orbit counts

The abstract finite quotient and its physical image have the same cardinality
once equality of their physical orbits is proved to be exactly the given
phase-action equivalence. The geometric equivariance and bit-coding proofs
are separate inputs to this general transfer, not assumptions of a completed
physical A.3 theorem.
-/

namespace CorralFormalization.Results.SwitchFamily.OrbitCorrespondence

noncomputable section

variable {G α β : Type*} [AddGroup G] [AddAction G α] [Fintype α]

/-- A function that distinguishes exactly the phase orbits yields a genuine
bijection from the action quotient to its actual finite image. -/
def quotientEquivImage [DecidableEq β] (f : α → β)
    (hclass : ∀ x y, f x = f y ↔ (AddAction.orbitRel G α) x y) :
    Quotient (AddAction.orbitRel G α) ≃ ↥(Finset.univ.image f) := by
  classical
  let k : α → ↥(Finset.univ.image f) := fun x =>
    ⟨f x, Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩⟩
  have hk : ∀ x y, (AddAction.orbitRel G α) x y → k x = k y := by
    intro x y hxy
    apply Subtype.ext
    exact (hclass x y).mpr hxy
  let q : Quotient (AddAction.orbitRel G α) → ↥(Finset.univ.image f) :=
    Quotient.lift k hk
  have hinj : Function.Injective q := by
    intro a b hab
    induction a using Quotient.inductionOn with
    | _ x =>
      induction b using Quotient.inductionOn with
      | _ y =>
        apply Quotient.sound
        exact (hclass x y).mp (congrArg Subtype.val hab)
  have hsurj : Function.Surjective q := by
    rintro ⟨y,hy⟩
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hy
    refine ⟨Quotient.mk _ x,?_⟩
    apply Subtype.ext
    exact hx
  exact Equiv.ofBijective q ⟨hinj,hsurj⟩

theorem image_card_eq_orbit_quotient [DecidableEq β] (f : α → β)
    (hclass : ∀ x y, f x = f y ↔ (AddAction.orbitRel G α) x y) :
    (Finset.univ.image f).card = Nat.card (Quotient (AddAction.orbitRel G α)) := by
  classical
  letI := Fintype.ofFinite (Quotient (AddAction.orbitRel G α))
  have hc := Fintype.card_congr (quotientEquivImage f hclass)
  simpa [Nat.card_eq_fintype_card, Fintype.card_coe] using hc.symm

open CorralFormalization.PhysicalCorral CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceLift CorralLatinTailMarker

section Physical

variable {h n : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable {X : Type*} [AddAction (ZMod h) X] [Fintype X]

/-- Equivariance, injectivity and the physical marker restriction together
identify the *actual* physical orbit relation with the phase-action relation. -/
theorem physical_orbit_classifier (F : X → PhysicalFamily h n)
    (hinj : Function.Injective F)
    (hrot : ∀ x y (f : Motion (h*n)), f.onFamily (F x) = F y →
      ∃ a : ZMod h, f = .rotation (zeroSite h n a))
    (hequiv : ∀ (a : ZMod h) x, F (a +ᵥ x) =
      (Motion.rotation (zeroSite h n a)).onFamily (F x)) :
    ∀ x y, physicalOrbit (F x) = physicalOrbit (F y) ↔
      (AddAction.orbitRel (ZMod h) X) x y := by
  intro x y
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · intro heq
    obtain ⟨f,hf⟩ := (physicalOrbit_eq_iff (F y) (F x)).mp heq.symm
    obtain ⟨a,rfl⟩ := hrot y x f hf
    exact ⟨a,hinj ((hequiv a y).trans hf)⟩
  · rintro ⟨a,ha⟩
    apply Eq.symm
    apply (physicalOrbit_eq_iff (F y) (F x)).mpr
    exact ⟨.rotation (zeroSite h n a), (hequiv a y).symm.trans (congrArg F ha)⟩

/-- Under the same checked geometric conditions, physical asymmetry is
exactly trivial stabilizer for the parameter action. -/
theorem physical_asymmetry_iff_trivial_stabilizer (F : X → PhysicalFamily h n)
    (hinj : Function.Injective F)
    (hrot : ∀ x y (f : Motion (h*n)), f.onFamily (F x) = F y →
      ∃ a : ZMod h, f = .rotation (zeroSite h n a))
    (hequiv : ∀ (a : ZMod h) x, F (a +ᵥ x) =
      (Motion.rotation (zeroSite h n a)).onFamily (F x)) (x : X) :
    PhysicallyAsymmetric (F x) ↔ ∀ a : ZMod h, a +ᵥ x = x → a = 0 := by
  constructor
  · intro hasym a ha
    have hfix : (Motion.rotation (zeroSite h n a)).onFamily (F x) = F x := by
      rw [← hequiv, ha]
    have hz : zeroSite h n a = 0 := Motion.rotation.inj (hasym _ hfix)
    apply zeroSite_injective (NeZero.pos n)
    simpa [zeroSite] using hz
  · intro hstab f hf
    obtain ⟨a,rfl⟩ := hrot x x f hf
    have ha : a +ᵥ x = x := hinj ((hequiv a x).trans hf)
    have ha0 := hstab a ha
    simp [ha0,zeroSite]

/-- Version for local words: precomposition by `+a` shifts the physical
family by the phase `-a`. -/
theorem physical_orbit_classifier_negative (F : X → PhysicalFamily h n)
    (hinj : Function.Injective F)
    (hrot : ∀ x y (f : Motion (h*n)), f.onFamily (F x) = F y →
      ∃ a : ZMod h, f = .rotation (zeroSite h n a))
    (hequiv : ∀ (a : ZMod h) x, F (a +ᵥ x) =
      (Motion.rotation (zeroSite h n (-a))).onFamily (F x)) :
    ∀ x y, physicalOrbit (F x) = physicalOrbit (F y) ↔
      (AddAction.orbitRel (ZMod h) X) x y := by
  intro x y
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
  constructor
  · intro heq
    obtain ⟨f,hf⟩ := (physicalOrbit_eq_iff (F y) (F x)).mp heq.symm
    obtain ⟨a,rfl⟩ := hrot y x f hf
    refine ⟨-a,hinj ?_⟩
    have hn : F ((-a) +ᵥ y) = (Motion.rotation (zeroSite h n a)).onFamily (F y) := by
      simpa using hequiv (-a) y
    exact hn.trans hf
  · rintro ⟨a,ha⟩
    apply Eq.symm
    apply (physicalOrbit_eq_iff (F y) (F x)).mpr
    exact ⟨.rotation (zeroSite h n (-a)), (hequiv a y).symm.trans (congrArg F ha)⟩

theorem physical_asymmetry_iff_trivial_stabilizer_negative (F : X → PhysicalFamily h n)
    (hinj : Function.Injective F)
    (hrot : ∀ x y (f : Motion (h*n)), f.onFamily (F x) = F y →
      ∃ a : ZMod h, f = .rotation (zeroSite h n a))
    (hequiv : ∀ (a : ZMod h) x, F (a +ᵥ x) =
      (Motion.rotation (zeroSite h n (-a))).onFamily (F x)) (x : X) :
    PhysicallyAsymmetric (F x) ↔ ∀ a : ZMod h, a +ᵥ x = x → a = 0 := by
  constructor
  · intro hasym a ha
    have hfix : (Motion.rotation (zeroSite h n (-a))).onFamily (F x) = F x := by
      rw [← hequiv, ha]
    have hz : zeroSite h n (-a) = 0 := Motion.rotation.inj (hasym _ hfix)
    have ha' : -a = 0 := by
      apply zeroSite_injective (NeZero.pos n)
      simpa [zeroSite] using hz
    simpa using ha'
  · intro hstab f hf
    obtain ⟨a,rfl⟩ := hrot x x f hf
    have hn : F ((-a) +ᵥ x) = (Motion.rotation (zeroSite h n a)).onFamily (F x) := by
      simpa using hequiv (-a) x
    have ha : (-a) +ᵥ x = x := hinj (hn.trans hf)
    have ha0 : a = 0 := by simpa using hstab (-a) ha
    simp [ha0,zeroSite]

end Physical

open Counting
open LayoutPhysicalBridge
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.GeneralTiles
open CorralFormalization.Results.SwitchFamily.Physical

/-- The actual anchored switch construction supplies the geometric
restriction required by the general orbit classifier. -/
theorem anchored_motion_is_phase {h : ℕ} [NeZero h] [NeZero (2*h-1)]
    [NeZero (h*(2*h-1))] (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (x y : Layout h × SwitchChoice hh) (f : Motion (h*(2*h-1)))
    (hf : f.onFamily (anchoredFamily hh D hD x) = anchoredFamily hh D hD y) :
    ∃ a : ZMod h, f = .rotation (zeroSite h (2*h-1) a) := by
  classical
  have hs : (5*switchMultiplicity (2*h-1)+8)^2 ≤ 2*h-1 := by
    change (5*Prefix.count (2*h-1)+8)^2 ≤ 2*h-1
    exact Prefix.count_square_bound (by omega)
  obtain ⟨P,hP⟩ := explicit_actual_row_modification D rfl (by omega) hs hD x.1.toCyclicTiling x.2.1
  obtain ⟨Q,hQ⟩ := explicit_actual_row_modification D rfl (by omega) hs hD y.1.toCyclicTiling y.2.1
  have hf' : f.onFamily P.family = Q.family := by
    rw [hP,hQ]
    exact hf
  obtain ⟨a,ha,_⟩ := isometry_forces_layout_rotation (by omega) rfl (by omega)
    x.1 y.1 D D hD.1 hD.1 P Q f hf'
  exact ⟨a,ha⟩

theorem full_period_iff_trivial_stabilizer {α : Type*} {R : α → α → Prop}
    {h : ℕ} [NeZero h] (u : LocalWord α R h) :
    u.period = h ↔ ∀ a : ZMod h, a +ᵥ u = u → a = 0 := by
  constructor
  · intro hp a ha
    have hfix : a +ᵥ (⟨u,hp⟩ : LocalWord.Primitive α R h) = ⟨u,hp⟩ := Subtype.ext ha
    exact (LocalWord.primitive_fixed_iff ⟨u,hp⟩ a).mp hfix
  · intro htriv
    have hfix : (u.period : ZMod h) +ᵥ u = u :=
      (LocalWord.fixed_iff_period_dvd u u.period).mpr (dvd_refl _)
    have hzero : (u.period : ZMod h) = 0 := htriv _ hfix
    exact Nat.dvd_antisymm u.period_dvd ((ZMod.natCast_eq_zero_iff u.period h).mp hzero)

section Decorated

variable {h n Q : ℕ} [NeZero h] [NeZero n] [NeZero (h*n)]
variable (F : DecoratedLayout h Q → PhysicalFamily h n)
variable (hinj : Function.Injective F)
variable (hrot : ∀ x y (f : Motion (h*n)), f.onFamily (F x) = F y →
  ∃ a : ZMod h, f = .rotation (zeroSite h n a))
variable (hequiv : ∀ (a : ZMod h) x, F (a +ᵥ x) =
  (Motion.rotation (zeroSite h n (-a))).onFamily (F x))

def asymmetricWordImage : Finset (Finset (PhysicalFamily h n)) := by
  classical
  exact (Finset.univ.filter (fun x => PhysicallyAsymmetric (F x))).image
    (fun x => physicalOrbit (F x))

theorem asymmetric_word_image_le_census (hh : 2 ≤ h) (hn : n = 2*h-1)
    (hvalid : ∀ x, F x ∈ validOptimalFamilies h n) :
    (asymmetricWordImage F).card ≤ A_h h hh := by
  classical
  rw [A_h_eq hh hn]
  apply Finset.card_le_card
  intro O hO
  change O ∈ ((Finset.univ.filter (fun x => PhysicallyAsymmetric (F x))).image
    (fun x => physicalOrbit (F x))) at hO
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hO
  have hasym := (Finset.mem_filter.mp hx).2
  change physicalOrbit (F x) ∈ ((validOptimalFamilies h n).filter PhysicallyAsymmetric).image physicalOrbit
  exact Finset.mem_image.mpr ⟨F x,Finset.mem_filter.mpr ⟨hvalid x,hasym⟩,rfl⟩

include hinj hrot hequiv

/-- Once the explicit word model has been connected to the actual physical
family, the full physical-orbit count is the proved Burnside count. -/
theorem physical_orbits_card_of_word_model :
    (Finset.univ.image (fun x => physicalOrbit (F x))).card = cyclicOrbitCount h Q := by
  classical
  simpa [cyclicOrbitCount] using
    image_card_eq_orbit_quotient (G:=ZMod h) (fun x => physicalOrbit (F x))
      (physical_orbit_classifier_negative F hinj hrot hequiv)

theorem physical_asymmetry_iff_full_period (x : DecoratedLayout h Q) :
    PhysicallyAsymmetric (F x) ↔ x.period = h := by
  rw [physical_asymmetry_iff_trivial_stabilizer_negative F hinj hrot hequiv,
    ← full_period_iff_trivial_stabilizer]

/-- The physical asymmetric orbit image agrees with the proved primitive
word quotient, provided the stated actual embedding facts have been shown. -/
theorem physical_asymmetric_orbits_card_of_word_model :
    (asymmetricWordImage F).card = aperiodicOrbitCount h Q := by
  classical
  change ((Finset.univ.filter (fun x => PhysicallyAsymmetric (F x))).image
    (fun x => physicalOrbit (F x))).card = aperiodicOrbitCount h Q
  let P := LocalWord.Primitive (Fin 3 × Fin Q) (fun a b => tileEdge a.1 b.1) h
  have hclass : ∀ (x y : P), physicalOrbit (F x.1) = physicalOrbit (F y.1) ↔
      (AddAction.orbitRel (ZMod h) P) x y := by
    intro x y
    have hb := physical_orbit_classifier_negative F hinj hrot hequiv x.1 y.1
    rw [AddAction.orbitRel_apply,AddAction.mem_orbit_iff] at hb ⊢
    constructor
    · intro hxy
      obtain ⟨a,ha⟩ := hb.mp hxy
      exact ⟨a,Subtype.ext ha⟩
    · rintro ⟨a,ha⟩
      apply hb.mpr
      exact ⟨a,congrArg Subtype.val ha⟩
  have hc := image_card_eq_orbit_quotient (G:=ZMod h)
    (fun x : P => physicalOrbit (F x.1)) hclass
  have hi : (Finset.univ.image (fun x : P => physicalOrbit (F x.1))) =
      ((Finset.univ.filter (fun x => PhysicallyAsymmetric (F x))).image
        (fun x => physicalOrbit (F x))) := by
    ext o
    simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨⟨x,hx⟩,he⟩
      exact ⟨x,(physical_asymmetry_iff_full_period F hinj hrot hequiv x).mpr hx,he⟩
    · rintro ⟨x,hx,he⟩
      exact ⟨⟨x,(physical_asymmetry_iff_full_period F hinj hrot hequiv x).mp hx⟩,he⟩
  rw [← hi]
  exact hc

end Decorated

end
end CorralFormalization.Results.SwitchFamily.OrbitCorrespondence
