import CorralFormalization.Results.SwitchFamily.LayoutPhysicalEquivariance
import CorralFormalization.Results.SwitchFamily.OrbitCorrespondence
import CorralFormalization.Results.SwitchFamily.OrbitLogarithmic

/-!
# Physical orbit counts for the explicit Appendix A family

The concrete bit encoding, physical phase translation, marker rigidity,
actual cyclic quotients and the paper's finite counts are composed here.
No physical orbit, switch, or equivariance supplier is assumed.
-/

open CorralFormalization.PhysicalCorral CorralFormalization.PhysicalCensus
open CorralFormalization.LatinCompletion.TerraceCompletion
open CorralFormalization.LatinCompletion.TerraceLift CorralLatinTailMarker
open CorralFormalization.Results.SwitchFamily.Counting
open CorralFormalization.Results.SwitchFamily.Counting.DecoratedPhysicalCode
open CorralFormalization.Results.SwitchFamily.LayoutPhysicalBridge
open CorralFormalization.Results.SwitchFamily.LayoutPhysicalEquivariance
open CorralFormalization.Results.SwitchFamily.OrbitCorrespondence
open Filter Topology
open scoped Topology

namespace CorralFormalization.Results.SwitchFamily.DecoratedPhysicalOrbitCounts

noncomputable section

variable {h : ℕ} [NeZero h] [NeZero (2*h-1)] [NeZero (h*(2*h-1))]

/-- The actual decorated physical family admits only whole-phase motions. -/
theorem decorated_motion_is_phase (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D)
    (u v : DecoratedLayout h (2^switchMultiplicity (2*h-1))) (f : Motion (h*(2*h-1)))
    (hf : f.onFamily (anchoredDecoratedFamily hh D hD u) = anchoredDecoratedFamily hh D hD v) :
    ∃ a : ZMod h, f = .rotation (zeroSite h (2*h-1) a) :=
  anchored_motion_is_phase hh D hD (decoratedPhysicalEquiv hh u) (decoratedPhysicalEquiv hh v) f hf

/-- Exact physical equivalence and physical asymmetry for the concrete
family, with the actual marked word action and no extra supplier. -/
theorem decorated_physical_classification (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    (∀ u v, physicalOrbit (anchoredDecoratedFamily hh D hD u) =
      physicalOrbit (anchoredDecoratedFamily hh D hD v) ↔
      (AddAction.orbitRel (ZMod h) (DecoratedLayout h (2^switchMultiplicity (2*h-1)))) u v) ∧
    (∀ u, PhysicallyAsymmetric (anchoredDecoratedFamily hh D hD u) ↔ u.period = h) := by
  constructor
  · exact physical_orbit_classifier_negative (anchoredDecoratedFamily hh D hD)
      (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
      (anchoredDecoratedFamily_rotation hh D hD)
  · exact physical_asymmetry_iff_full_period (anchoredDecoratedFamily hh D hD)
      (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
      (anchoredDecoratedFamily_rotation hh D hD)

/-- Both numerical quotient functions used in the asymptotic proof are
exactly the corresponding physical orbit counts of this concrete family. -/
theorem physical_count_identification (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    (Finset.univ.image (fun u => physicalOrbit (anchoredDecoratedFamily hh D hD u))).card =
      cyclicOrbitCount h (2^switchMultiplicity (2*h-1)) ∧
    (asymmetricWordImage (anchoredDecoratedFamily hh D hD)).card =
      aperiodicOrbitCount h (2^switchMultiplicity (2*h-1)) := by
  exact ⟨physical_orbits_card_of_word_model (anchoredDecoratedFamily hh D hD)
      (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
      (anchoredDecoratedFamily_rotation hh D hD),
    physical_asymmetric_orbits_card_of_word_model (anchoredDecoratedFamily hh D hD)
      (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
      (anchoredDecoratedFamily_rotation hh D hD)⟩
/-- Exactly the actual physical equivalence classes of the constructed
family, including the asymmetric subfamily, with the printed A9/A10 sums. -/
theorem exact_physical_family_counts (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    (Finset.univ.image (fun u => physicalOrbit (anchoredDecoratedFamily hh D hD u))).card =
      (∑ d ∈ h.divisors, Nat.totient d * C (h/d) *
        (2^switchMultiplicity (2*h-1))^(h/d)) / h ∧
    (((asymmetricWordImage (anchoredDecoratedFamily hh D hD)).card : ℕ) : ℚ) =
      (∑ d ∈ h.divisors, (ArithmeticFunction.moebius d : ℚ) *
        (C (h/d) : ℚ) * ((2^switchMultiplicity (2*h-1) : ℕ) : ℚ)^(h/d)) / (h : ℚ) := by
  constructor
  · rw [physical_orbits_card_of_word_model (anchoredDecoratedFamily hh D hD)
      (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
      (anchoredDecoratedFamily_rotation hh D hD)]
    exact burnside_totient h _
  · rw [physical_asymmetric_orbits_card_of_word_model (anchoredDecoratedFamily hh D hD)
      (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
      (anchoredDecoratedFamily_rotation hh D hD)]
    exact aperiodic_moebius h _

/-- The counted asymmetric physical classes inject into the full census. -/
theorem aperiodic_count_le_total_census (hh : 33 ≤ h) (D : DirectedTerrace (2*h-1))
    (hD : Prefix.PrescribedTerrace (switchMultiplicity (2*h-1)) D) :
    aperiodicOrbitCount h (2^switchMultiplicity (2*h-1)) ≤ A_h h (by omega) := by
  have hc := asymmetric_word_image_le_census (anchoredDecoratedFamily hh D hD)
    (show 2 ≤ h by omega) rfl (fun u => anchoredFamily_valid hh D hD (decoratedPhysicalEquiv hh u))
  rwa [physical_asymmetric_orbits_card_of_word_model (anchoredDecoratedFamily hh D hD)
    (anchoredDecoratedFamily_injective hh D hD) (decorated_motion_is_phase hh D hD)
    (anchoredDecoratedFamily_rotation hh D hD)] at hc

end
end CorralFormalization.Results.SwitchFamily.DecoratedPhysicalOrbitCounts
