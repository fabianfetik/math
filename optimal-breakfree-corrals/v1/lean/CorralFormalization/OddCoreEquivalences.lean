import CorralFormalization.Core
import CorralFormalization.FiberPhysical

namespace CorralFormalization

@[simp]
theorem prefixPhysicalEquiv_apply {K h : ℕ} [NeZero h]
    (r : Fin K → Fin K) (q : Fin K → Fin h)
    (hr : Function.Bijective r) (i : Fin K) (s : Fin h) :
    (prefixPhysicalEquiv r q hr (i, s)).val = (r i).val + K * (q i + s).val := by
  simp [prefixPhysicalEquiv, prefixOrbitFinMap]

/-- The odd-core prefix transversal, together with arbitrary quotient
offsets, bijects the entire odd-core site set. Here `K=4A+3` and the odd-core
height is `h=2A+3`. The quotient offsets are intentionally left abstract:
this theorem handles the fiber-fill step independently of endpoint profiles. -/
noncomputable def oddCorePhysicalEquiv (A : ℕ) (hA : 2 ≤ A)
    (q : Fin (4 * A + 3) → Fin (2 * A + 3)) :
    (Fin (4 * A + 3) × Fin (2 * A + 3)) ≃
      Fin ((2 * A + 3) * (4 * A + 3)) := by
  letI : NeZero (2 * A + 3) := ⟨by omega⟩
  exact prefixPhysicalEquiv (oddCoreTranslatedPrefixResidue A hA) q
    (oddCoreTranslatedPrefixResidue_bijective A hA)

theorem oddCorePhysicalEquiv_bijective (A : ℕ) (hA : 2 ≤ A)
    (q : Fin (4 * A + 3) → Fin (2 * A + 3)) :
    Function.Bijective (oddCorePhysicalEquiv A hA q) :=
  (oddCorePhysicalEquiv A hA q).bijective

/-- The odd-core quotient and translated remainder columns transcribed from the
normalized prefix profile. The resulting coordinate map is a genuine
bijection. This module does not prove that these columns are the quotients and
remainders of the concrete gap-word prefix sums. -/
noncomputable def oddCoreCoordinateEquiv (A : ℕ) (hA : 2 ≤ A) :
    (Fin (4 * A + 3) × Fin (2 * A + 3)) ≃
      Fin ((2 * A + 3) * (4 * A + 3)) := by
  letI : NeZero (2 * A + 3) := ⟨by omega⟩
  exact prefixPhysicalEquiv (oddCoreTranslatedPrefixResidue A hA) (oddCorePrefixQuotient A hA)
    (oddCoreTranslatedPrefixResidue_bijective A hA)

theorem oddCoreCoordinateEquiv_bijective (A : ℕ) (hA : 2 ≤ A) :
    Function.Bijective (oddCoreCoordinateEquiv A hA) :=
  (oddCoreCoordinateEquiv A hA).bijective

@[simp]
theorem oddCoreCoordinateEquiv_apply (A : ℕ) (hA : 2 ≤ A)
    (i : Fin (4 * A + 3)) (s : Fin (2 * A + 3)) :
    (oddCoreCoordinateEquiv A hA (i, s)).val =
      (oddCoreTranslatedPrefixResidue A hA i).val + (4 * A + 3) *
        (oddCorePrefixQuotient A hA i + s).val := by
  letI : NeZero (2 * A + 3) := ⟨by omega⟩
  simpa [oddCoreCoordinateEquiv] using
    (prefixPhysicalEquiv_apply (oddCoreTranslatedPrefixResidue A hA)
      (oddCorePrefixQuotient A hA) (oddCoreTranslatedPrefixResidue_bijective A hA) i s)

end CorralFormalization
