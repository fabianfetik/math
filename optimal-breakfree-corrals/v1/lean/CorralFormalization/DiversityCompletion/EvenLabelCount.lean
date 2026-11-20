import CorralFormalization.DiversityCompletion.EvenSwitches
import CorralFormalization.DiversityCompletion.PhaseReflection

/-! The exact §6 reflection count for the explicit abstract label type.
The geometry must still identify each label with a distinct physical
two-row decomposition and identify its reflection with `flipLetter`. -/

namespace CorralFormalization.EvenSwitches

open PhysicalCorral

abbrev EvenLetter (m : ℕ) := Choices m × Bool

def flipLetter {m : ℕ} (a : EvenLetter m) : EvenLetter m := (a.1, !a.2)

theorem flipLetter_involutive (m : ℕ) : Function.Involutive (@flipLetter m) := by
  intro a
  rcases a with ⟨c, b⟩
  cases b <;> rfl

theorem evenLetter_card (m : ℕ) (hm : 1 ≤ m) : Fintype.card (EvenLetter m) = 2^(2*m) := by
  classical
  simp only [EvenLetter, Fintype.card_prod, choices_card m hm, Fintype.card_bool]
  rw [← pow_succ]
  congr 1
  omega

theorem evenLabels_reflection_fixed (m : ℕ) (hm : 1 ≤ m) :
    (Finset.univ.filter (fun f : NonzeroPhase m → EvenLetter m =>
      phaseReflection m flipLetter f = f)).card = 2^(2*m*m) := by
  classical
  rw [phaseReflection_fixed_card m flipLetter (flipLetter_involutive m), evenLetter_card m hm]
  rw [← pow_mul]

theorem evenLabels_reflection_nonfixed_pairs (m : ℕ) (hm : 1 ≤ m) :
    (involutionPairs (phaseReflection m (@flipLetter m))).card =
      (2^(4*m*m) - 2^(2*m*m))/2 := by
  classical
  rw [phaseReflection_nonfixed_pairs m flipLetter (flipLetter_involutive m), evenLetter_card m hm]
  simp only [← pow_mul]
  congr 2
  congr 1
  ring

theorem evenLabels_total (m : ℕ) (hm : 1 ≤ m) :
    Fintype.card (NonzeroPhase m → EvenLetter m) = 2^(4*m*m) := by
  classical
  have hc := Fintype.card_congr (phaseEquiv m)
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool] at hc
  have hp : Fintype.card (NonzeroPhase m) = 2*m := by omega
  rw [Fintype.card_fun, evenLetter_card m hm, hp, ← pow_mul]
  congr 1
  ring

/-- The exact physical orbit formula follows once the literal family pays
the seed-marker, decoding and reflection-equivariance interfaces. -/
theorem evenLabels_physical_orbit_formula {M : ℕ} (m : ℕ) (hm : 1 ≤ m)
    (family : (NonzeroPhase m → EvenLetter m) → Finset (Finset (ZMod M)))
    (hinj : Function.Injective family) (R : Finset (ZMod M)) (C : ZMod M)
    (marker : Finset (ZMod M) → Prop) (hrigid : RigidRow R) (hmarker : marker R)
    (hinvariant : ∀ f : Motion M, ∀ S, marker (f.onRow S) ↔ marker S)
    (hseed : ∀ t, R ∈ family t)
    (honly : ∀ t S, S ∈ family t → marker S → S = R ∨ S = (Motion.reflection C).onRow R)
    (hequiv : ∀ t, (Motion.reflection C).onFamily (family t) =
      family (phaseReflection m flipLetter t)) :
    (asymmetricOrbitIntersections family).card = (2^(4*m*m) - 2^(2*m*m))/2 := by
  classical
  rw [marked_family_asymmetric_orbit_count family hinj R C marker hrigid hmarker
    hinvariant hseed honly (phaseReflection m flipLetter) hequiv,
    evenLabels_total m hm, evenLabels_reflection_fixed m hm]

end CorralFormalization.EvenSwitches
