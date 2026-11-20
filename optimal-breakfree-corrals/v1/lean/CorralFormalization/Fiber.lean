import Mathlib

namespace CorralFormalization

/-- Quotient/remainder form of the translated-prefix construction. The seed
index selects a residue fiber, while the owner variable translates inside
that fiber. `q i` records the seed's quotient coordinate. -/
def prefixOrbitMap {K h : ℕ} (r : Fin K → Fin K) (q : Fin K → ZMod h) :
    Fin K × ZMod h → Fin K × ZMod h
  | (i, s) => (r i, q i + s)

/-- If the seed prefixes hit each residue once, then adding every owner
translation fills the complete product of residue and quotient coordinates.
The quotient offsets `q` may be arbitrary; they do not affect coverage. -/
theorem prefixOrbitMap_bijective {K h : ℕ}
    (r : Fin K → Fin K) (q : Fin K → ZMod h)
    (hr : Function.Bijective r) :
    Function.Bijective (prefixOrbitMap r q) := by
  constructor
  · intro a b hab
    rcases a with ⟨i, s⟩
    rcases b with ⟨j, t⟩
    change (r i, q i + s) = (r j, q j + t) at hab
    have hij : i = j := hr.1 (congrArg Prod.fst hab)
    subst j
    have hst : q i + s = q i + t := congrArg Prod.snd hab
    exact congrArg (fun x => (i, x)) (add_left_cancel hst)
  · intro y
    rcases y with ⟨r0, q0⟩
    obtain ⟨i, hi⟩ := hr.2 r0
    refine ⟨(i, q0 - q i), ?_⟩
    change (r i, q i + (q0 - q i)) = (r0, q0)
    rw [hi]
    apply Prod.ext
    · rfl
    · abel

end CorralFormalization
