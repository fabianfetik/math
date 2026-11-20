import CorralFormalization.Fiber

namespace CorralFormalization

/-- The owner-fiber map with quotient coordinates represented by `Fin h`.
Addition in `Fin h` is cyclic addition. -/
def prefixOrbitFinMap {K h : ℕ} (r : Fin K → Fin K) (q : Fin K → Fin h) :
    Fin K × Fin h → Fin K × Fin h
  | (i, s) => (r i, q i + s)

/-- A residue transversal, followed by arbitrary cyclic quotient offsets,
permutes the complete product of residue and owner coordinates. -/
theorem prefixOrbitFinMap_bijective {K h : ℕ} [NeZero h]
    (r : Fin K → Fin K) (q : Fin K → Fin h)
    (hr : Function.Bijective r) :
    Function.Bijective (prefixOrbitFinMap r q) := by
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

/-- Encode `(remainder, quotient)` as a site in the cyclic block of size
`h*K`. This is the quotient/remainder order used by `finProdFinEquiv`. -/
noncomputable def prefixPhysicalEquiv {K h : ℕ} [NeZero h]
    (r : Fin K → Fin K) (q : Fin K → Fin h)
    (hr : Function.Bijective r) : (Fin K × Fin h) ≃ Fin (h * K) :=
  (Equiv.ofBijective (prefixOrbitFinMap r q)
    (prefixOrbitFinMap_bijective r q hr)).trans
    ((Equiv.prodComm (Fin K) (Fin h)).trans finProdFinEquiv)

theorem prefixPhysicalEquiv_bijective {K h : ℕ} [NeZero h]
    (r : Fin K → Fin K) (q : Fin K → Fin h)
    (hr : Function.Bijective r) :
    Function.Bijective (prefixPhysicalEquiv r q hr) :=
  (prefixPhysicalEquiv r q hr).bijective

end CorralFormalization
