import CorralFormalization.EndpointProof.AbsorberInputs.CandidatePacking.Packing

/-!
# Active categorical slots of an actual affine packing

The entire signed gadget support is retained even when only some of its
orbits require categorical labels. The label prescription is fixed as a
function of the query, actual parameter tuple and orbit index, before the
sample is drawn.
-/

open MeasureTheory
open scoped Classical

namespace AbsorberInputs.AffineAvailability

open AbsorberInputs.CandidatePacking EndpointOriginalReservoir

noncomputable section

variable {Q G L : Type*} [Fintype Q] [AddCommGroup G] [Fintype G] [DecidableEq G]
variable (e r s : Q → ℕ) (D : ∀ q, Data (e q) (r q) (s q) G)
variable {M : ℕ} (P : ∀ q, Packed (D q) M)
variable (hodd : Odd (Fintype.card G))
variable (require : ∀ q, (Fin (e q) → G) → Fin (r q) → Option L)

/-- The orbits actually requesting a label; other gadget orbits still belong
    to the full numerical support. -/
def Active (q : Q) (i : Fin M) : Type _ :=
  {j : Fin (r q) // ∃ l, require q ((P q).parameter i) j = some l}

instance activeFintype (q : Q) (i : Fin M) : Fintype (Active e r s D P require q i) := by
  classical
  unfold Active
  infer_instance

/-- The sampled orbit of each active slot. Injection follows from the actual
    signed collision tests and disjointness of the constructed packing. -/
def activeEmbedding (q : Q) :
    (Σ i : Fin M, Active e r s D P require q i) ↪ OddOrbit G where
  toFun ij := (P q).sigmaOrbitEmbedding hodd ⟨ij.1, ij.2.val⟩
  inj' := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have he := ((P q).sigmaOrbitEmbedding hodd).injective h
    have hik : i = k := congrArg Sigma.fst he
    subst k
    have hjl : j.val = l.val :=
      congrArg (fun x : Σ _i : Fin M, Fin (r q) => x.2) he
    have hjl' : j = l := Subtype.ext hjl
    subst l
    rfl

def activeDemand (q : Q) (i : Fin M) (j : Active e r s D P require q i) : L :=
  Classical.choose j.property

omit [Fintype Q] [Fintype G] in
theorem activeDemand_spec (q : Q) (i : Fin M) (j : Active e r s D P require q i) :
    require q ((P q).parameter i) j.val = some (activeDemand e r s D P require q i j) :=
  Classical.choose_spec j.property

omit [Fintype Q] [Fintype G] in
theorem active_card_le (q : Q) (i : Fin M) :
    Fintype.card (Active e r s D P require q i) ≤ r q := by
  calc
    _ ≤ Fintype.card (Fin (r q)) := Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = r q := Fintype.card_fin _

omit [Fintype Q] in
/-- A sampled word agrees with the active slot demands exactly when every
actual prescribed orbit label is met. Orbits with `none` impose no label. -/
theorem active_word_iff_requirements (q : Q) (i : Fin M) (ω : OddOrbit G → L) :
    (fun j : Active e r s D P require q i =>
      ω (activeEmbedding e r s D P hodd require q ⟨i,j⟩)) =
        activeDemand e r s D P require q i ↔
    ∀ j l, require q ((P q).parameter i) j = some l →
      ω ((P q).orbitEmbedding hodd (i,j)) = l := by
  constructor
  · intro hs j l hj
    let a : Active e r s D P require q i := ⟨j, l, hj⟩
    have hword := congrFun hs a
    have hdemand : activeDemand e r s D P require q i a = l := by
      apply Option.some.inj
      exact (activeDemand_spec e r s D P require q i a).symm.trans hj
    change ω ((P q).orbitEmbedding hodd (i,j)) =
      activeDemand e r s D P require q i a at hword
    exact hword.trans hdemand
  · intro hs
    funext a
    have hword := hs a.val (activeDemand e r s D P require q i a)
      (activeDemand_spec e r s D P require q i a)
    exact hword

def fullSupport (q : Q) (i : Fin M) : Finset G :=
  (D q).support ((P q).parameter i)

omit [Fintype Q] [Fintype G] in
theorem fullSupport_disjoint (q : Q) :
    Pairwise fun i j => Disjoint (fullSupport e r s D P q i) (fullSupport e r s D P q j) :=
  (P q).disjoint

end
end AbsorberInputs.AffineAvailability
