import CorralFormalization.Results.ConnectorFreePrefix.Construction.ColumnOrder
import CorralFormalization.Results.ConnectorFreePrefix.PhysicalTransfer.Coordinates

/-!
# The translated Walecki order supplies the physical coordinate geometry

The downstream H4 geometry no longer needs a supplied injective column map:
it is instantiated with the explicit order (L4), including the odd-`r`
case whose actual modulus may be `r+1`.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

open CorralFormalization.LatinCompletion.ConnectorFreePhysical

/-- The literal normalized columns used in the connector-free construction. -/
def waleckiCoordinates (r : ℕ) [NeZero r] : Coordinates r where
  modulus := Construction.modulus r
  lower := (Construction.modulus_bounds r).1
  upper := (Construction.modulus_bounds r).2
  column t := ⟨Construction.column r t.val, Construction.column_lt (NeZero.pos r) t.val⟩
  column_injective := by
    intro a b hab
    apply Fin.ext
    exact Construction.column_injective (NeZero.pos r) a.isLt b.isLt (congrArg Fin.val hab)

@[simp] theorem waleckiCoordinates_modulus (r : ℕ) [NeZero r] :
    (waleckiCoordinates r).modulus = Construction.modulus r := rfl

@[simp] theorem waleckiCoordinates_column (r : ℕ) [NeZero r] (t : Fin r) :
    ((waleckiCoordinates r).column t).val = Construction.column r t.val := rfl

/-- For the explicit Walecki columns, H4 selects distinct actual physical
sites for every phase, column and symbol. -/
theorem walecki_h4_site_injective {r h n : ℕ} [NeZero r] [NeZero h]
    (hr : 3 ≤ r) (hn : 200*r*r ≤ n) :
    Function.Injective ((waleckiCoordinates r).site h n) :=
  (waleckiCoordinates r).site_injective hr hn

/-- The printed lifted location (L14) is the same actual site as H4 for
the explicitly constructed Walecki columns. -/
theorem walecki_lift_eq_h4 {r h n : ℕ} [NeZero r] [NeZero h]
    (q : ZMod h) (j t s : Fin r) :
    ((q.val*n+(waleckiCoordinates r).residue t s+(2+r*j.val+t.val)*n : ℕ) : ZMod (h*n)) =
      (waleckiCoordinates r).site h n (q+(waleckiCoordinates r).offset h j,t,s) :=
  (waleckiCoordinates r).lift_eq_site q j t s

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
