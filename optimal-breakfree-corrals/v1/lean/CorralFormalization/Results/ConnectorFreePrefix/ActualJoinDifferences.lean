import CorralFormalization.Results.ConnectorFreePrefix.WaleckiCoordinates
import CorralFormalization.Results.ConnectorFreePrefix.Construction.DirectJoinColors

/-!
# Actual directed differences at connector-free joins

The within-row and between-row expressions are first compared as integers
with the actual successor/predecessor coordinates, and only then reduced
to the clock. This connects the distinct L11/L12 expressions to physical
directed differences, rather than introducing abstract edge colours.
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix

open CorralFormalization.LatinCompletion.ConnectorFreePhysical

variable {r n : ℕ} [NeZero r]

/-- Ordinary integer displacement from one actual `N` to another actual `P`. -/
theorem coordinates_join_displacement (D : Coordinates r)
    (hr : 3 ≤ r) (hn : 200*r*r ≤ n) (j k t u : Fin r) :
    (D.predecessor j t : ℤ) - (D.successor k u : ℤ) =
      ((D.modulus : ℤ)+1)*((D.column t).val-(D.column u).val) - D.a j - D.b k := by
  have hp := (D.local_gap_geometry hr hn j t t).2.2.1
  have hp' : (D.predecessor j t : ℤ) + (D.a j : ℤ) = D.xi t := by exact_mod_cast hp
  have ht := D.xi_normalization hr t
  have hu := D.xi_normalization hr u
  have ht' : (D.xi t : ℤ) + ((D.modulus : ℤ)+1)*(D.column ⟨0,NeZero.pos r⟩).val =
      20*(r : ℤ)*r+((D.modulus : ℤ)+1)*(D.column t).val := by exact_mod_cast ht
  have hu' : (D.xi u : ℤ) + ((D.modulus : ℤ)+1)*(D.column ⟨0,NeZero.pos r⟩).val =
      20*(r : ℤ)*r+((D.modulus : ℤ)+1)*(D.column u).val := by exact_mod_cast hu
  simp only [Coordinates.successor, Nat.cast_add]
  nlinarith

/-- The integer displacement at an internal row join equals the printed
colour (L11) minus one complete turn of the clock. -/
theorem within_join_displacement (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (j t : Fin r) (ht : t.val+1 < r) :
    let D := waleckiCoordinates r
    (D.predecessor j ⟨t.val+1,ht⟩ : ℤ) - (D.successor j t : ℤ) =
      Construction.withinColor n r j.val t.val - n := by
  have h := coordinates_join_displacement (waleckiCoordinates r) hr hn j j ⟨t.val+1,ht⟩ t
  dsimp only [Construction.withinColor, Construction.delta]
  dsimp [waleckiCoordinates, Coordinates.a, Coordinates.b] at h ⊢
  push_cast at h ⊢
  nlinarith

/-- The integer displacement at a row boundary equals the printed colour
(L12) minus one complete turn of the clock. -/
theorem between_join_displacement (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (j : Fin r) (hj : j.val+1 < r) :
    let D := waleckiCoordinates r
    (D.predecessor ⟨j.val+1,hj⟩ ⟨0,NeZero.pos r⟩ : ℤ) -
      (D.successor j ⟨r-1,by omega⟩ : ℤ) =
        Construction.betweenColor n r j.val - n := by
  have h := coordinates_join_displacement (waleckiCoordinates r) hr hn
    ⟨j.val+1,hj⟩ j ⟨0,NeZero.pos r⟩ ⟨r-1,by omega⟩
  dsimp only [Construction.betweenColor, Construction.boundary]
  dsimp [waleckiCoordinates, Coordinates.a, Coordinates.b] at h ⊢
  push_cast at h ⊢
  nlinarith

/-- A displacement equal to `d - n`, with `0 ≤ d < n`, has `d` as its
actual positive clock representative. -/
theorem clock_value_of_one_turn (a b n : ℕ) (d : ℤ)
    (hd0 : 0 ≤ d) (hdn : d < n) (h : (a : ℤ) - b = d - n) :
    ((a : ZMod n) - (b : ZMod n)).val = d.toNat := by
  have hnat : (d.toNat : ℤ) = d := Int.toNat_of_nonneg hd0
  have hlt : d.toNat < n := by omega
  have hc := congrArg (fun z : ℤ => (z : ZMod n)) h
  have hc' : (a : ZMod n) - (b : ZMod n) = (d : ZMod n) := by
    simpa using hc
  have hdcast : (d.toNat : ZMod n) = (d : ZMod n) := by
    calc
      (d.toNat : ZMod n) = ((d.toNat : ℤ) : ZMod n) := by push_cast; rfl
      _ = (d : ZMod n) := congrArg (fun z : ℤ => (z : ZMod n)) hnat
  rw [← hdcast] at hc'
  rw [hc', ZMod.val_natCast_of_lt hlt]

/-- The actual directed clock difference at every within-row join is exactly
the natural value of the pairwise-distinct expression (L11). -/
theorem within_join_actual_color (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (j t : Fin r) (ht : t.val+1 < r) :
    let D := waleckiCoordinates r
    ((D.predecessor j ⟨t.val+1,ht⟩ : ZMod n) - (D.successor j t : ZMod n)).val =
      (Construction.withinColor n r j.val t.val).toNat := by
  have hb := Construction.withinColor_bounds (n := n) hr j.isLt (by omega : t.val < r-1)
  have hs := Construction.directColor_separation hr hn _ hb
  exact clock_value_of_one_turn _ _ _ _ hs.2.2.1.le hs.2.2.2
    (within_join_displacement hr hn j t ht)

/-- The actual directed clock difference at every row boundary is exactly
the natural value of the expression (L12). -/
theorem between_join_actual_color (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (j : Fin r) (hj : j.val+1 < r) :
    let D := waleckiCoordinates r
    ((D.predecessor ⟨j.val+1,hj⟩ ⟨0,NeZero.pos r⟩ : ZMod n) -
      (D.successor j ⟨r-1,by omega⟩ : ZMod n)).val =
        (Construction.betweenColor n r j.val).toNat := by
  have hb := Construction.betweenColor_bounds (n := n) hr (by omega : j.val < r-1)
  have hs := Construction.directColor_separation hr hn _ hb
  exact clock_value_of_one_turn _ _ _ _ hs.2.2.1.le hs.2.2.2
    (between_join_displacement hr hn j hj)

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix
