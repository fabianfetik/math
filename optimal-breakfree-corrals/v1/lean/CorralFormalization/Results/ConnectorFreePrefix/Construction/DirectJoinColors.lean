import CorralFormalization.Results.ConnectorFreePrefix.Construction.ColumnOrder

/-!
# Ordinary directed colours of all connector-free direct joins

The colours in (L11) and (L12) are integer expressions. Their bounds below
put them in `(0,n)`, so taking natural values does not change the colours.
The mixed distinctness proof uses the *ordinary* boundary equality (L5).
-/

namespace CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction

/-- The literal within-row direct join colour (L11). -/
def withinColor (n r j t : ℕ) : ℤ :=
  n - 60*(r:ℤ)*r - 2*(modulus r:ℤ)*j + ((modulus r:ℤ)+1)*delta r t

/-- The literal between-row direct join colour (L12). -/
def betweenColor (n r j : ℕ) : ℤ :=
  n - 60*(r:ℤ)*r - (modulus r:ℤ)*(2*(j:ℤ)+1) + ((modulus r:ℤ)+1)*boundary r

theorem row_product_bound {r j : ℕ} (hr : 3 ≤ r) (hj : j < r) :
    modulus r*j ≤ r*r-1 := by
  have hm := modulus_bounds r
  have hj' : j+1 ≤ r := by omega
  have hp := Nat.mul_le_mul hm.2 (show j ≤ r-1 by omega)
  have hsub : r-1+1=r := by omega
  have hpos : 0 < r*r := Nat.mul_pos (by omega) (by omega)
  have hsq : r*r-1+1=r*r := by omega
  nlinarith

theorem modulus_square_bound {r : ℕ} (hr : 3 ≤ r) :
    modulus r*modulus r-1 ≤ 2*r*r := by
  have hm := modulus_bounds r
  have hsq := Nat.mul_le_mul hm.2 hm.2
  have hpos : 0 < modulus r*modulus r := Nat.mul_pos (by omega) (by omega)
  have hsub : modulus r*modulus r-1+1=modulus r*modulus r := by omega
  nlinarith

theorem weighted_delta_bounds {r t : ℕ} (hr : 3 ≤ r) (ht : t+1 < r) :
    -(2*(r:ℤ)*r) ≤ ((modulus r:ℤ)+1)*delta r t ∧
      ((modulus r:ℤ)+1)*delta r t ≤ 2*(r:ℤ)*r := by
  have h0 := column_lt (by omega : 0 < r) t
  have h1 := column_lt (by omega : 0 < r) (t+1)
  have hsq := modulus_square_bound hr
  have hsq' : (modulus r:ℤ)*(modulus r:ℤ)-1 ≤ 2*(r:ℤ)*r := by
    have hmpos := modulus_pos (by omega : 0 < r)
    have hpos := Nat.mul_pos hmpos hmpos
    have hsub : modulus r*modulus r-1+1=modulus r*modulus r := by omega
    have hsub' : ((modulus r*modulus r-1:ℕ):ℤ)+1=(modulus r:ℤ)*(modulus r:ℤ) := by
      exact_mod_cast hsub
    have hcast : ((modulus r*modulus r-1:ℕ):ℤ) ≤ 2*(r:ℤ)*r := by exact_mod_cast hsq
    omega
  have h0' : (column r t:ℤ) < modulus r := by exact_mod_cast h0
  have h1' : (column r (t+1):ℤ) < modulus r := by exact_mod_cast h1
  have hnon0 : (0:ℤ) ≤ column r t := by omega
  have hnon1 : (0:ℤ) ≤ column r (t+1) := by omega
  have hM : (0:ℤ) ≤ modulus r := by omega
  unfold delta
  constructor <;> nlinarith

theorem weighted_boundary_bounds {r : ℕ} (hr : 3 ≤ r) :
    -(2*(r:ℤ)*r) ≤ ((modulus r:ℤ)+1)*boundary r ∧
      ((modulus r:ℤ)+1)*boundary r ≤ 2*(r:ℤ)*r := by
  obtain ⟨t, ht⟩ := boundary_internal hr
  rw [← ht]
  exact weighted_delta_bounds hr (by have := t.isLt; omega)

theorem withinColor_bounds {n r j t : ℕ} (hr : 3 ≤ r)
    (hj : j < r) (ht : t < r-1) :
    (n:ℤ)-64*(r:ℤ)*r ≤ withinColor n r j t ∧
      withinColor n r j t ≤ (n:ℤ)-58*(r:ℤ)*r := by
  have hd := weighted_delta_bounds hr (by omega : t+1<r)
  have hp := row_product_bound hr hj
  have hp' : (modulus r:ℤ)*(j:ℤ) ≤ (r:ℤ)*r-1 := by
    have hpos : 0 < r*r := Nat.mul_pos (by omega) (by omega)
    have he : r*r-1+1=r*r := by omega
    have hcast : ((modulus r*j:ℕ):ℤ) ≤ ((r*r-1:ℕ):ℤ) := by exact_mod_cast hp
    have hecast : ((r*r-1:ℕ):ℤ)+1=(r:ℤ)*r := by exact_mod_cast he
    push_cast at hcast
    omega
  have hnon : (0:ℤ) ≤ (modulus r:ℤ)*(j:ℤ) := by positivity
  unfold withinColor
  constructor <;> nlinarith

theorem betweenColor_bounds {n r j : ℕ} (hr : 3 ≤ r) (hj : j < r-1) :
    (n:ℤ)-64*(r:ℤ)*r ≤ betweenColor n r j ∧
      betweenColor n r j ≤ (n:ℤ)-58*(r:ℤ)*r := by
  have hd := weighted_boundary_bounds hr
  have hp := row_product_bound hr (by omega : j < r)
  have hq := row_product_bound hr (by omega : j+1 < r)
  have hp' : (modulus r:ℤ)*(j:ℤ) ≤ (r:ℤ)*r := by
    have := hp.trans (Nat.sub_le (r*r) 1)
    exact_mod_cast this
  have hq' : (modulus r:ℤ)*((j:ℤ)+1) ≤ (r:ℤ)*r := by
    have := hq.trans (Nat.sub_le (r*r) 1)
    exact_mod_cast this
  have hnon : (0:ℤ) ≤ (modulus r:ℤ)*(2*(j:ℤ)+1) := by positivity
  unfold betweenColor
  constructor <;> nlinarith

private theorem within_modEq (n r j t : ℕ) :
    withinColor n r j t ≡ (n:ℤ)-60*(r:ℤ)*r+delta r t [ZMOD (modulus r:ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨2*(j:ℤ)-delta r t, ?_⟩
  unfold withinColor
  ring

private theorem between_modEq (n r j : ℕ) :
    betweenColor n r j ≡ (n:ℤ)-60*(r:ℤ)*r+boundary r [ZMOD (modulus r:ℤ)] := by
  apply Int.modEq_iff_dvd.mpr
  refine ⟨2*(j:ℤ)+1-boundary r, ?_⟩
  unfold betweenColor
  ring

/-- All within-row joins have distinct actual colours, indexed by row and
internal column position. -/
theorem withinColor_injective {n r j k s t : ℕ} (hr : 3 ≤ r)
    (hs : s < r-1) (ht : t < r-1)
    (h : withinColor n r j s = withinColor n r k t) : j=k ∧ s=t := by
  have hc' := within_modEq n r j s
  rw [h] at hc'
  have hc := hc'.symm.trans (within_modEq n r k t)
  have hst := delta_residue_injective hr hs ht
    (Int.ModEq.add_left_cancel' ((n:ℤ)-60*(r:ℤ)*r) hc)
  subst t
  have hM : (0:ℤ) < modulus r := by exact_mod_cast modulus_pos (by omega : 0<r)
  unfold withinColor at h
  have hjk : (j:ℤ)=(k:ℤ) := by nlinarith
  exact ⟨by exact_mod_cast hjk, rfl⟩

/-- All between-row joins have distinct actual colours. -/
theorem betweenColor_injective {n r j k : ℕ} (hr : 3 ≤ r)
    (h : betweenColor n r j = betweenColor n r k) : j=k := by
  have hM : (0:ℤ) < modulus r := by exact_mod_cast modulus_pos (by omega : 0<r)
  unfold betweenColor at h
  have hjk : (j:ℤ)=(k:ℤ) := by nlinarith
  exact_mod_cast hjk

/-- No within-row join colour equals a between-row join colour.
Here the exact integer equality in the boundary table eliminates the
possible multiple-of-`m` ambiguity, leaving an impossible odd/even equation. -/
theorem withinColor_ne_betweenColor {n r j k t : ℕ} (hr : 3 ≤ r)
    (ht : t < r-1) : withinColor n r j t ≠ betweenColor n r k := by
  intro h
  have hc' := within_modEq n r j t
  rw [h] at hc'
  have hc := hc'.symm.trans (between_modEq n r k)
  have hti := boundary_internal_unique hr ht
    (Int.ModEq.add_left_cancel' ((n:ℤ)-60*(r:ℤ)*r) hc)
  have hordinary : delta r t = boundary r := by
    rw [hti]
    exact delta_boundaryIndex hr
  have hM : (0:ℤ) < modulus r := by exact_mod_cast modulus_pos (by omega : 0<r)
  unfold withinColor betweenColor at h
  rw [hordinary] at h
  have hparity : 2*(j:ℤ)=2*(k:ℤ)+1 := by nlinarith
  omega

/-- Every literal direct-join expression is a positive representative and
is separated from both centre-colour bands and the large marker colour. -/
theorem directColor_separation {n r : ℕ} (hr : 3 ≤ r) (hn : 200*r*r ≤ n)
    (d : ℤ) (hd : (n:ℤ)-64*(r:ℤ)*r ≤ d ∧ d ≤ (n:ℤ)-58*(r:ℤ)*r) :
    51*(r:ℤ)*r < d ∧ d < (n:ℤ)-14 ∧ 0 < d ∧ d < n := by
  have hn' : 200*(r:ℤ)*r ≤ n := by exact_mod_cast hn
  have hr' : (3:ℤ) ≤ r := by exact_mod_cast hr
  constructor
  · nlinarith
  constructor
  · nlinarith
  constructor <;> nlinarith

end CorralFormalization.LatinCompletion.TerraceCompletion.ConnectorFreePrefix.Construction
