import CorralFormalization.EndpointProof.Router.Collisions
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Data.Finset.Card

/-! # Actual affine fibre counts for the router

All counting is over an arbitrary finite additive commutative group of odd
order.  The ±2 cases are justified from coprimality with the group order.
-/
namespace EndpointRouter
namespace Affine

open Switch
universe u
variable {G : Type u} [AddCommGroup G]

abbrev Parameters (G : Type u) := G × G × G

def value (constant : G) (coefficient : Fin 3 → ℤ) (t : Parameters G) : G :=
  constant + coefficient 0 • t.1 + coefficient 1 • t.2.1 + coefficient 2 • t.2.2

variable [Fintype G]

theorem double_injective (hodd : Odd (Fintype.card G)) :
    Function.Injective (fun x : G => x+x) := by
  have hc : (Nat.card G).Coprime 2 := by
    rw [Nat.card_eq_fintype_card]
    exact hodd.coprime_two_right
  simpa only [two_nsmul] using hc.nsmul_right_bijective.injective

theorem smallCoefficient_injective (hodd : Odd (Fintype.card G)) (a : ℤ)
    (ha : SmallCoefficient a) : Function.Injective (fun x : G => a • x) := by
  rcases ha with rfl | rfl | rfl | rfl
  · intro x y h; simpa using h
  · intro x y h; exact neg_injective (by simpa using h)
  · simpa only [two_zsmul] using double_injective hodd
  · intro x y h
    apply double_injective hodd
    apply neg_injective
    simpa only [neg_zsmul,two_zsmul] using h

/-- Forget the coordinate whose coefficient is invertible. -/
def freeProjection (k : Fin 3) (t : Parameters G) : G × G :=
  if k = 0 then (t.2.1,t.2.2) else if k = 1 then (t.1,t.2.2) else (t.1,t.2.1)

variable [DecidableEq G]

theorem fiber_projection_injOn (hodd : Odd (Fintype.card G))
    (constant : G) (coefficient : Fin 3 → ℤ) (k : Fin 3)
    (hk : SmallCoefficient (coefficient k)) (z : G) :
    Set.InjOn (freeProjection k)
      (↑((Finset.univ : Finset (Parameters G)).filter
        (fun t => value constant coefficient t = z)) : Set (Parameters G)) := by
  rintro ⟨a,b,c⟩ ht ⟨x,y,w⟩ hu he
  have ht' := (Finset.mem_filter.mp ht).2
  have hu' := (Finset.mem_filter.mp hu).2
  have hs := ht'.trans hu'.symm
  have hinj := smallCoefficient_injective hodd (coefficient k) hk
  fin_cases k
  · simp [freeProjection] at he
    rcases he with ⟨rfl,rfl⟩
    have hax : a = x := hinj (add_left_cancel (add_right_cancel (add_right_cancel hs)))
    simp [hax]
  · simp [freeProjection] at he
    rcases he with ⟨rfl,rfl⟩
    have hby : b = y := hinj (add_left_cancel (add_right_cancel hs))
    simp [hby]
  · simp [freeProjection] at he
    rcases he with ⟨rfl,rfl⟩
    have hcw : c = w := hinj (add_left_cancel hs)
    simp [hcw]

/-- A genuine n² fibre bound, not an assumed affine-counting interface. -/
theorem fiber_card_le (hodd : Odd (Fintype.card G))
    (constant : G) (coefficient : Fin 3 → ℤ) (k : Fin 3)
    (hk : SmallCoefficient (coefficient k)) (z : G) :
    ((Finset.univ : Finset (Parameters G)).filter
      (fun t => value constant coefficient t = z)).card ≤ (Fintype.card G)^2 := by
  have hc := Finset.card_le_card_of_injOn
    (s := (Finset.univ : Finset (Parameters G)).filter
      (fun t => value constant coefficient t = z))
    (t := (Finset.univ : Finset (G × G))) (freeProjection k)
    (by intro t ht; simp) (fiber_projection_injOn hodd constant coefficient k hk z)
  simpa only [Finset.card_univ,Fintype.card_prod,pow_two] using hc

omit [Fintype G] [DecidableEq G] in
theorem value_sub (a b : G) (p q : Fin 3 → ℤ) (t : Parameters G) :
    value a p t - value b q t = value (a-b) (fun k => p k-q k) t := by
  simp only [value,sub_zsmul]
  abel

/-- An affine equality has at most n² solutions if the difference of its
coefficient vectors has a small nonzero pivot. -/
theorem equation_card_le (hodd : Odd (Fintype.card G))
    (a b : G) (p q : Fin 3 → ℤ) (k : Fin 3)
    (hk : SmallCoefficient (p k-q k)) :
    ((Finset.univ : Finset (Parameters G)).filter
      (fun t => value a p t = value b q t)).card ≤ (Fintype.card G)^2 := by
  have heq : ((Finset.univ : Finset (Parameters G)).filter
      (fun t => value a p t = value b q t)) =
      Finset.univ.filter (fun t => value (a-b) (fun k => p k-q k) t = 0) := by
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,← value_sub,sub_eq_zero]
  rw [heq]
  exact fiber_card_le hodd _ _ k hk 0

end Affine
end EndpointRouter
