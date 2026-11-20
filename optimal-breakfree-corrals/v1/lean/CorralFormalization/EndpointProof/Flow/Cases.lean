import CorralFormalization.EndpointProof.Flow.Packing

/-!
Explicit sufficient block conditions for the three regular layouts, and
the three-torsion obstruction in the third layout.  The hypotheses here
are numerical root conditions, not assumed existence of a flow candidate.
-/

open scoped BigOperators

namespace EndpointFlow

set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

section

variable {G : Type*} [CommRing G] [DecidableEq G]

theorem two_block_offsetDistinct (L : Layout) (hL : L ≠ .third)
    (r : Fin 6 → G) (hn : ∀ i, r i ≠ 0)
    (h01 : r 0+r 1 ≠ 0) (h23 : r 2+r 3 ≠ 0) (h45 : r 4+r 5 ≠ 0) :
    OffsetDistinct L r := by
  have h0 := hn 0; have h1 := hn 1; have h2 := hn 2
  have h3 := hn 3; have h4 := hn 4; have h5 := hn 5
  cases L with
  | third => exact False.elim (hL rfl)
  | first | second =>
    intro i j hij hp he
    fin_cases i <;> fin_cases j
    all_goals try exact False.elim (hij rfl)
    all_goals simp [path,offset,Matrix.cons_val_succ',Matrix.cons_val_zero'] at hp he
    all_goals first
      | (apply h0; linear_combination he) | (apply h0; linear_combination -he)
      | (apply h1; linear_combination he) | (apply h1; linear_combination -he)
      | (apply h2; linear_combination he) | (apply h2; linear_combination -he)
      | (apply h3; linear_combination he) | (apply h3; linear_combination -he)
      | (apply h4; linear_combination he) | (apply h4; linear_combination -he)
      | (apply h5; linear_combination he) | (apply h5; linear_combination -he)
      | (apply h01; linear_combination he) | (apply h01; linear_combination -he)
      | (apply h23; linear_combination he) | (apply h23; linear_combination -he)
      | (apply h45; linear_combination he) | (apply h45; linear_combination -he)

theorem first_rootLegal (r : Fin 6 → G) (hn : ∀ i, r i ≠ 0)
    (h01 : r 0 ≠ r 1) (h23 : r 2 ≠ r 3) (h45 : r 4 ≠ r 5) :
    RootLegal .first r := by
  refine ⟨hn,?_⟩
  intro i j he
  fin_cases i <;> fin_cases j
  all_goals simp_all [rootVertex,rootPart]

theorem second_rootLegal (r : Fin 6 → G) (hn : ∀ i, r i ≠ 0)
    (h05 : r 0 ≠ r 5) (h12 : r 1 ≠ r 2) (h34 : r 3 ≠ r 4) :
    RootLegal .second r := by
  refine ⟨hn,?_⟩
  intro i j he
  fin_cases i <;> fin_cases j
  all_goals simp_all [rootVertex,rootPart]

def thirdRoots (a : G) : Fin 6 → G := ![a,a,a,-a,-a,-a]

theorem third_rootLegal [Fintype G] (hodd : Odd (Fintype.card G))
    (a : G) (ha : a ≠ 0) : RootLegal .third (thirdRoots a) := by
  have hn := EndpointSelector.ne_neg_of_odd hodd ha
  refine ⟨?_,?_⟩
  · intro i; fin_cases i <;> simpa [thirdRoots] using ha
  · intro i j he
    fin_cases i <;> fin_cases j
    all_goals simp_all [rootVertex,rootPart,thirdRoots]

theorem third_offsetDistinct [Fintype G] (hodd : Odd (Fintype.card G))
    (a : G) (ha : a ≠ 0) (h3a : a+a+a ≠ 0) :
    OffsetDistinct .third (thirdRoots a) := by
  have h2a : a+a ≠ 0 := by
    intro h
    apply ha
    exact EndpointSelector.doubling_injective_of_odd hodd (by simpa using h)
  intro i j hij hp he
  fin_cases i <;> fin_cases j
  all_goals try exact False.elim (hij rfl)
  all_goals simp [path,offset,thirdRoots,Matrix.cons_val_succ',Matrix.cons_val_zero'] at hp he
  all_goals first
    | (apply ha; linear_combination he) | (apply ha; linear_combination -he)
    | (apply h2a; linear_combination he) | (apply h2a; linear_combination -he)
    | (apply h3a; linear_combination he) | (apply h3a; linear_combination -he)

/-- If 3a=0, the regular third layout has an unavoidable repeated flow.
Thus the exceptional case is necessary even for odd cyclic groups. -/
theorem third_collision_of_three_torsion (a : G) (h3a : a+a+a=0) (xy : G × G) :
    flow .third (thirdRoots a) xy 0 = flow .third (thirdRoots a) xy 3 := by
  simp [flow,path,offset,thirdRoots]
  linear_combination h3a

theorem third_invalid_of_three_torsion (a : G) (h3a : a+a+a=0) (xy : G × G) :
    ¬Valid .third (thirdRoots a) xy := by
  intro hv
  exact (hv.2.1 0 3 (by decide)).1 (third_collision_of_three_torsion a h3a xy)

end

end EndpointFlow
