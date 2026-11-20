import CorralFormalization.EndpointProof.Router.Switch
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The 121 local router collision equations

The arrays below are symbolic integer coefficients of the three free
variables (h,d,f), together with constants depending only on the ports.
Every possible equality is either impossible from the port hypotheses,
or has a coefficient ±1 or ±2 in a free variable.  This is the precise
algebraic input to the affine fibre-counting argument; no collision or
reservoir probability estimate is asserted in this module.
-/
namespace EndpointRouter
namespace Switch

universe u
variable {G : Type u} [AddCommGroup G]

/-- A coefficient invertible on every odd-order finite abelian group. -/
def SmallCoefficient (a : ℤ) : Prop := a = 1 ∨ a = -1 ∨ a = 2 ∨ a = -2

def vertexCoefficient (i : Fin 12) (k : Fin 3) : ℤ :=
  match i.val, k.val with
  | 4,2 => -1
  | 5,0 => 1
  | 6,1 => 1
  | 7,1 => 1
  | 8,0 => 1
  | 8,1 => 1
  | 9,1 => 1
  | 9,2 => -1
  | 10,2 => 1
  | 11,2 => 1
  | _,_ => 0

def vertexConstant (S : Switch G) (i : Fin 12) : G :=
  match i.val with
  | 0 => S.x
  | 1 => S.y
  | 2 => S.v
  | 3 => S.w
  | 4 => S.w
  | 5 => 0
  | 6 => S.x
  | 7 => S.y
  | 8 => 0
  | 9 => S.v
  | 10 => S.x
  | _ => S.y

def colorCoefficient (i : Fin 10) (k : Fin 3) : ℤ :=
  match i.val, k.val with
  | 0,2 => -1
  | 1,1 => 1
  | 1,2 => 1
  | 2,0 => 1
  | 3,0 => -1
  | 3,1 => -1
  | 3,2 => 1
  | 4,2 => -1
  | 5,0 => 1
  | 6,0 => -1
  | 6,1 => 1
  | 7,2 => -1
  | 8,1 => -1
  | 8,2 => 2
  | 9,2 => -1
  | _,_ => 0

def colorConstant (S : Switch G) (i : Fin 10) : G :=
  match i.val with
  | 0 => S.w-S.x
  | 1 => S.x-S.w
  | 2 => -S.x
  | 3 => S.x
  | 4 => S.v-S.x
  | 5 => -S.y
  | 6 => S.y
  | 7 => S.v-S.y
  | 8 => S.y-S.v
  | _ => S.w-S.y

/-- Integer affine evaluation; valid over every additive commutative group. -/
def affineValue (constant : G) (coefficient : Fin 3 → ℤ) (S : Switch G) : G :=
  constant + coefficient 0 • S.h + coefficient 1 • S.d + coefficient 2 • S.f

def vertexValue (S : Switch G) (i : Fin 12) : G :=
  match i.val with
  | 0 => S.x
  | 1 => S.y
  | 2 => S.v
  | 3 => S.w
  | 4 => S.a
  | 5 => S.h
  | 6 => S.d+S.x
  | 7 => S.d+S.y
  | 8 => S.d+S.h
  | 9 => S.d+S.c
  | 10 => S.f+S.x
  | _ => S.f+S.y

def colorValue (S : Switch G) (i : Fin 10) : G :=
  match i.val with
  | 0 => S.a-S.x
  | 1 => S.d+S.x-S.a
  | 2 => S.h-S.x
  | 3 => S.f+S.x-S.d-S.h
  | 4 => S.c-S.x
  | 5 => S.h-S.y
  | 6 => S.d+S.y-S.h
  | 7 => S.c-S.y
  | 8 => S.f+S.y-S.d-S.c
  | _ => S.a-S.y

theorem vertices_ofFn (S : Switch G) : S.vertices = List.ofFn S.vertexValue := by rfl

theorem colors_ofFn (S : Switch G) : S.colors = List.ofFn S.colorValue := by rfl

theorem vertex_affine (S : Switch G) (i : Fin 12) :
    affineValue (S.vertexConstant i) (vertexCoefficient i) S = S.vertexValue i := by
  fin_cases i <;>
    simp [affineValue,vertexConstant,vertexCoefficient,vertexValue,a,c] <;> abel

theorem color_affine (S : Switch G) (i : Fin 10) :
    affineValue (S.colorConstant i) (colorCoefficient i) S = S.colorValue i := by
  fin_cases i <;>
    simp [affineValue,colorConstant,colorCoefficient,colorValue,a,c,two_zsmul] <;> abel

private theorem rectangle_nodup (S : Switch G) (h : S.LegalPorts) :
    [S.w-S.x, S.v-S.x, S.v-S.y, S.w-S.y].Nodup := by
  obtain ⟨hp,hplus,hminus⟩ := h
  have hx : S.x ≠ S.y := by
    intro he
    exact hp.notMem (by simp [he])
  have hv : S.v ≠ S.w := by
    have hvw := hp.of_cons.of_cons
    intro he
    exact hvw.notMem (by simp [he])
  have hdiag1 : S.w-S.x ≠ S.v-S.y := by
    intro he
    apply hminus
    calc
      S.v-S.w = (S.v-S.y) - (S.w-S.x) - (S.x-S.y) := by abel
      _ = -(S.x-S.y) := by rw [← he]; abel
  have hdiag2 : S.v-S.x ≠ S.w-S.y := by
    intro he
    apply hplus
    calc
      S.v-S.w = (S.v-S.x) - (S.w-S.y) + (S.x-S.y) := by abel
      _ = S.x-S.y := by rw [he]; abel
  simp [List.nodup_cons, hx, hv, Ne.symm hv, hdiag1, hdiag2]

set_option maxHeartbeats 1500000 in
/-- Every vertex-collision equation either has equal random coefficients
and unequal port constants, or has a usable random coefficient. -/
theorem vertex_collision_classification (S : Switch G) (h : S.LegalPorts)
    (i j : Fin 12) (hij : i ≠ j) :
    (vertexCoefficient i = vertexCoefficient j ∧
      S.vertexConstant i ≠ S.vertexConstant j) ∨
      ∃ k : Fin 3, SmallCoefficient (vertexCoefficient i k - vertexCoefficient j k) := by
  have hp := h.1
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | (right; refine ⟨0, ?_⟩; unfold SmallCoefficient; decide)
    | (right; refine ⟨1, ?_⟩; unfold SmallCoefficient; decide)
    | (right; refine ⟨2, ?_⟩; unfold SmallCoefficient; decide)
    | (left; refine ⟨by decide, ?_⟩; simp_all [vertexConstant, List.nodup_cons])
  all_goals grind

set_option maxHeartbeats 1500000 in
/-- The analogous exhaustive statement for all 45 colour pairs. -/
theorem color_collision_classification (S : Switch G) (h : S.LegalPorts)
    (i j : Fin 10) (hij : i ≠ j) :
    (colorCoefficient i = colorCoefficient j ∧
      S.colorConstant i ≠ S.colorConstant j) ∨
      ∃ k : Fin 3, SmallCoefficient (colorCoefficient i k - colorCoefficient j k) := by
  have hp := h.1
  have hr := rectangle_nodup S h
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hij rfl).elim
    | (right; refine ⟨0, ?_⟩; unfold SmallCoefficient; decide)
    | (right; refine ⟨1, ?_⟩; unfold SmallCoefficient; decide)
    | (right; refine ⟨2, ?_⟩; unfold SmallCoefficient; decide)
    | (left; refine ⟨by decide, ?_⟩; simp_all [colorConstant,List.nodup_cons])
  all_goals grind

/-- Equal coefficient vectors with different constants cannot collide. -/
theorem affineValue_ne_of_parallel (S : Switch G) (a b : G)
    (p q : Fin 3 → ℤ) (hpq : p = q) (hab : a ≠ b) :
    affineValue a p S ≠ affineValue b q S := by
  subst q
  intro he
  unfold affineValue at he
  exact hab (add_right_cancel (add_right_cancel (add_right_cancel he)))

/-- An actual repeated vertex has a usable coefficient in a free variable. -/
theorem vertex_collision_has_pivot (S : Switch G) (h : S.LegalPorts)
    (i j : Fin 12) (hij : i ≠ j) (he : S.vertexValue i = S.vertexValue j) :
    ∃ k : Fin 3, SmallCoefficient (vertexCoefficient i k - vertexCoefficient j k) := by
  rcases vertex_collision_classification S h i j hij with ⟨hp,hc⟩ | hp
  · apply False.elim
    apply affineValue_ne_of_parallel S _ _ _ _ hp hc
    simpa only [vertex_affine] using he
  · exact hp

/-- An actual repeated colour has a usable coefficient in a free variable. -/
theorem color_collision_has_pivot (S : Switch G) (h : S.LegalPorts)
    (i j : Fin 10) (hij : i ≠ j) (he : S.colorValue i = S.colorValue j) :
    ∃ k : Fin 3, SmallCoefficient (colorCoefficient i k - colorCoefficient j k) := by
  rcases color_collision_classification S h i j hij with ⟨hp,hc⟩ | hp
  · apply False.elim
    apply affineValue_ne_of_parallel S _ _ _ _ hp hc
    simpa only [color_affine] using he
  · exact hp

/-- Every zero-colour equation even has a unit random coefficient. -/
theorem zero_color_coefficient (i : Fin 10) :
    ∃ k : Fin 3, colorCoefficient i k = 1 ∨ colorCoefficient i k = -1 := by
  fin_cases i
  all_goals first
    | exact ⟨0, by decide⟩
    | exact ⟨1, by decide⟩
    | exact ⟨2, by decide⟩

/-- 66 vertex pairs, 45 colour pairs and ten zero-colour equations. -/
theorem number_collision_equations :
    ((Finset.univ : Finset (Fin 12 × Fin 12)).filter (fun p => p.1 < p.2)).card +
    ((Finset.univ : Finset (Fin 10 × Fin 10)).filter (fun p => p.1 < p.2)).card +
    10 = 121 := by decide

end Switch
end EndpointRouter
