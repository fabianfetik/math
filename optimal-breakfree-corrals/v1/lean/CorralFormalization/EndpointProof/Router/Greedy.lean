import CorralFormalization.EndpointProof.Router.Switch
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Forall2
import Mathlib.Tactic.Common

/-!
# Deterministic installation from local primitive availability

The supplier is queried with the *current* numerical forbidden set.  Its
quantifier ranges over all forbidden sets up to the budget, which allows
later adaptive exclusions.  Vertices and colours share one numerical
support here, as in the packed-candidate argument for the router.
-/
namespace EndpointRouter

universe u v w

section Greedy
variable {Q : Type u} {A : Type v} {V : Type w} [DecidableEq V]

/-- Greedily install a prescribed list of local queries.  The hypotheses
are local availability and a numerical support bound; no globally
disjoint family is assumed. -/
theorem greedy_install (good : Q → A → Prop) (support : A → Finset V)
    (weight : Q → ℕ) (budget : ℕ)
    (hsize : ∀ q a, good q a → (support a).card ≤ weight q)
    (queries : List Q) (F : Finset V)
    (hbudget : F.card + (queries.map weight).sum ≤ budget)
    (havail : ∀ q ∈ queries, ∀ F' : Finset V, F'.card ≤ budget →
      ∃ a, good q a ∧ Disjoint (support a) F') :
    ∃ installed : List A,
      List.Forall₂ good queries installed ∧
      installed.Pairwise (fun a b => Disjoint (support a) (support b)) ∧
      (∀ a ∈ installed, Disjoint (support a) F) := by
  induction queries generalizing F with
  | nil => exact ⟨[], .nil, by simp, by simp⟩
  | cons q qs ih =>
    have hF : F.card ≤ budget := by
      have hb := hbudget
      simp only [List.map_cons, List.sum_cons] at hb
      omega
    obtain ⟨a, hgood, havoid⟩ := havail q (by simp) F hF
    let F' := F ∪ support a
    have hbudget' : F'.card + (qs.map weight).sum ≤ budget := by
      have hu := Finset.card_union_le F (support a)
      have hs := hsize q a hgood
      simp only [List.map_cons, List.sum_cons] at hbudget
      dsimp [F']
      omega
    have havail' : ∀ q ∈ qs, ∀ F'' : Finset V, F''.card ≤ budget →
        ∃ a, good q a ∧ Disjoint (support a) F'' := by
      intro q hq F'' hF''
      exact havail q (by simp [hq]) F'' hF''
    obtain ⟨rest, hrest, hpair, hrestavoid⟩ := ih F' hbudget' havail'
    refine ⟨a::rest, .cons hgood hrest, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, hpair⟩
      intro b hb
      exact ((hrestavoid b hb).mono_right Finset.subset_union_right).symm
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact havoid
      · exact (hrestavoid b hb).mono_right Finset.subset_union_left

end Greedy

section Primitives
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

/-- A real length-five idle path, with four freely chosen new vertices. -/
structure Idle (G : Type u) where
  x : G
  y : G
  p : G
  q : G
  r : G
  s : G

namespace Idle
variable (I : Idle G)
def path : EndpointFactor.Segment G := ⟨I.x, [I.p,I.q,I.r,I.s], I.y⟩
def interior : List G := [I.p,I.q,I.r,I.s]
def colors : List G := I.path.colors (fun a b => b-a)
def Valid : Prop := I.path.vertices.Nodup ∧ I.colors.Nodup

omit [AddCommGroup G] [DecidableEq G] in
theorem interior_length : I.interior.length = 4 := rfl
omit [DecidableEq G] in
theorem colors_length : I.colors.length = 5 := rfl
end Idle

/-- Query data are fixed before the local primitive is chosen. -/
inductive Query (G : Type u)
  | idle (x y : G)
  | exchange (x y v w : G)

/-- The installed object contains actual affine coordinates. -/
inductive Primitive (G : Type u)
  | idle (I : Idle G)
  | exchange (S : Switch G)

namespace Query

def arity : Query G → ℕ
  | .idle _ _ => 1
  | .exchange _ _ _ _ => 2

/-- Only the ports, never the random coordinates, occur in this condition. -/
def Legal : Query G → Prop
  | .idle x y => x ≠ y
  | .exchange x y v w =>
    [x,y,v,w].Nodup ∧ v-w ≠ x-y ∧ v-w ≠ -(x-y)
end Query

namespace Primitive

def interior : Primitive G → List G
  | .idle I => I.interior
  | .exchange S => S.interior

def colors : Primitive G → List G
  | .idle I => I.colors
  | .exchange S => S.colors

def support (P : Primitive G) : Finset G :=
  (P.interior ++ P.colors).toFinset

/-- Concrete local success: correct query, actual simple/rainbow paths,
and membership of every random vertex/colour in its own reservoir. -/
def Good (RV RC : Set G) : Query G → Primitive G → Prop
  | .idle x y, .idle I =>
      I.x = x ∧ I.y = y ∧ I.Valid ∧
      (∀ z ∈ I.interior, z ∈ RV) ∧ (∀ c ∈ I.colors, c ∈ RC)
  | .exchange x y v w, .exchange S =>
      S.x = x ∧ S.y = y ∧ S.v = v ∧ S.w = w ∧ S.CollisionFree ∧
      (∀ z ∈ S.interior, z ∈ RV) ∧ (∀ c ∈ S.colors, c ∈ RC)
  | _, _ => False

/-- Nine requests per idle, eighteen per two-track switch. -/
theorem good_support_card (RV RC : Set G) (q : Query G) (P : Primitive G)
    (h : P.Good RV RC q) : P.support.card ≤ 9*q.arity := by
  cases q <;> cases P
  case idle.idle x y I =>
    exact (List.toFinset_card_le _).trans_eq (by rfl)
  case idle.exchange => exact False.elim h
  case exchange.idle => exact False.elim h
  case exchange.exchange x y v w S =>
    exact (List.toFinset_card_le _).trans_eq (by rfl)

end Primitive

/-- Install a fixed schedule of actual router switches and idle paths,
with pairwise disjoint combined numerical supports and avoidance of F.
The only missing supplier is the stated local reservoir availability. -/
theorem install_router_primitives (RV RC : Set G) (budget : ℕ)
    (queries : List (Query G)) (F : Finset G)
    (hlegal : ∀ q ∈ queries, q.Legal)
    (hbudget : F.card + (queries.map (fun q => 9*q.arity)).sum ≤ budget)
    (havail : ∀ q : Query G, q.Legal → ∀ F' : Finset G, F'.card ≤ budget →
      ∃ P : Primitive G, P.Good RV RC q ∧ Disjoint P.support F') :
    ∃ installed : List (Primitive G),
      List.Forall₂ (Primitive.Good RV RC) queries installed ∧
      installed.Pairwise (fun P Q => Disjoint P.support Q.support) ∧
      (∀ P ∈ installed, Disjoint P.support F) := by
  apply greedy_install (Primitive.Good RV RC) Primitive.support
    (fun q => 9*q.arity) budget (Primitive.good_support_card RV RC)
    queries F hbudget
  intro q hq F' hF'
  exact havail q (hlegal q hq) F' hF'

omit [AddCommGroup G] [DecidableEq G] in
private theorem sum_arity_scale (queries : List (Query G)) :
    (queries.map (fun q => 9*q.arity)).sum = 9*(queries.map Query.arity).sum := by
  induction queries with
  | nil => simp
  | cons q qs ih => simp [ih,Nat.mul_add]

/-- The complete two-layer numerical installation budget: n intermediate
ports, at most 2n external ports, and 18n primitive random requests.  The
hypothesis on total arity expresses the schedule of two layers. -/
theorem install_router_primitives_explicit_budget (RV RC : Set G) (budget n : ℕ)
    (queries : List (Query G)) (F external intermediate : Finset G)
    (hlegal : ∀ q ∈ queries, q.Legal)
    (htracks : (queries.map Query.arity).sum = 2*n)
    (hexternal : external.card ≤ 2*n) (hintermediate : intermediate.card ≤ n)
    (hbudget : F.card + 21*n ≤ budget)
    (havail : ∀ q : Query G, q.Legal → ∀ F' : Finset G, F'.card ≤ budget →
      ∃ P : Primitive G, P.Good RV RC q ∧ Disjoint P.support F') :
    ∃ installed : List (Primitive G),
      List.Forall₂ (Primitive.Good RV RC) queries installed ∧
      installed.Pairwise (fun P Q => Disjoint P.support Q.support) ∧
      (∀ P ∈ installed, Disjoint P.support (F ∪ external ∪ intermediate)) := by
  apply install_router_primitives RV RC budget queries (F ∪ external ∪ intermediate)
    hlegal ?_ havail
  have h1 := Finset.card_union_le F external
  have h2 := Finset.card_union_le (F ∪ external) intermediate
  rw [sum_arity_scale, htracks]
  omega

end Primitives
end EndpointRouter
