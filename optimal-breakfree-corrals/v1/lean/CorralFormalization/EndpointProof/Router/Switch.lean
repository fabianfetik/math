import CorralFormalization.EndpointProof.Factor.Join
import Mathlib.Data.List.Permutation

/-!
# The two-setting length-five router switch

These are exactly the affine paths in the two-layer router, rather than the
absorber switches in `EndpointProof.Selector`.  The free parameters are
already chosen.  `CollisionFree` is the explicit, finite local obligation
that a later availability argument must discharge.
-/
namespace EndpointRouter

open EndpointFactor

universe u
variable {G : Type u} [AddCommGroup G]

structure Switch (G : Type u) where
  x : G
  y : G
  v : G
  w : G
  h : G
  d : G
  f : G

namespace Switch

variable (S : Switch G)

def a : G := S.w - S.f
def c : G := S.v - S.f

/-- Exactly the port hypothesis in (4.1). -/
def LegalPorts : Prop :=
  [S.x, S.y, S.v, S.w].Nodup ∧
    S.v - S.w ≠ S.x - S.y ∧ S.v - S.w ≠ -(S.x - S.y)

/-- Eight new vertices; the ports are deliberately excluded. -/
def interior : List G :=
  [S.a, S.h, S.d + S.x, S.d + S.y,
    S.d + S.h, S.d + S.c, S.f + S.x, S.f + S.y]

def vertices : List G := [S.x, S.y, S.v, S.w] ++ S.interior

/-- The common list (4.2), in its published order. -/
def colors : List G :=
  [S.a-S.x, S.d+S.x-S.a, S.h-S.x, S.f+S.x-S.d-S.h, S.c-S.x,
   S.h-S.y, S.d+S.y-S.h, S.c-S.y, S.f+S.y-S.d-S.c, S.a-S.y]

/-- These finite collision obligations contain no existential path premise. -/
def CollisionFree : Prop := S.vertices.Nodup ∧ S.colors.Nodup

/-- `false` is the straight setting, `true` exchanges the two outputs. -/
def path (cross : Bool) (track : Bool) : Segment G :=
  if cross then
    if track then ⟨S.y, [S.a, S.d+S.x, S.d+S.c, S.f+S.y], S.v⟩
    else ⟨S.x, [S.h, S.d+S.y, S.d+S.h, S.f+S.x], S.w⟩
  else
    if track then ⟨S.y, [S.h, S.d+S.y, S.d+S.c, S.f+S.y], S.w⟩
    else ⟨S.x, [S.a, S.d+S.x, S.d+S.h, S.f+S.x], S.v⟩

@[simp] theorem path_first (cross track : Bool) :
    (S.path cross track).first = if track then S.y else S.x := by
  cases cross <;> cases track <;> rfl

@[simp] theorem path_last (cross track : Bool) :
    (S.path cross track).last = if cross != track then S.w else S.v := by
  cases cross <;> cases track <;> rfl

@[simp] theorem path_interior_length (cross track : Bool) :
    (S.path cross track).interior.length = 4 := by
  cases cross <;> cases track <;> rfl

@[simp] theorem path_length (cross track : Bool) :
    (S.path cross track).vertices.length = 6 := by
  cases cross <;> cases track <;> rfl

@[simp] theorem path_colors_length (cross track : Bool) :
    ((S.path cross track).colors (fun a b => b-a)).length = 5 := by
  rw [Segment.colors_length]
  simp [Segment.body]

/-- Every setting uses exactly the same twelve vertices, with multiplicity. -/
theorem vertices_perm (cross : Bool) :
    ((S.path cross false).vertices ++ (S.path cross true).vertices).Perm S.vertices := by
  classical
  apply List.perm_iff_count.mpr
  intro z
  cases cross <;>
    simp [path, Segment.vertices, Segment.body, vertices, interior,
      List.count_cons] <;> omega

/-- The new vertices, separately from the four ports, are unchanged. -/
theorem interior_perm (cross : Bool) :
    ((S.path cross false).interior ++ (S.path cross true).interior).Perm S.interior := by
  classical
  apply List.perm_iff_count.mpr
  intro z
  cases cross <;> simp [path, interior, List.count_cons] <;> omega

private theorem straight_colors :
    (S.path false false).colors (fun a b => b-a) ++
      (S.path false true).colors (fun a b => b-a) = S.colors := by
  simp only [path, Bool.false_eq_true, ↓reduceIte, Segment.colors,
    Segment.vertices, Segment.body, edgeLabels,
    List.cons_append, List.nil_append]
  unfold colors a c
  congr 1
  abel_nf

private theorem crossed_colors :
    (S.path true false).colors (fun a b => b-a) ++
      (S.path true true).colors (fun a b => b-a) =
    [S.h-S.x, S.d+S.y-S.h, S.h-S.y, S.f+S.x-S.d-S.h, S.a-S.x,
      S.a-S.y, S.d+S.x-S.a, S.c-S.x, S.f+S.y-S.d-S.c, S.c-S.y] := by
  simp only [path, Bool.false_eq_true, ↓reduceIte, Segment.colors,
    Segment.vertices, Segment.body, edgeLabels,
    List.cons_append, List.nil_append]
  unfold a c
  congr 1
  abel_nf

/-- The ten actual directed differences are unchanged, with multiplicity. -/
theorem colors_perm (cross : Bool) :
    ((S.path cross false).colors (fun a b => b-a) ++
      (S.path cross true).colors (fun a b => b-a)).Perm S.colors := by
  cases cross with
  | false => rw [S.straight_colors]
  | true =>
    rw [S.crossed_colors]
    classical
    apply List.perm_iff_count.mpr
    intro z
    simp [colors, List.count_cons]
    omega

/-- Concrete simplicity, rainbow property, cross-track disjointness and
nonzero labels for either setting.  The assumptions concern only the fixed
coordinate lists, so no setting is chosen until after installation. -/
theorem setting_valid (h : S.CollisionFree) (cross : Bool) :
    ((S.path cross false).vertices ++ (S.path cross true).vertices).Nodup ∧
    ((S.path cross false).colors (fun a b => b-a) ++
      (S.path cross true).colors (fun a b => b-a)).Nodup ∧
    (∀ track, (S.path cross track).vertices.Nodup) ∧
    (∀ track, ((S.path cross track).colors (fun a b => b-a)).Nodup) ∧
    (∀ track, ∀ d ∈ (S.path cross track).colors (fun a b => b-a), d ≠ 0) := by
  have hv := (S.vertices_perm cross).nodup_iff.mpr h.1
  have hc := (S.colors_perm cross).nodup_iff.mpr h.2
  have hs : ∀ track, (S.path cross track).vertices.Nodup := by
    intro track
    cases track
    · exact hv.of_append_left
    · exact hv.of_append_right
  refine ⟨hv, hc, hs, ?_, ?_⟩
  · intro track
    cases track
    · exact hc.of_append_left
    · exact hc.of_append_right
  · intro track
    exact difference_labels_nonzero _ (hs track)

/-- Membership form is convenient for reservoir and forbidden-set proofs. -/
theorem interior_inventory (cross : Bool) (z : G) :
    z ∈ (S.path cross false).interior ∨ z ∈ (S.path cross true).interior ↔
      z ∈ S.interior := by
  rw [← List.mem_append]
  exact (S.interior_perm cross).mem_iff

theorem color_inventory (cross : Bool) (z : G) :
    z ∈ (S.path cross false).colors (fun a b => b-a) ∨
      z ∈ (S.path cross true).colors (fun a b => b-a) ↔ z ∈ S.colors := by
  rw [← List.mem_append]
  exact (S.colors_perm cross).mem_iff

/-- Exact finite inventories once the local collision tests pass. -/
theorem inventory_cards [DecidableEq G] (h : S.CollisionFree) :
    S.interior.toFinset.card = 8 ∧ S.colors.toFinset.card = 10 ∧
    List.Disjoint [S.x,S.y,S.v,S.w] S.interior := by
  have hi := h.1.of_append_right
  have hd := (List.nodup_append.mp h.1).2.2
  refine ⟨?_, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hi]
    rfl
  · rw [List.toFinset_card_of_nodup h.2]
    rfl
  · exact List.disjoint_left.mpr (fun z hz hz' => hd z hz z hz' rfl)

/-- Every entry of the fixed common colour inventory is a real nonzero
edge in either setting. -/
theorem colors_nonzero (h : S.CollisionFree) : ∀ d ∈ S.colors, d ≠ 0 := by
  intro d hd
  have hm := (S.colors_perm false).mem_iff.mpr hd
  rcases List.mem_append.mp hm with hm | hm
  · exact (S.setting_valid h false).2.2.2.2 false d hm
  · exact (S.setting_valid h false).2.2.2.2 true d hm

end Switch
end EndpointRouter
