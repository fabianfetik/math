import CorralFormalization.EndpointProof.Factor.Join
import Mathlib.Data.List.SplitBy
import Mathlib.Data.Real.Basic

/-!
# Cutting marked edges of an actual cyclic vertex order

The paper first constructs a single cycle whose virtual edges go from the
prescribed terminal set to the prescribed start set. Removing every such
edge should give disjoint paths, not just the single-path case. This module
builds the finite list machinery for that deterministic step.
-/

namespace EndpointFactor.CycleCut

variable {V : Type*} [DecidableEq V]
open scoped BigOperators

/-- Split after a vertex in `ends`; the closing edge is treated separately. -/
def cutAfter (ends : Finset V) (vertices : List V) : List (List V) :=
  vertices.splitBy (fun a _ => decide (a ∉ ends))

@[simp] theorem cutAfter_flatten (ends : Finset V) (vertices : List V) :
    (cutAfter ends vertices).flatten = vertices :=
  List.flatten_splitBy _ _

theorem cutAfter_nonempty_parts (ends : Finset V) (vertices : List V) :
    [] ∉ cutAfter ends vertices := List.nil_notMem_splitBy _ _

theorem cutAfter_partition (ends : Finset V) {vertices : List V}
    (hnodup : vertices.Nodup) :
    (∀ p ∈ cutAfter ends vertices, p.Nodup) ∧
      (cutAfter ends vertices).Pairwise List.Disjoint := by
  apply List.nodup_flatten.mp
  simpa using hnodup

/-- No marked vertex occurs inside one part before its final vertex. -/
theorem cutAfter_internal (ends : Finset V) {vertices p : List V}
    (hp : p ∈ cutAfter ends vertices) :
    p.IsChain (fun a _ => a ∉ ends) := by
  have h := List.isChain_of_mem_splitBy hp
  exact h.imp (by intro a b hab; simpa using hab)

/-- Between consecutive parts the last vertex of the first is marked. -/
theorem cutAfter_boundaries (ends : Finset V) (vertices : List V) :
    (cutAfter ends vertices).IsChain
      (fun p _ => ∀ a ∈ p.getLast?, a ∈ ends) := by
  have h := List.isChain_getLast_head_splitBy (fun a _ => decide (a ∉ ends)) vertices
  apply h.imp
  intro p q hpq a ha
  obtain ⟨hp, hq, hboundary⟩ := hpq
  have heq : p.getLast hp = a := List.getLast_of_mem_getLast? ha
  simpa [heq] using hboundary

private theorem all_of_chain_last {α : Type*} (P : α → Prop) (l : List α)
    (hchain : l.IsChain (fun a _ => P a))
    (hlast : ∀ a ∈ l.getLast?, P a) : ∀ a ∈ l, P a := by
  induction l with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simpa using hlast
    | cons b tail =>
      have hp : P a := (List.isChain_cons_cons.mp hchain).1
      have ht := ih (List.isChain_cons_cons.mp hchain).2 (by simpa using hlast)
      intro x hx
      simp only [List.mem_cons] at hx
      rcases hx with rfl | hx
      · exact hp
      · exact ht x (by simpa only [List.mem_cons] using hx)

/-- If the final vertex of the chosen cyclic order is marked, every part
ends at a marked vertex; this includes the closing edge's last endpoint. -/
theorem cutAfter_all_end_marked (ends : Finset V) {vertices : List V}
    (hn : vertices ≠ []) (hlast : vertices.getLast hn ∈ ends) :
    ∀ p ∈ cutAfter ends vertices, ∀ a ∈ p.getLast?, a ∈ ends := by
  apply all_of_chain_last _ _ (cutAfter_boundaries ends vertices)
  intro p hp a ha
  have hparts : cutAfter ends vertices ≠ [] := List.splitBy_ne_nil.mpr hn
  have hep : (cutAfter ends vertices).getLast hparts = p :=
    List.getLast_of_mem_getLast? hp
  have hpne : p ≠ [] := by
    intro he
    simp [he] at ha
  have hea : p.getLast hpne = a := List.getLast_of_mem_getLast? ha
  have h := List.getLast_getLast_splitBy (fun a _ => decide (a ∉ ends)) hn
  change ((cutAfter ends vertices).getLast hparts).getLast _ = vertices.getLast hn at h
  have he : a = vertices.getLast hn := by simpa only [hep, hea] using h
  simpa [he] using hlast

/-- In a part with a marked last vertex, it is the only marked vertex. -/
private theorem filter_marked_eq_last (ends : Finset V) (p : List V)
    (hne : p ≠ []) (hchain : p.IsChain (fun a _ => a ∉ ends))
    (hlast : p.getLast hne ∈ ends) :
    p.filter (fun a => decide (a ∈ ends)) = [p.getLast hne] := by
  induction p with
  | nil => contradiction
  | cons a rest ih =>
    cases rest with
    | nil => simpa using hlast
    | cons b tail =>
      have ha : a ∉ ends := (List.isChain_cons_cons.mp hchain).1
      have hc : (b :: tail).IsChain (fun a _ => a ∉ ends) :=
        (List.isChain_cons_cons.mp hchain).2
      have hb : (b :: tail).getLast (by simp) ∈ ends := by simpa using hlast
      have hrec := ih (by simp) hc hb
      simpa [ha] using hrec

/-- Cutting after each marked vertex, with the closing cut placed last,
produces exactly as many paths as marked vertices. -/
theorem cutAfter_length_eq_marked_count (ends : Finset V) {vertices : List V}
    (hn : vertices ≠ []) (hlast : vertices.getLast hn ∈ ends) :
    (cutAfter ends vertices).length =
      (vertices.filter (fun a => decide (a ∈ ends))).length := by
  have heach : ∀ p ∈ cutAfter ends vertices,
      List.countP (fun a => decide (a ∈ ends)) p = 1 := by
    intro p hp
    have hpne : p ≠ [] := by
      intro he
      subst p
      exact cutAfter_nonempty_parts ends vertices hp
    have hlastp : p.getLast hpne ∈ ends :=
      cutAfter_all_end_marked ends hn hlast p hp _ (List.getLast_mem_getLast? hpne)
    rw [List.countP_eq_length_filter, filter_marked_eq_last ends p hpne
      (cutAfter_internal ends hp) hlastp]
    rfl
  have hmap : (cutAfter ends vertices).map
      (List.countP (fun a => decide (a ∈ ends))) =
      (cutAfter ends vertices).map (fun _ => (1 : ℕ)) :=
    List.map_congr_left heach
  have hc := List.countP_flatten (p := fun a => decide (a ∈ ends))
    (l := cutAfter ends vertices)
  rw [cutAfter_flatten, List.countP_eq_length_filter, hmap] at hc
  have hones (ps : List (List V)) : (ps.map (fun _ => (1 : ℕ))).sum = ps.length := by
    induction ps with
    | nil => rfl
    | cons p ps ih => simp [Nat.add_comm]
  rw [hones] at hc
  exact hc.symm

/-- Under the actual vertex inventory and simplicity conditions, the number
of resulting paths is exactly the prescribed terminal-set cardinality. -/
theorem cutAfter_length_eq_card (ends : Finset V) {vertices : List V}
    (hn : vertices ≠ []) (hlast : vertices.getLast hn ∈ ends)
    (hnodup : vertices.Nodup) (hsubset : ends ⊆ vertices.toFinset) :
    (cutAfter ends vertices).length = ends.card := by
  rw [cutAfter_length_eq_marked_count ends hn hlast]
  rw [← List.toFinset_card_of_nodup (hnodup.filter _), List.toFinset_filter]
  congr 1
  ext a
  simp only [Finset.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun ha => ⟨hsubset ha, ha⟩⟩

/-- The actual terminal vertices of the parts are exactly `ends`. -/
theorem cutAfter_terminal_inventory (ends : Finset V) {vertices : List V}
    (hn : vertices ≠ []) (hlast : vertices.getLast hn ∈ ends)
    (hsubset : ends ⊆ vertices.toFinset) (a : V) :
    (∃ p ∈ cutAfter ends vertices, a ∈ p.getLast?) ↔ a ∈ ends := by
  constructor
  · rintro ⟨p, hp, ha⟩
    exact cutAfter_all_end_marked ends hn hlast p hp a ha
  · intro ha
    have hav : a ∈ vertices := List.mem_toFinset.mp (hsubset ha)
    rw [← cutAfter_flatten ends vertices, List.mem_flatten] at hav
    obtain ⟨p, hp, hap⟩ := hav
    have hpne : p ≠ [] := by
      intro he
      subst p
      exact cutAfter_nonempty_parts ends vertices hp
    have hlastp : p.getLast hpne ∈ ends :=
      cutAfter_all_end_marked ends hn hlast p hp _ (List.getLast_mem_getLast? hpne)
    have haf : a ∈ p.filter (fun v => decide (v ∈ ends)) := by simpa using ⟨hap, ha⟩
    rw [filter_marked_eq_last ends p hpne (cutAfter_internal ends hp) hlastp] at haf
    have heq : a = p.getLast hpne := by simpa using haf
    refine ⟨p, hp, ?_⟩
    simpa [heq] using List.getLast_mem_getLast? hpne

omit [DecidableEq V] in
private theorem edgeLabels_append_nonempty {C : Type*} (edge : V → V → C)
    (p q : List V) (hp : p ≠ []) (hq : q ≠ []) :
    edgeLabels edge (p ++ q) =
      edgeLabels edge p ++ [edge (p.getLast hp) (q.head hq)] ++ edgeLabels edge q := by
  cases q with
  | nil => contradiction
  | cons b tail =>
    calc
      edgeLabels edge (p ++ b :: tail) =
          edgeLabels edge (p.dropLast ++ p.getLast hp :: b :: tail) := by
            congr 1
            simpa [List.append_assoc] using
              congrArg (fun xs => xs ++ b :: tail) (List.dropLast_append_getLast hp).symm
      _ = edgeLabels edge (p.dropLast ++ [p.getLast hp]) ++
            edgeLabels edge (p.getLast hp :: b :: tail) :=
          edgeLabels_append_pivot edge p.dropLast (b :: tail) (p.getLast hp)
      _ = edgeLabels edge p ++ [edge (p.getLast hp) ((b :: tail).head hq)] ++
            edgeLabels edge (b :: tail) := by
          simp [List.dropLast_append_getLast hp, edgeLabels, List.append_assoc]

omit [DecidableEq V] in
private theorem directedEdges_avoid_marked (ends : Finset V) (p : List V)
    (h : p.IsChain (fun a _ => a ∉ ends)) :
    ∀ e ∈ edgeLabels (fun a b : V => (a, b)) p, e.1 ∉ ends := by
  induction p with
  | nil => simp [edgeLabels]
  | cons a rest ih =>
    cases rest with
    | nil => simp [edgeLabels]
    | cons b tail =>
      have ht := (List.isChain_cons_cons.mp h).2
      have ha := (List.isChain_cons_cons.mp h).1
      intro e he
      simp only [edgeLabels, List.mem_cons] at he
      rcases he with he | he
      · subst e
        exact ha
      · exact ih ht e he

private theorem filter_directedEdges_self (ends : Finset V) (p : List V)
    (h : p.IsChain (fun a _ => a ∉ ends)) :
    (edgeLabels (fun a b : V => (a, b)) p).filter
      (fun e => decide (e.1 ∉ ends)) = edgeLabels (fun a b : V => (a, b)) p := by
  apply List.filter_eq_self.mpr
  intro e he
  simpa using directedEdges_avoid_marked ends p h e he

private theorem directedEdges_parts (ends : Finset V) (parts : List (List V))
    (hne : [] ∉ parts)
    (hinside : ∀ p ∈ parts, p.IsChain (fun a _ => a ∉ ends))
    (hboundary : parts.IsChain (fun p _ => ∀ a ∈ p.getLast?, a ∈ ends)) :
    parts.flatMap (edgeLabels (fun a b : V => (a, b))) =
      (edgeLabels (fun a b : V => (a, b)) parts.flatten).filter
        (fun e => decide (e.1 ∉ ends)) := by
  induction parts with
  | nil => simp [edgeLabels]
  | cons p rest ih =>
    have hpne : p ≠ [] := by
      intro he
      subst p
      exact hne (by simp)
    have hp : p.IsChain (fun a _ => a ∉ ends) := hinside p (by simp)
    have hne' : [] ∉ rest := by
      intro h
      exact hne (by simp [h])
    have hinside' : ∀ q ∈ rest, q.IsChain (fun a _ => a ∉ ends) := by
      intro q hq
      exact hinside q (by simp [hq])
    have htail := ih hne' hinside' hboundary.tail
    cases rest with
    | nil =>
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.flatten_cons, List.flatten_nil]
      simpa using (filter_directedEdges_self ends p hp).symm
    | cons q qs =>
      have hqne : q ≠ [] := by
        intro he
        subst q
        exact hne' (by simp)
      have hrestne : (q :: qs).flatten ≠ [] :=
        List.flatten_ne_nil_iff.mpr ⟨q, by simp, hqne⟩
      have hmark : p.getLast hpne ∈ ends :=
        (List.isChain_cons_cons.mp hboundary).1 _ (List.getLast_mem_getLast? hpne)
      change edgeLabels (fun a b : V => (a, b)) p ++
          (q :: qs).flatMap (edgeLabels (fun a b : V => (a, b))) =
        (edgeLabels (fun a b : V => (a, b)) (p ++ (q :: qs).flatten)).filter
          (fun e => decide (e.1 ∉ ends))
      rw [edgeLabels_append_nonempty _ p ((q :: qs).flatten) hpne hrestne]
      simp only [List.filter_append, List.filter_cons, List.filter_nil]
      simp only [filter_directedEdges_self ends p hp, hmark, not_true_eq_false,
        decide_false, Bool.false_eq_true, if_false, List.append_nil]
      exact congrArg (fun z => edgeLabels (fun a b : V => (a, b)) p ++ z) htail

/-- The paths retain exactly the directed edges whose source is not marked.
Filtering directed edges, rather than their labels, permits a virtual edge's
colour to coincide with a real colour without corrupting the inventory. -/
theorem cutAfter_directed_edges (ends : Finset V) (vertices : List V) :
    (cutAfter ends vertices).flatMap (edgeLabels (fun a b : V => (a, b))) =
      (edgeLabels (fun a b : V => (a, b)) vertices).filter
        (fun e => decide (e.1 ∉ ends)) := by
  have h := directedEdges_parts ends (cutAfter ends vertices)
    (cutAfter_nonempty_parts ends vertices) (fun _ hp => cutAfter_internal ends hp)
    (cutAfter_boundaries ends vertices)
  simpa using h

private theorem predecessor_of_mem_tail {α : Type*} (R : α → α → Prop)
    (first : α) (tail : List α) (h : (first :: tail).IsChain R)
    (x : α) (hx : x ∈ tail) : ∃ y ∈ first :: tail, R y x := by
  induction tail generalizing first with
  | nil => simp at hx
  | cons b tail ih =>
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨first, by simp, (List.isChain_cons_cons.mp h).1⟩
    · obtain ⟨y, hy, hyx⟩ := ih b (List.isChain_cons_cons.mp h).2 hx
      exact ⟨y, by simp [hy], hyx⟩

/-- Every member of a finite cyclic chain has a predecessor in that chain. -/
private theorem cyclic_predecessor {α : Type*} (R : α → α → Prop)
    (l : List α) (hn : l ≠ []) (h : l.IsChain R)
    (hwrap : R (l.getLast hn) (l.head hn)) :
    ∀ x ∈ l, ∃ y ∈ l, R y x := by
  cases l with
  | nil => contradiction
  | cons a tail =>
    intro x hx
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ⟨(x :: tail).getLast hn, List.getLast_mem hn, by simpa using hwrap⟩
    · exact predecessor_of_mem_tail R a tail h x hx

/-- Every member of a finite cyclic chain also has a successor in it. -/
private theorem cyclic_successor {α : Type*} (R : α → α → Prop)
    (l : List α) (hn : l ≠ []) (h : l.IsChain R)
    (hwrap : R (l.getLast hn) (l.head hn)) :
    ∀ x ∈ l, ∃ y ∈ l, R x y := by
  have hrn : l.reverse ≠ [] := by simpa using hn
  have hr : l.reverse.IsChain (fun a b => R b a) := List.isChain_reverse.mpr h
  have hrw : R (l.reverse.head hrn) (l.reverse.getLast hrn) := by
    simpa only [List.head_reverse, List.getLast_reverse] using hwrap
  intro x hx
  obtain ⟨y, hy, hyx⟩ := cyclic_predecessor (fun a b => R b a) l.reverse hrn hr hrw x
    (by simpa using hx)
  exact ⟨y, by simpa using hy, hyx⟩

private def Follows (next : V → V) (p q : List V) : Prop :=
  ∀ a ∈ p.getLast?, ∀ b ∈ q.head?, next a = b

private theorem cutAfter_follows (ends : Finset V) {vertices : List V}
    (next : V → V) (hn : vertices ≠ [])
    (hchain : vertices.IsChain (fun a b => next a = b))
    (hwrap : next (vertices.getLast hn) = vertices.head hn) :
    let parts := cutAfter ends vertices
    ∃ hparts : parts ≠ [],
      parts.IsChain (Follows next) ∧
        Follows next (parts.getLast hparts) (parts.head hparts) := by
  let parts := cutAfter ends vertices
  have hparts : parts ≠ [] := List.splitBy_ne_nil.mpr hn
  refine ⟨hparts, ?_, ?_⟩
  · have hflat : parts.flatten.IsChain (fun a b => next a = b) := by
      simpa [parts] using hchain
    exact ((List.isChain_flatten (cutAfter_nonempty_parts ends vertices)).mp hflat).2
  · intro a ha b hb
    have hlast := List.getLast_getLast_splitBy (fun a _ => decide (a ∉ ends)) hn
    have hfirst := List.head_head_splitBy (fun a _ => decide (a ∉ ends)) hn
    change (parts.getLast hparts).getLast _ = vertices.getLast hn at hlast
    change (parts.head hparts).head _ = vertices.head hn at hfirst
    have hea : a = vertices.getLast hn := (List.getLast_of_mem_getLast? ha).symm.trans hlast
    have heb : b = vertices.head hn := (List.head_of_mem_head? hb).symm.trans hfirst
    simpa [hea, heb] using hwrap

/-- The path starts are exactly the successors of the marked ends, including
the chosen closing edge. No disjointness or injectivity is assumed here. -/
theorem cutAfter_initial_inventory (ends : Finset V) {vertices : List V}
    (next : V → V) (hn : vertices ≠ [])
    (hlast : vertices.getLast hn ∈ ends) (hsubset : ends ⊆ vertices.toFinset)
    (hchain : vertices.IsChain (fun a b => next a = b))
    (hwrap : next (vertices.getLast hn) = vertices.head hn) (x : V) :
    (∃ p ∈ cutAfter ends vertices, x ∈ p.head?) ↔ x ∈ ends.image next := by
  obtain ⟨hparts, hfollow, hcycle⟩ := cutAfter_follows ends next hn hchain hwrap
  constructor
  · rintro ⟨p, hp, hxp⟩
    obtain ⟨q, hq, hqp⟩ :=
      cyclic_predecessor (Follows next) _ hparts hfollow hcycle p hp
    have hqne : q ≠ [] := by
      intro he
      subst q
      exact cutAfter_nonempty_parts ends vertices hq
    let y := q.getLast hqne
    have hyq : y ∈ q.getLast? := List.getLast_mem_getLast? hqne
    have hy : y ∈ ends := cutAfter_all_end_marked ends hn hlast q hq y hyq
    exact Finset.mem_image.mpr ⟨y, hy, hqp y hyq x hxp⟩
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨p, hp, hyp⟩ := (cutAfter_terminal_inventory ends hn hlast hsubset y).mpr hy
    obtain ⟨q, hq, hpq⟩ :=
      cyclic_successor (Follows next) _ hparts hfollow hcycle p hp
    have hqne : q ≠ [] := by
      intro he
      subst q
      exact cutAfter_nonempty_parts ends vertices hq
    let z := q.head hqne
    have hzq : z ∈ q.head? := List.head_mem_head? hqne
    have heq : next y = z := hpq y hyp z hzq
    exact ⟨q, hq, by simpa [heq] using hzq⟩

/-- The real edge labels of all paths are exactly the labels of the
unmarked directed edges of the original linear order, in that order. -/
theorem cutAfter_real_labels {C : Type*} (edge : V → V → C)
    (ends : Finset V) (vertices : List V) :
    (cutAfter ends vertices).flatMap (edgeLabels edge) =
      ((edgeLabels (fun a b : V => (a, b)) vertices).filter
        (fun e => decide (e.1 ∉ ends))).map (fun e => edge e.1 e.2) := by
  have h := congrArg (List.map (fun e : V × V => edge e.1 e.2))
    (cutAfter_directed_edges ends vertices)
  rw [List.map_flatMap] at h
  have hmap : (fun p : List V =>
      (edgeLabels (fun a b : V => (a, b)) p).map (fun e => edge e.1 e.2)) =
      edgeLabels edge := by
    funext p
    simpa using (edgeLabels_map (fun a b : V => (a, b)) (fun e => edge e.1 e.2) p).symm
  rw [hmap] at h
  exact h

/-- A finite rainbow path factor in the physical additive group. Its lists
are disjoint and cover `W`; their directed differences cover `D` exactly
once; and their initial and terminal inventories are exactly `X` and `Y`. -/
def PhysicalPathFactor {G : Type*} [AddCommGroup G] [DecidableEq G]
    (W D X Y : Finset G) : Prop :=
  ∃ paths : List (List G),
    [] ∉ paths ∧ paths.length = Y.card ∧ paths.flatten.Nodup ∧
    paths.flatten.toFinset = W ∧
    (paths.flatMap (edgeLabels (fun a b : G => b - a))).Nodup ∧
    (paths.flatMap (edgeLabels (fun a b : G => b - a))).toFinset = D ∧
    (∀ a, (∃ p ∈ paths, a ∈ p.head?) ↔ a ∈ X) ∧
    (∀ a, (∃ p ∈ paths, a ∈ p.getLast?) ↔ a ∈ Y)

/-- Actual real directed differences after the marked outgoing edges are
removed. The closing edge is marked because the chosen order ends in `Y`. -/
def realDifferences {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y : Finset G) (vertices : List G) : List G :=
  ((edgeLabels (fun a b : G => (a, b)) vertices).filter
    (fun e => decide (e.1 ∉ Y))).map (fun e => e.2 - e.1)

/-- Close the actual order before removing virtual edges. -/
def cyclicRealDifferences {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y : Finset G) (vertices : List G) (hn : vertices ≠ []) : List G :=
  ((edgeLabels (fun a b : G => (a, b)) (vertices ++ [vertices.head hn])).filter
    (fun e => decide (e.1 ∉ Y))).map (fun e => e.2 - e.1)

private theorem cyclicRealDifferences_of_last {G : Type*} [AddCommGroup G] [DecidableEq G]
    (Y : Finset G) (vertices : List G) (hn : vertices ≠ [])
    (hlast : vertices.getLast hn ∈ Y) :
    cyclicRealDifferences Y vertices hn = realDifferences Y vertices := by
  unfold cyclicRealDifferences realDifferences
  rw [edgeLabels_append_nonempty _ vertices [vertices.head hn] hn (by simp)]
  simp [edgeLabels, hlast]

private theorem cyclicRealDifferences_empty {G : Type*} [AddCommGroup G] [DecidableEq G]
    (vertices : List G) (hn : vertices ≠ []) :
    cyclicRealDifferences ∅ vertices hn =
      edgeLabels (fun a b : G => b - a) (vertices ++ [vertices.head hn]) := by
  unfold cyclicRealDifferences
  simpa using (edgeLabels_map (fun a b : G => (a, b)) (fun e => e.2 - e.1)
    (vertices ++ [vertices.head hn])).symm

/-- A directed rainbow cycle with the exact physical vertex and difference
sets, including its closing edge. -/
def PhysicalCycle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (W D : Finset G) : Prop :=
  ∃ vertices : List G, ∃ hn : vertices ≠ [],
    vertices.Nodup ∧ vertices.toFinset = W ∧
      (edgeLabels (fun a b : G => b - a) (vertices ++ [vertices.head hn])).Nodup ∧
      (edgeLabels (fun a b : G => b - a) (vertices ++ [vertices.head hn])).toFinset = D

/-- Deterministic final step of the paper's positive-`K` case: cutting one
actual cyclic order at its marked virtual edges yields the physical path
factor, with exact vertex, colour and endpoint inventories. -/
theorem pathFactor_of_marked_cycle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (W D X Y : Finset G) (vertices : List G) (next : G → G)
    (hn : vertices ≠ []) (hlast : vertices.getLast hn ∈ Y)
    (hnodup : vertices.Nodup) (hvertices : vertices.toFinset = W)
    (hY : Y ⊆ W) (hX : Y.image next = X)
    (hchain : vertices.IsChain (fun a b => next a = b))
    (hwrap : next (vertices.getLast hn) = vertices.head hn)
    (hcolors : (realDifferences Y vertices).Nodup)
    (hD : (realDifferences Y vertices).toFinset = D) :
    PhysicalPathFactor W D X Y := by
  have hsubset : Y ⊆ vertices.toFinset := by simpa [hvertices] using hY
  refine ⟨cutAfter Y vertices, cutAfter_nonempty_parts Y vertices,
    cutAfter_length_eq_card Y hn hlast hnodup hsubset, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using hnodup
  · simpa using hvertices
  · simpa [realDifferences, cutAfter_real_labels] using hcolors
  · simpa [realDifferences, cutAfter_real_labels] using hD
  · intro a
    simpa [hX] using cutAfter_initial_inventory Y next hn hlast hsubset hchain hwrap a
  · intro a
    exact cutAfter_terminal_inventory Y hn hlast hsubset a

/-- Both terminal cases from the same actual cyclic order. If virtual edges
exist the chosen order is rooted immediately after one of them, so its last
vertex is marked. The input only describes the already-constructed cycle;
it does not assume a path factor or the paper's uniform existence theorem. -/
theorem physicalConclusion_of_marked_cycle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (W D X Y : Finset G) (vertices : List G) (next : G → G)
    (hn : vertices ≠ []) (hlast : Y.Nonempty → vertices.getLast hn ∈ Y)
    (hnodup : vertices.Nodup) (hvertices : vertices.toFinset = W)
    (hY : Y ⊆ W) (hX : Y.image next = X)
    (hchain : vertices.IsChain (fun a b => next a = b))
    (hwrap : next (vertices.getLast hn) = vertices.head hn)
    (hcolors : (cyclicRealDifferences Y vertices hn).Nodup)
    (hD : (cyclicRealDifferences Y vertices hn).toFinset = D) :
    (Y = ∅ ∧ X = ∅ ∧ PhysicalCycle W D) ∨
      (Y.Nonempty ∧ PhysicalPathFactor W D X Y) := by
  by_cases hempty : Y = ∅
  · left
    have hx : X = ∅ := by simpa [hempty] using hX.symm
    refine ⟨hempty, hx, vertices, hn, hnodup, hvertices, ?_, ?_⟩
    · simpa [hempty, cyclicRealDifferences_empty] using hcolors
    · simpa [hempty, cyclicRealDifferences_empty] using hD
  · right
    have hnonempty : Y.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    refine ⟨hnonempty, pathFactor_of_marked_cycle W D X Y vertices next hn (hlast hnonempty)
      hnodup hvertices hY hX hchain hwrap ?_ ?_⟩
    · simpa [cyclicRealDifferences_of_last Y vertices hn (hlast hnonempty)] using hcolors
    · simpa [cyclicRealDifferences_of_last Y vertices hn (hlast hnonempty)] using hD

/-- The two exact output clauses of the paper, indexed by the start set. -/
def PhysicalEndpointConclusion {G : Type*} [AddCommGroup G] [DecidableEq G]
    (W D X Y : Finset G) : Prop :=
  (X = ∅ → PhysicalCycle W D) ∧ (X.Nonempty → PhysicalPathFactor W D X Y)

/-- An actual installed and closed marked cycle supplies both paper cases;
the next remaining obligation is to construct such a cycle for each query. -/
theorem endpointConclusion_of_marked_cycle {G : Type*} [AddCommGroup G] [DecidableEq G]
    (W D X Y : Finset G) (vertices : List G) (next : G → G)
    (hn : vertices ≠ []) (hlast : Y.Nonempty → vertices.getLast hn ∈ Y)
    (hnodup : vertices.Nodup) (hvertices : vertices.toFinset = W)
    (hY : Y ⊆ W) (hX : Y.image next = X)
    (hchain : vertices.IsChain (fun a b => next a = b))
    (hwrap : next (vertices.getLast hn) = vertices.head hn)
    (hcolors : (cyclicRealDifferences Y vertices hn).Nodup)
    (hD : (cyclicRealDifferences Y vertices hn).toFinset = D) :
    PhysicalEndpointConclusion W D X Y := by
  rcases physicalConclusion_of_marked_cycle W D X Y vertices next hn hlast hnodup
      hvertices hY hX hchain hwrap hcolors hD with hzero | hpositive
  · obtain ⟨hY0, hX0, hcycle⟩ := hzero
    refine ⟨fun _ => hcycle, ?_⟩
    intro hne
    exact (hne.ne_empty hX0).elim
  · obtain ⟨hYne, hfactor⟩ := hpositive
    have hXne : X.Nonempty := by
      obtain ⟨y, hy⟩ := hYne
      refine ⟨next y, ?_⟩
      rw [← hX]
      exact Finset.mem_image.mpr ⟨y, hy, rfl⟩
    refine ⟨?_, fun _ => hfactor⟩
    intro he
    exact (hXne.ne_empty he).elim

universe u

/-- Literal odd-abelian target of Theorem 9. This definition exposes the
remaining uniform existence claim; it is not itself a proof of that claim. -/
def UniformPhysicalEndpointCompletion : Prop := by
  classical
  exact ∃ ε0 : ℝ, 0 < ε0 ∧ ∃ n0 : ℕ,
    ∀ (G : Type u) [Fintype G] [AddCommGroup G],
      Odd (Fintype.card G) → n0 ≤ Fintype.card G →
      ∀ W D X Y : Finset G,
        X ⊆ W → Y ⊆ W → Disjoint X Y → X.card = Y.card →
        (X.card : ℝ) ≤ ε0 * (Fintype.card G : ℝ) →
        (1 - ε0) * (Fintype.card G : ℝ) ≤ (W.card : ℝ) →
        (0 : G) ∉ D → D.card + X.card = W.card →
        (∑ d ∈ D, d) = (∑ y ∈ Y, y) - (∑ x ∈ X, x) →
        PhysicalEndpointConclusion W D X Y

namespace Example

def vertices : List (ZMod 11) := [0, 1, 4, 6, 10, 7]

def next (x : ZMod 11) : ZMod 11 :=
  if x = 0 then 1 else if x = 1 then 4 else if x = 4 then 6 else
  if x = 6 then 10 else if x = 10 then 7 else if x = 7 then 0 else x

/-- Two virtual cuts give two actual paths, with the requested terminal
and start sets. The closing virtual colour equals an actual path colour. -/
theorem two_path_factor :
    PhysicalPathFactor ({0, 1, 4, 6, 10, 7} : Finset (ZMod 11))
      {1, 3, 4, 8} {0, 6} {4, 7} := by
  apply pathFactor_of_marked_cycle _ _ _ _ vertices next (by decide)
  all_goals decide

theorem virtual_colour_can_equal_real :
    ((0 : ZMod 11) - 7) ∈ realDifferences {4, 7} vertices := by decide

theorem zero_terminal_cycle :
    PhysicalCycle ({0, 1, 3} : Finset (ZMod 11)) {1, 2, 8} := by
  refine ⟨[0, 1, 3], by decide, ?_, ?_, ?_, ?_⟩ <;> decide

end Example

end EndpointFactor.CycleCut
