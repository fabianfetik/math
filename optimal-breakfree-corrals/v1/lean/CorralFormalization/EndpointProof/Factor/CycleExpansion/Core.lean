import CorralFormalization.EndpointProof.Factor.Allocation.ContractedClosure
import Mathlib.GroupTheory.Perm.List

/-! # Expand a contracted cycle of actual path keys into physical vertices -/

open scoped Classical BigOperators
namespace EndpointFactor.CycleExpansion
open OrdinaryFragments FragmentChecksum
noncomputable section
universe u
variable {G : Type u} [AddCommGroup G] [DecidableEq G]

/-- An actual list's head is its first physical vertex. -/
theorem head_first (F : Family G) (k : F.Index) :
    (F.path k).head? = some (F.first k) := by
  cases hp : F.path k with
  | nil => exact False.elim (F.nonempty k hp)
  | cons a p => simp [Family.first,firstOrZero,hp]

theorem last_last (F : Family G) (k : F.Index) :
    (F.path k).getLast? = some (F.last k) := by
  simp [Family.last,lastOrZero,List.getLast?_eq_some_getLast (F.nonempty k)]

theorem edgeLabels_append_one {V C : Type*} (edge : V → V → C)
    (p : List V) (hp : p ≠ []) (y : V) :
    edgeLabels edge (p ++ [y]) = edgeLabels edge p ++ [edge (p.getLast hp) y] := by
  have he := List.dropLast_append_getLast hp
  calc
    edgeLabels edge (p ++ [y]) = edgeLabels edge (p.dropLast ++ p.getLast hp :: [y]) := by
      simpa [List.append_assoc] using congrArg (fun z : List V => edgeLabels edge (z ++ [y])) he.symm
    _ = edgeLabels edge (p.dropLast ++ [p.getLast hp]) ++ [edge (p.getLast hp) y] := by
      rw [edgeLabels_append_pivot]
      rfl
    _ = edgeLabels edge p ++ [edge (p.getLast hp) y] := by rw [he]

private theorem flatMap_head {I : Type*} (p : I → List G) (l : List I) (hl : l ≠ [])
    (hp : ∀ i, p i ≠ []) :
    (l.flatMap p).head? = (p (l.head hl)).head? := by
  cases l with
  | nil => contradiction
  | cons i l =>
    rw [List.flatMap_cons,List.head?_append,List.head?_eq_some_head (hp i)]
    change some ((p i).head (hp i)) = (p i).head?
    exact (List.head?_eq_some_head (hp i)).symm

private theorem flatMap_last {I : Type*} (p : I → List G) (l : List I) (hl : l ≠ [])
    (hp : ∀ i, p i ≠ []) :
    (l.flatMap p).getLast? = (p (l.getLast hl)).getLast? := by
  induction l with
  | nil => contradiction
  | cons i l ih =>
    cases l with
    | nil => simp
    | cons j l =>
      have hn : (j :: l).flatMap p ≠ [] := by simp [hp j]
      rw [List.flatMap_cons,List.getLast?_append_of_ne_nil _ hn]
      exact ih (by simp)

/-- `List.formPerm` gives the physical successor, with its chain and wrap
paid from the actual duplicate-free vertex list. -/
theorem formPerm_chain (q : List G) (hq : q.Nodup) :
    q.IsChain (fun a b => q.formPerm a = b) := by
  apply List.isChain_iff_getElem.mpr
  intro i hi
  exact List.formPerm_apply_lt_getElem q hq i hi

theorem formPerm_wrap (q : List G) (hn : q ≠ []) :
    q.formPerm (q.getLast hn) = q.head hn := by
  cases q with
  | nil => contradiction
  | cons a q => exact List.formPerm_apply_getLast a q

private theorem edge_relation {V : Type*} {R : V → V → Prop} (q : List V)
    (h : q.IsChain R) : ∀ e ∈ edgeLabels (fun a b : V => (a,b)) q, R e.1 e.2 := by
  induction q with
  | nil => simp [edgeLabels]
  | cons a q ih =>
    cases q with
    | nil => simp [edgeLabels]
    | cons b q =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact (List.isChain_cons_cons.mp h).1
      · exact ih (List.isChain_cons_cons.mp h).2 e he

theorem formPerm_of_cyclic_edge (q : List G) (hn : q ≠ []) (hq : q.Nodup)
    (e : G × G) (he : e ∈ edgeLabels (fun a b : G => (a,b)) (q ++ [q.head hn])) :
    q.formPerm e.1 = e.2 := by
  apply edge_relation (R := fun a b => q.formPerm a = b) (q ++ [q.head hn]) ?_ e he
  apply (formPerm_chain q hq).append (by simp)
  intro a ha b hb
  have ha' : a = q.getLast hn := (List.getLast_of_mem_getLast? ha).symm
  have hb' : b = q.head hn := by symm; simpa using hb
  simpa [ha',hb'] using formPerm_wrap q hn

section Expansion
variable {n : ℕ} (F : Family G) (key : Fin n ≃ F.Index)
    (ρ : Equiv.Perm (Fin n)) (root : Fin n) (hc : ρ.IsCycleOn Set.univ)

def trackSegment (i : Fin n) : Segment G where
  first := F.first (key i)
  interior := (F.path (key i)).tail
  last := F.first (key (ρ i))

@[simp] theorem trackSegment_body (i : Fin n) : (trackSegment F key ρ i).body = F.path (key i) := by
  cases hp : F.path (key i) with
  | nil => exact False.elim (F.nonempty _ hp)
  | cons a p => simp [trackSegment,Segment.body,Family.first,firstOrZero,hp]

def trackOrder : CycleOrder ρ root := cycleOrderOfIsCycleOn ρ root hc

def vertices : List G := (trackOrder ρ root hc).order.flatMap (fun i => F.path (key i))

private theorem order_connects (l : List (Fin n))
    (hchain : l.IsChain (fun i j => ρ i = j))
    (hclose : ∀ i, l.getLast? = some i → ρ i = root) :
    Connects (trackSegment F key ρ) l (F.first (key root)) := by
  induction l with
  | nil => trivial
  | cons i l ih =>
    cases l with
    | nil =>
      exact ⟨by simpa [trackSegment,anchor] using congrArg (fun j => F.first (key j)) (hclose i (by simp)),trivial⟩
    | cons j l =>
      refine ⟨?_,ih (List.isChain_cons_cons.mp hchain).2 ?_⟩
      · simpa [trackSegment,anchor] using congrArg (fun j => F.first (key j)) (List.isChain_cons_cons.mp hchain).1
      · intro k hk
        exact hclose k (by simpa using hk)

theorem trackOrder_connects :
    Connects (trackSegment F key ρ) (trackOrder ρ root hc).order (F.first (key root)) :=
  order_connects F key ρ root _ (trackOrder ρ root hc).follows (trackOrder ρ root hc).closes

theorem vertices_head : (vertices F key ρ root hc).head? = some (F.first (key root)) := by
  rw [vertices,flatMap_head _ _ (trackOrder ρ root hc).nonempty (fun i => F.nonempty (key i))]
  have hh : (trackOrder ρ root hc).order.head (trackOrder ρ root hc).nonempty = root :=
    List.head_of_mem_head? (trackOrder ρ root hc).first
  rw [hh]
  exact head_first F _

theorem vertices_nonempty : vertices F key ρ root hc ≠ [] := by
  intro h
  have hh := vertices_head F key ρ root hc
  simp [h] at hh

theorem vertices_last : (vertices F key ρ root hc).getLast? =
    some (F.last (key ((trackOrder ρ root hc).order.getLast (trackOrder ρ root hc).nonempty))) := by
  rw [vertices,flatMap_last _ _ (trackOrder ρ root hc).nonempty (fun i => F.nonempty (key i))]
  exact last_last F _

theorem vertices_nodup : (vertices F key ρ root hc).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun i _ => F.simple _,?_⟩
  apply (trackOrder ρ root hc).nodup.imp
  intro i j hij
  exact F.disjoint _ _ (fun h => hij (key.injective h))

theorem vertices_inventory : (vertices F key ρ root hc).toFinset = F.vertices := by
  ext g
  simp only [vertices,List.mem_toFinset,List.mem_flatMap,Family.mem_vertices]
  constructor
  · rintro ⟨i,_,hi⟩; exact ⟨key i,hi⟩
  · rintro ⟨k,hk⟩
    obtain ⟨i,rfl⟩ := key.surjective k
    exact ⟨i,(trackOrder ρ root hc).covers i,hk⟩

/-- Exact directed pairs, including all closing transitions, in physical
cyclic order. No marked or unmarked label has yet been discarded. -/
theorem cyclic_edges :
    edgeLabels (fun a b : G => (a,b))
      (vertices F key ρ root hc ++ [(vertices F key ρ root hc).head (vertices_nonempty F key ρ root hc)]) =
      (trackOrder ρ root hc).order.flatMap
        (fun i => (trackSegment F key ρ i).colors (fun a b : G => (a,b))) := by
  have hhead : (vertices F key ρ root hc).head (vertices_nonempty F key ρ root hc) = F.first (key root) :=
    List.head_of_mem_head? (vertices_head F key ρ root hc)
  rw [hhead]
  have hexpand : vertices F key ρ root hc ++ [F.first (key root)] =
      expand (trackSegment F key ρ) (trackOrder ρ root hc).order (F.first (key root)) := by
    simp [vertices,expand]
  rw [hexpand]
  exact expand_labels _ _ _ _ (trackOrder_connects F key ρ root hc)

/-- The physical successor at every component end is precisely the next
component's initial vertex under the supplied contracted permutation. -/
theorem successor_at_end (i : Fin n) :
    (vertices F key ρ root hc).formPerm (F.last (key i)) = F.first (key (ρ i)) := by
  apply formPerm_of_cyclic_edge _ (vertices_nonempty F key ρ root hc) (vertices_nodup F key ρ root hc)
    (F.last (key i),F.first (key (ρ i)))
  rw [cyclic_edges]
  apply List.mem_flatMap.mpr
  refine ⟨i,(trackOrder ρ root hc).covers i,?_⟩
  simp only [Segment.colors,Segment.vertices,trackSegment_body]
  rw [edgeLabels_append_one _ _ (F.nonempty _)]
  apply List.mem_append_right
  have hl : (F.path (key i)).getLast (F.nonempty _) = F.last (key i) := by
    simp [Family.last,lastOrZero,List.getLast?_eq_some_getLast (F.nonempty _)]
  simp [hl,trackSegment]

end Expansion
end
end EndpointFactor.CycleExpansion
