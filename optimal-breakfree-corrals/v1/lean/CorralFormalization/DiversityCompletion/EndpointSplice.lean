import CorralFormalization.DiversityCompletion.DirectedTerraceCompletion
import Mathlib.Data.List.NodupEquivFin

namespace CorralFormalization.LatinCompletion.TerraceCompletion

open LatinTransfer TerraceLift LatinPrefix LatinPrefixSupply

/-- Positive representatives of the actual consecutive directed edges of
a list path. Unlike a cyclic calendar, this has no extra closing edge. -/
def pathGaps {n : ℕ} : List (ZMod n) → List ℕ
  | [] => []
  | [_] => []
  | x::y::rest => (y-x).val :: pathGaps (y::rest)

theorem pathGaps_length {n : ℕ} (w : List (ZMod n)) :
    (pathGaps w).length = w.length-1 := by
  induction w with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simpa [pathGaps] using ih

theorem pathGaps_append_pivot {n : ℕ} (xs ys : List (ZMod n)) (z : ZMod n) :
    pathGaps (xs ++ z::ys) = pathGaps (xs ++ [z]) ++ pathGaps (z::ys) := by
  induction xs with
  | nil => simp [pathGaps]
  | cons x xs ih =>
    cases xs with
    | nil => simp [pathGaps]
    | cons y ys' => simpa [pathGaps] using congrArg (List.cons (y-x).val) ih

theorem pathGaps_getElem {n : ℕ} (w : List (ZMod n)) (i : ℕ) (hi : i+1 < w.length) :
    (pathGaps w)[i]'(by rw [pathGaps_length]; omega) =
      (w[i+1]'hi - w[i]'(by omega)).val := by
  induction w generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases xs with
    | nil => simp at hi
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => exact ih i (by simpa using hi)

/-- The cyclic successor gaps are precisely the consecutive gaps after
appending one repeated initial vertex. This pays the final edge as well. -/
theorem pathGaps_close {n : ℕ} (a : ZMod n) (xs : List (ZMod n)) :
    pathGaps ((a::xs) ++ [a]) =
      List.ofFn (fun i : Fin (a::xs).length =>
        ((a::xs)[(finRotate (a::xs).length i).val] - (a::xs)[i.val]).val) := by
  let v := a::xs
  change pathGaps (v++[a]) = List.ofFn (fun i : Fin v.length =>
    (v[(finRotate v.length i).val] - v[i.val]).val)
  apply List.ext_getElem
  · simp [pathGaps_length,v]
  · intro i hi hi'
    have hiv : i < v.length := by simpa only [List.length_ofFn] using hi'
    have hip : i+1 < (v++[a]).length := by
      rw [List.length_append,List.length_singleton]
      omega
    rw [pathGaps_getElem _ _ hip,List.getElem_ofFn]
    rw [List.getElem_append_left hiv]
    have : NeZero v.length := ⟨by simp [v]⟩
    have hval : (finRotate v.length (⟨i,hiv⟩ : Fin v.length)).val =
        (i+1) % v.length := by simp [finRotate_apply,Fin.add_def]
    simp only [hval]
    by_cases hs : i+1 < v.length
    · simp only [Nat.mod_eq_of_lt hs,List.getElem_append_left hs]
    · have he : i+1 = v.length := by omega
      simp only [he,Nat.mod_self]
      rw [List.getElem_append_right (Nat.le_refl v.length)]
      simp only [Nat.sub_self,List.getElem_cons_zero]
      rfl

/-- Two actual simple rainbow paths with opposite endpoints. The second
visits exactly the remaining vertices, keeping both endpoints, and uses
exactly the unused directed differences. No completed cyclic ordering is
an input. -/
structure EndpointSpliceInput (n : ℕ) where
  first : ZMod n
  last : ZMod n
  prefixInterior : List (ZMod n)
  completionInterior : List (ZMod n)
  prefix_simple : ((first::prefixInterior) ++ [last]).Nodup
  prefix_nonzero : ∀ x ∈ (first::prefixInterior) ++ [last], x ≠ 0
  prefix_rainbow : (pathGaps ((first::prefixInterior) ++ [last])).Nodup
  prefix_colors : ∀ d ∈ pathGaps ((first::prefixInterior) ++ [last]), 0 < d ∧ d < n
  completion_simple : ((last::completionInterior) ++ [first]).Nodup
  remaining_vertices : ∀ x, x ∈ (last::completionInterior) ++ [first] ↔
    x ≠ 0 ∧ x ∉ prefixInterior
  completion_rainbow : (pathGaps ((last::completionInterior) ++ [first])).Nodup
  remaining_colors : ∀ d, d ∈ pathGaps ((last::completionInterior) ++ [first]) ↔
    0 < d ∧ d < n ∧ d ∉ pathGaps ((first::prefixInterior) ++ [last])

namespace EndpointSpliceInput

def prefixPath {n : ℕ} (S : EndpointSpliceInput n) : List (ZMod n) :=
  (S.first::S.prefixInterior) ++ [S.last]

def completion {n : ℕ} (S : EndpointSpliceInput n) : List (ZMod n) :=
  (S.last::S.completionInterior) ++ [S.first]

def cycleVertices {n : ℕ} (S : EndpointSpliceInput n) : List (ZMod n) :=
  (S.first::S.prefixInterior) ++ S.last::S.completionInterior

theorem colors_perm {n : ℕ} (S : EndpointSpliceInput n) :
    (pathGaps S.prefixPath ++ pathGaps S.completion).Perm (fullGapList (n-1)) := by
  have hd : List.Disjoint (pathGaps S.prefixPath) (pathGaps S.completion) := by
    intro d hp hc
    exact ((S.remaining_colors d).mp hc).2.2 hp
  apply (List.perm_ext_iff_of_nodup
    (S.prefix_rainbow.append S.completion_rainbow hd) (fullGapList_nodup _)).mpr
  intro d
  rw [List.mem_append,fullGapList_mem]
  constructor
  · rintro (hp | hc)
    · have hh := S.prefix_colors d hp; omega
    · have hh := (S.remaining_colors d).mp hc; omega
  · intro hd
    by_cases hp : d ∈ pathGaps S.prefixPath
    · exact Or.inl hp
    · exact Or.inr ((S.remaining_colors d).mpr ⟨hd.1,by omega,hp⟩)

theorem cycle_nodup {n : ℕ} (S : EndpointSpliceInput n) : S.cycleVertices.Nodup := by
  have hpa : (S.first::S.prefixInterior).Nodup := S.prefix_simple.of_append_left
  have hqa : (S.last::S.completionInterior).Nodup := S.completion_simple.of_append_left
  apply hpa.append hqa
  intro x hp hq
  have hc : x ∈ S.completion := List.mem_append_left _ hq
  have hh := (S.remaining_vertices x).mp hc
  rcases List.mem_cons.mp hp with hx | hx
  · subst x
    exact S.completion_simple.disjoint hq (by simp)
  · exact hh.2 hx

theorem cycle_mem_iff {n : ℕ} (S : EndpointSpliceInput n) (x : ZMod n) :
    x ∈ S.cycleVertices ↔ x ≠ 0 := by
  constructor
  · intro hx
    rcases List.mem_append.mp hx with hp | hq
    · exact S.prefix_nonzero x (List.mem_append_left _ hp)
    · exact ((S.remaining_vertices x).mp (List.mem_append_left _ hq)).1
  · intro hx
    by_cases hp : x ∈ S.prefixInterior
    · exact List.mem_append_left _ (List.mem_cons_of_mem _ hp)
    · have hc := (S.remaining_vertices x).mpr ⟨hx,hp⟩
      rcases List.mem_append.mp hc with hq | he
      · exact List.mem_append_right _ hq
      · have he' : x=S.first := by simpa using he
        subst x
        exact List.mem_append_left _ (by simp)

theorem cycle_length {n : ℕ} (S : EndpointSpliceInput n) :
    S.cycleVertices.length = n-1 := by
  have hh := S.colors_perm.length_eq
  simp only [List.length_append,pathGaps_length,prefixPath,completion,
    List.length_append,List.length_cons,List.length_nil,fullGapList,
    List.length_map,List.length_range] at hh
  simp only [cycleVertices,List.length_append,List.length_cons]
  omega

def vertexEquiv {n : ℕ} (S : EndpointSpliceInput n) :
    Fin (n-1) ≃ {x : ZMod n // x ≠ 0} :=
  (finCongr S.cycle_length.symm).trans
    ((S.cycle_nodup.getEquiv S.cycleVertices).trans (Equiv.subtypeEquivRight S.cycle_mem_iff))

theorem vertexEquiv_val {n : ℕ} (S : EndpointSpliceInput n) (i : Fin (n-1)) :
    (S.vertexEquiv i).val = S.cycleVertices[i.val]'(by rw [S.cycle_length]; exact i.isLt) := rfl

theorem cyclic_gaps {n : ℕ} (S : EndpointSpliceInput n) :
    List.ofFn (fun i : Fin (n-1) =>
      ((S.vertexEquiv (finRotate (n-1) i)).val - (S.vertexEquiv i).val).val) =
        pathGaps S.prefixPath ++ pathGaps S.completion := by
  have hp := pathGaps_append_pivot (S.first::S.prefixInterior)
    (S.completionInterior ++ [S.first]) S.last
  have hc := pathGaps_close S.first (S.prefixInterior ++ S.last::S.completionInterior)
  have he : S.cycleVertices ++ [S.first] =
      (S.first::S.prefixInterior) ++ S.last::(S.completionInterior ++ [S.first]) := by
    simp [cycleVertices,List.append_assoc]
  have hw : pathGaps (S.cycleVertices ++ [S.first]) =
      pathGaps S.prefixPath ++ pathGaps S.completion := by simpa [he,prefixPath,completion] using hp
  rw [← hw]
  change _ = pathGaps ((S.first::(S.prefixInterior ++ S.last::S.completionInterior)) ++ [S.first])
  rw [hc]
  apply List.ext_getElem
  · simp only [List.length_ofFn]
    change n-1 = S.cycleVertices.length
    exact S.cycle_length.symm
  · intro j hj hj'
    have hn : 0 < n-1 := by
      have hh : j < n-1 := by simpa using hj
      omega
    have : NeZero (n-1) := ⟨by omega⟩
    have : NeZero S.cycleVertices.length := ⟨by rw [S.cycle_length]; omega⟩
    simp only [List.getElem_ofFn,vertexEquiv_val]
    apply congrArg ZMod.val
    apply congrArg₂ (fun x y : ZMod n => x-y)
    · change S.cycleVertices.get _ = S.cycleVertices.get _
      apply congrArg S.cycleVertices.get
      apply Fin.ext
      simp only [finRotate_apply,Fin.val_add]
      change (j+(1%(n-1)))%(n-1) =
        (j+(1%S.cycleVertices.length))%S.cycleVertices.length
      exact congrArg (fun k => (j+(1%k))%k) S.cycle_length.symm
    · rfl

/-- An arbitrary actually supplied complementary endpoint path yields the
complete genuine directed rotational terrace. All cyclic adjacencies and
the edge closing back to the initial vertex were paid in `cyclic_gaps`. -/
def directedTerrace {n : ℕ} (S : EndpointSpliceInput n) : DirectedTerrace n where
  vertices := S.vertexEquiv
  rainbow := by rw [S.cyclic_gaps]; exact S.colors_perm

theorem directedTerrace_word {n : ℕ} (S : EndpointSpliceInput n) :
    S.directedTerrace.word = pathGaps S.prefixPath ++ pathGaps S.completion := S.cyclic_gaps

theorem directedTerrace_first {n : ℕ} (S : EndpointSpliceInput n)
    (hn : 0 < n-1) : (S.directedTerrace.vertices ⟨0,hn⟩).val = S.first := rfl

theorem directedTerrace_prefix {n : ℕ} (S : EndpointSpliceInput n) :
    pathGaps S.prefixPath <+: S.directedTerrace.word := by
  rw [S.directedTerrace_word]
  exact List.prefix_append _ _

theorem prefix_vertices_preserved {n : ℕ} (S : EndpointSpliceInput n) :
    S.prefixPath <+: S.cycleVertices := by
  refine ⟨S.completionInterior,?_⟩
  simp [prefixPath,cycleVertices,List.append_assoc]

/-- For an actual connector-prefix prefix, the arbitrary complementary path now supplies
the precise completed calendar needed by the corral construction. -/
def completedConnectorPrefix {n r : ℕ} [NeZero n] [NeZero r]
    (S : EndpointSpliceInput n) (hn : 15 ≤ n) (y : Cell r → ℕ)
    (hfirst : S.first = ((n-3 : ℕ) : ZMod n))
    (hprefix : pathGaps S.prefixPath = [2,3,10,n-14,12] ++ connectorPrefixGaps n y) :
    CompletedTerrace n :=
  completedOfConnectorPrefix S.directedTerrace hn y (pathGaps S.completion)
    (by rw [S.directedTerrace_first (by omega),hfirst])
    (by rw [S.directedTerrace_word,hprefix])

theorem completedConnectorPrefix_body {n r : ℕ} [NeZero n] [NeZero r]
    (S : EndpointSpliceInput n) (hn : 15 ≤ n) (y : Cell r → ℕ)
    (hfirst : S.first = ((n-3 : ℕ) : ZMod n))
    (hprefix : pathGaps S.prefixPath = [2,3,10,n-14,12] ++ connectorPrefixGaps n y) :
    (S.completedConnectorPrefix hn y hfirst hprefix).body = connectorPrefixGaps n y ++ pathGaps S.completion := rfl

def bodyInputOfSplicedConnectorPrefix {n r : ℕ} [NeZero n] [NeZero r]
    (S : EndpointSpliceInput n) (hr : 2 ≤ r) (hlarge : 100*r*r ≤ n)
    (y : Cell r → ℕ) (hy : ∀ i, 30*r*r ≤ y i ∧ y i < 40*r*r)
    (hfirst : S.first = ((n-3 : ℕ) : ZMod n))
    (hprefix : pathGaps S.prefixPath = [2,3,10,n-14,12] ++ connectorPrefixGaps n y) :
    BodyInput (S.completedConnectorPrefix (by nlinarith) y hfirst hprefix) r :=
  bodyInputOfConnectorPrefix _ hr hlarge y hy (pathGaps S.completion) rfl

end EndpointSpliceInput

end CorralFormalization.LatinCompletion.TerraceCompletion
