import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ChainOfFn
import Mathlib.Data.List.Chain
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.Tactic.Common
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Data.ZMod.Basic

/-!
# Finite factor joining with a virtual edge removed

This module is independent of the supplied CorralFormalization modules.
`Segment` stores an actual finite walk; its outgoing body excludes its final
vertex. The factor theorem below assumes local simplicity and disjointness
of those bodies, and a single endpoint cycle. It constructs the resulting
path rather than taking that path as a premise. No probabilistic statement
or endpoint-completion hypothesis is assumed or proved.
-/

namespace EndpointFactor

universe u v w z

variable {V : Type u} {C : Type v} {K : Type w}

/-- Consecutive directed edge labels; there is no closing edge. -/
def edgeLabels (edge : V → V → C) : List V → List C
  | [] => []
  | [_] => []
  | a :: b :: rest => edge a b :: edgeLabels edge (b :: rest)

theorem edgeLabels_length (edge : V → V → C) (l : List V) :
    (edgeLabels edge l).length = l.length - 1 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    cases l with
    | nil => rfl
    | cons b l => simpa [edgeLabels] using ih

theorem edgeLabels_append_pivot (edge : V → V → C)
    (xs ys : List V) (a : V) :
    edgeLabels edge (xs ++ a :: ys) =
      edgeLabels edge (xs ++ [a]) ++ edgeLabels edge (a :: ys) := by
  induction xs with
  | nil => simp [edgeLabels]
  | cons x xs ih =>
    cases xs with
    | nil => simp [edgeLabels]
    | cons y xs => simpa [edgeLabels] using congrArg (List.cons (edge x y)) ih

theorem edgeLabels_map {D : Type z} (edge : V → V → C) (f : C → D) (l : List V) :
    edgeLabels (fun a b => f (edge a b)) l = (edgeLabels edge l).map f := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest => simpa [edgeLabels] using congrArg (List.cons (f (edge a b))) ih

/-- A nonempty-edge directed walk, with no simplicity or rainbow claim built in. -/
structure Segment (V : Type u) where
  first : V
  interior : List V
  last : V

namespace Segment

def body (P : Segment V) : List V := P.first :: P.interior

def vertices (P : Segment V) : List V := P.body ++ [P.last]

def colors (P : Segment V) (edge : V → V → C) : List C :=
  edgeLabels edge P.vertices

@[simp] theorem body_ne_nil (P : Segment V) : P.body ≠ [] := by simp [body]

@[simp] theorem colors_length (P : Segment V) (edge : V → V → C) :
    (P.colors edge).length = P.body.length := by
  simp [colors, vertices, edgeLabels_length]

end Segment

/-- The initial vertex of the remaining sequence, or its terminal vertex. -/
def anchor (P : K → Segment V) : List K → V → V
  | [], terminal => terminal
  | i :: _, _ => (P i).first

/-- All local endpoint matches, before any walk is expanded. -/
def Connects (P : K → Segment V) : List K → V → Prop
  | [], _ => True
  | i :: rest, terminal =>
      (P i).last = anchor P rest terminal ∧ Connects P rest terminal

/-- Expand outgoing bodies and retain the last vertex once. -/
def expand (P : K → Segment V) (order : List K) (terminal : V) : List V :=
  order.flatMap (fun i => (P i).body) ++ [terminal]

@[simp] theorem expand_nil (P : K → Segment V) (terminal : V) :
    expand P [] terminal = [terminal] := rfl

@[simp] theorem expand_cons (P : K → Segment V) (i : K)
    (rest : List K) (terminal : V) :
    expand P (i :: rest) terminal = (P i).body ++ expand P rest terminal := by
  simp [expand, List.append_assoc]

theorem expand_head (P : K → Segment V) (order : List K) (terminal : V) :
    (expand P order terminal).head? = some (anchor P order terminal) := by
  cases order <;> simp [expand, anchor, Segment.body]

@[simp] theorem expand_last (P : K → Segment V) (order : List K) (terminal : V) :
    (expand P order terminal).getLast? = some terminal := by
  simp [expand]

theorem expand_mem (P : K → Segment V) (order : List K) (terminal v : V) :
    v ∈ expand P order terminal ↔
      (∃ i ∈ order, v ∈ (P i).body) ∨ v = terminal := by
  simp [expand]

theorem expand_labels (edge : V → V → C) (P : K → Segment V)
    (order : List K) (terminal : V) (hc : Connects P order terminal) :
    edgeLabels edge (expand P order terminal) =
      order.flatMap (fun i => (P i).colors edge) := by
  induction order with
  | nil => simp [expand, edgeLabels]
  | cons i rest ih =>
    rcases hc with ⟨hi, hr⟩
    have hh := expand_head P rest terminal
    cases he : expand P rest terminal with
    | nil => simp [he] at hh
    | cons a tail =>
      have ha : a = (P i).last := by simpa [he, hi] using hh
      subst a
      rw [expand_cons, he, edgeLabels_append_pivot]
      simp only [← he, Segment.colors, Segment.vertices, List.flatMap_cons]
      rw [ih hr]
      rfl

/-- Local body conditions imply global vertex uniqueness after expansion. -/
theorem expand_nodup (P : K → Segment V) (order : List K) (terminal : V)
    (ho : order.Nodup)
    (hs : ∀ i ∈ order, (P i).body.Nodup)
    (hd : ∀ i ∈ order, ∀ j ∈ order, i ≠ j →
      List.Disjoint (P i).body (P j).body)
    (ht : ∀ i ∈ order, terminal ∉ (P i).body) :
    (expand P order terminal).Nodup := by
  have hb : (order.flatMap (fun i => (P i).body)).Nodup := by
    apply List.nodup_flatMap.mpr
    refine ⟨hs, ?_⟩
    apply ho.imp_of_mem
    intro i j hi hj hij
    exact hd i hi j hj hij
  apply hb.append (by simp)
  intro v hv hv'
  have hvt : v = terminal := by simpa using hv'
  subst v
  rcases List.mem_flatMap.mp hv with ⟨i, hi, hv⟩
  exact ht i hi hv

theorem expand_rainbow (edge : V → V → C) (P : K → Segment V)
    (order : List K) (terminal : V) (hc : Connects P order terminal)
    (ho : order.Nodup)
    (hs : ∀ i ∈ order, ((P i).colors edge).Nodup)
    (hd : ∀ i ∈ order, ∀ j ∈ order, i ≠ j →
      List.Disjoint ((P i).colors edge) ((P j).colors edge)) :
    (edgeLabels edge (expand P order terminal)).Nodup := by
  rw [expand_labels edge P order terminal hc]
  apply List.nodup_flatMap.mpr
  refine ⟨hs, ?_⟩
  apply ho.imp_of_mem
  intro i j hi hj hij
  exact hd i hi j hj hij


/-! ## A complete endpoint-cycle order, including the singleton case -/

variable {I : Type w} {J : Type z}


/-! ## Adjoining the exceptional virtual arrow -/

/-- Extend the real reverse-factor endpoint bijection by exactly the
exceptional arrow `y → x`. This is a bijection construction, not a path
existence premise. -/
noncomputable def extendPuncturedEquiv (x : I) (y : J)
    (b0 : {j : J // j ≠ y} ≃ {i : I // i ≠ x}) : J ≃ I := by
  classical
  exact
    { toFun := fun j => if hj : j = y then x else (b0 ⟨j, hj⟩).val
      invFun := fun i => if hi : i = x then y else (b0.symm ⟨i, hi⟩).val
      left_inv := by
        intro j
        by_cases hj : j = y
        · subst j
          simp
        · simp only [dif_neg hj, dif_neg (b0 ⟨j, hj⟩).property]
          exact congrArg Subtype.val (b0.symm_apply_apply ⟨j, hj⟩)
      right_inv := by
        intro i
        by_cases hi : i = x
        · subst i
          simp
        · simp only [dif_neg hi, dif_neg (b0.symm ⟨i, hi⟩).property]
          exact congrArg Subtype.val (b0.apply_symm_apply ⟨i, hi⟩) }

@[simp] theorem extendPuncturedEquiv_exceptional (x : I) (y : J)
    (b0 : {j : J // j ≠ y} ≃ {i : I // i ≠ x}) :
    extendPuncturedEquiv x y b0 y = x := by
  simp [extendPuncturedEquiv]

theorem extendPuncturedEquiv_real (x : I) (y : J)
    (b0 : {j : J // j ≠ y} ≃ {i : I // i ≠ x}) (j : J) (hj : j ≠ y) :
    extendPuncturedEquiv x y b0 j = (b0 ⟨j, hj⟩).val := by
  simp [extendPuncturedEquiv, hj]

/-- A finite cyclic enumeration of endpoints, not a path on the expanded
vertices. The single-cycle assumption is confined to the endpoint map. -/
structure CycleOrder (ρ : Equiv.Perm I) (root : I) where
  order : List I
  nonempty : order ≠ []
  nodup : order.Nodup
  covers : ∀ i, i ∈ order
  first : order.head? = some root
  follows : order.IsChain (fun i j => ρ i = j)
  closes : ∀ i, order.getLast? = some i → ρ i = root

def orbit [Fintype I] (ρ : Equiv.Perm I) (root : I)
    (i : Fin (Fintype.card I)) : I := (ρ ^ i.val) root

theorem orbit_bijective [Fintype I] (ρ : Equiv.Perm I) (root : I)
    (hc : ρ.IsCycleOn Set.univ) : Function.Bijective (orbit ρ root) := by
  classical
  have hc' : ρ.IsCycleOn (Finset.univ : Finset I) := by simpa using hc
  constructor
  · intro i j hij
    have he : i.val ≡ j.val [MOD Fintype.card I] := by
      simpa [orbit] using
        (hc'.pow_apply_eq_pow_apply (a := root) (by simp)).mp hij
    exact Fin.ext (he.eq_of_lt_of_lt i.isLt j.isLt)
  · intro y
    obtain ⟨n, hn, he⟩ := hc'.exists_pow_eq (a := root) (b := y) (by simp) (by simp)
    exact ⟨⟨n, by simpa using hn⟩, he⟩

/-- Standard Mathlib `IsCycleOn univ` supplies the complete finite endpoint
order. It covers a one-point endpoint set, unlike `Perm.IsCycle`. -/
noncomputable def cycleOrderOfIsCycleOn [Fintype I]
    (ρ : Equiv.Perm I) (root : I) (hc : ρ.IsCycleOn Set.univ) :
    CycleOrder ρ root := by
  classical
  have hpos : 0 < Fintype.card I := Fintype.card_pos_iff.mpr ⟨root⟩
  have hne : List.ofFn (orbit ρ root) ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hh
    omega
  have hc' : ρ.IsCycleOn (Finset.univ : Finset I) := by simpa using hc
  refine
    { order := List.ofFn (orbit ρ root)
      nonempty := hne
      nodup := List.nodup_ofFn.mpr (orbit_bijective ρ root hc).1
      covers := ?_
      first := ?_
      follows := ?_
      closes := ?_ }
  · intro i
    exact List.mem_ofFn.mpr ((orbit_bijective ρ root hc).2 i)
  · rw [List.head?_eq_some_head hne, List.head_ofFn]
    simp [orbit]
  · apply List.isChain_ofFn.mpr
    intro i hi
    simp [orbit, pow_succ', Equiv.Perm.mul_apply]
  · intro i hi
    rw [List.getLast?_eq_some_getLast hne, List.getLast_ofFn] at hi
    have he : orbit ρ root ⟨Fintype.card I - 1, by omega⟩ = i := Option.some.inj hi
    rw [← he]
    change ρ ((ρ ^ (Fintype.card I - 1)) root) = root
    rw [← Equiv.Perm.mul_apply, ← pow_succ']
    have hk : Fintype.card I - 1 + 1 = Fintype.card I := by omega
    rw [hk]
    simpa using hc'.pow_card_apply (a := root) (by simp)

/-! ## Alternating the two factors and omitting the virtual reverse segment -/

/-- The final reverse segment is omitted. Its index is later proved to be
exactly the exceptional endpoint of the virtual arrow. -/
def alternate (f : I → J) : List I → List (Sum I J)
  | [] => []
  | [i] => [Sum.inl i]
  | i :: j :: rest => Sum.inl i :: Sum.inr (f i) :: alternate f (j :: rest)

@[simp] theorem alternate_nil (f : I → J) : alternate f [] = [] := rfl

@[simp] theorem alternate_singleton (f : I → J) (i : I) :
    alternate f [i] = [Sum.inl i] := rfl

@[simp] theorem mem_alternate_inl (f : I → J) (l : List I) (i : I) :
    Sum.inl i ∈ alternate f l ↔ i ∈ l := by
  induction l using List.twoStepInduction with
  | nil => simp [alternate]
  | singleton a => simp [alternate]
  | cons_cons a b rest _ ih => simp [alternate, ih]

@[simp] theorem mem_alternate_inr (f : I → J) (l : List I) (j : J) :
    Sum.inr j ∈ alternate f l ↔ ∃ i ∈ l.dropLast, f i = j := by
  induction l using List.twoStepInduction with
  | nil => simp [alternate]
  | singleton a => simp [alternate]
  | cons_cons a b rest _ ih =>
    simp [alternate, ih, List.dropLast_cons_cons, eq_comm]

/-- Injectivity of the forward endpoint map ensures each factor is expanded
at most once. -/
theorem alternate_nodup (f : I → J) (hf : Function.Injective f)
    (l : List I) (hl : l.Nodup) : (alternate f l).Nodup := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b rest _ ih =>
    have hab : a ∉ b :: rest := hl.notMem
    have hbr : (b :: rest).Nodup := hl.of_cons
    have hnot : Sum.inr (f a) ∉ alternate f (b :: rest) := by
      intro hm
      obtain ⟨i, hi, hfi⟩ := (mem_alternate_inr f (b :: rest) (f a)).mp hm
      have hia : i = a := hf hfi
      subst i
      exact hab (List.mem_of_mem_dropLast hi)
    simp only [alternate, List.nodup_cons]
    refine ⟨?_, hnot, ih b hbr⟩
    simp [hab]

/-- The outgoing body of every real factor participates exactly once; the
reverse factor at `exceptional` never participates. -/
theorem alternate_inventory (f : I ≃ J) (b : J ≃ I) (exceptional : J)
    (cyc : CycleOrder (f.trans b) (b exceptional)) (k : Sum I J) :
    k ∈ alternate f cyc.order ↔ k ≠ Sum.inr exceptional := by
  classical
  have hlast : f (cyc.order.getLast cyc.nonempty) = exceptional := by
    apply b.injective
    exact cyc.closes _ (List.getLast?_eq_some_getLast cyc.nonempty)
  have hs : cyc.order.dropLast ++ [cyc.order.getLast cyc.nonempty] = cyc.order :=
    List.dropLast_concat_getLast cyc.nonempty
  have hdrop : ∀ i, i ∈ cyc.order.dropLast ↔ f i ≠ exceptional := by
    intro i
    constructor
    · intro hi he
      have hie : i = cyc.order.getLast cyc.nonempty := f.injective (he.trans hlast.symm)
      subst i
      have hn : (cyc.order.dropLast ++ [cyc.order.getLast cyc.nonempty]).Nodup :=
        hs.symm ▸ cyc.nodup
      exact hn.disjoint hi (by simp)
    · intro hi
      have hm := cyc.covers i
      rw [← hs, List.mem_append, List.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hm
      · exact False.elim (hi (hm ▸ hlast))
  cases k with
  | inl i => simp [cyc.covers i]
  | inr j =>
    rw [mem_alternate_inr]
    constructor
    · rintro ⟨i, hi, rfl⟩
      simpa using (hdrop i).mp hi
    · intro hj
      refine ⟨f.symm j, (hdrop _).mpr ?_, f.apply_symm_apply j⟩
      simpa using hj

/-- Select either an actual forward or an actual reverse path. The omitted
reverse index is deliberately unconstrained and never receives a colour. -/
def factorPiece (F : I → Segment V) (R : J → Segment V) : Sum I J → Segment V :=
  Sum.elim F R

@[simp] theorem factorPiece_inl (F : I → Segment V) (R : J → Segment V) (i : I) :
    factorPiece F R (Sum.inl i) = F i := rfl

@[simp] theorem factorPiece_inr (F : I → Segment V) (R : J → Segment V) (j : J) :
    factorPiece F R (Sum.inr j) = R j := rfl

theorem anchor_alternate_cons (F : I → Segment V) (R : J → Segment V)
    (f : I → J) (i : I) (rest : List I) (terminal : V) :
    anchor (factorPiece F R) (alternate f (i :: rest)) terminal = (F i).first := by
  cases rest <;> rfl

/-- Endpoint equalities alone provide the chain that the expansion lemma
needs. No spanning path is a premise. -/
theorem alternate_connects (F : I → Segment V) (R : J → Segment V)
    (f : I ≃ J) (b : J ≃ I) (s : I → V) (e : J → V)
    (exceptional : J)
    (hFfirst : ∀ i, (F i).first = s i)
    (hFlast : ∀ i, (F i).last = e (f i))
    (hRfirst : ∀ j, (R j).first = e j)
    (hRlast : ∀ j, j ≠ exceptional → (R j).last = s (b j))
    (l : List I)
    (hc : l.IsChain (fun i j => b (f i) = j))
    (hlast : ∀ i, l.getLast? = some i → f i = exceptional)
    (hex : ∀ i ∈ l.dropLast, f i ≠ exceptional) :
    Connects (factorPiece F R) (alternate f l) (e exceptional) := by
  induction l using List.twoStepInduction with
  | nil => trivial
  | singleton i =>
    have he := hlast i (by simp)
    simp [alternate, Connects, anchor, hFlast, he]
  | cons_cons i j rest _ ih =>
    have hstep : b (f i) = j := (List.isChain_cons_cons.mp hc).1
    have htail := (List.isChain_cons_cons.mp hc).2
    have hi : f i ≠ exceptional := hex i (by simp)
    have hlast' : ∀ k, (j :: rest).getLast? = some k → f k = exceptional := by
      intro k hk
      exact hlast k (by simpa using hk)
    have hex' : ∀ k ∈ (j :: rest).dropLast, f k ≠ exceptional := by
      intro k hk
      exact hex k (by simpa using Or.inr hk)
    have hrec := ih j htail hlast' hex'
    change (F i).last = (R (f i)).first ∧
      (R (f i)).last = anchor (factorPiece F R) (alternate f (j :: rest)) (e exceptional) ∧
      Connects (factorPiece F R) (alternate f (j :: rest)) (e exceptional)
    rw [anchor_alternate_cons, hFlast, hRfirst, hRlast _ hi, hstep, hFfirst]
    exact ⟨rfl, rfl, hrec⟩



theorem alternate_length (f : I → J) (l : List I) :
    (alternate f l).length = 2 * l.length - 1 := by
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton a => simp
  | cons_cons a b rest _ ih =>
    have h := ih b
    simp only [alternate, List.length_cons] at *
    omega

theorem CycleOrder.length_eq_card [Fintype I] (ρ : Equiv.Perm I) (root : I)
    (cyc : CycleOrder ρ root) : cyc.order.length = Fintype.card I := by
  classical
  have he : cyc.order.toFinset = Finset.univ := by
    ext i
    simp [cyc.covers i]
  rw [← List.toFinset_card_of_nodup cyc.nodup, he, Finset.card_univ]

theorem flatMap_length_fixed (P : K → Segment V) (l : List K) (t : ℕ)
    (ht : ∀ i ∈ l, (P i).body.length = t) :
    (l.flatMap (fun i => (P i).body)).length = t * l.length := by
  induction l with
  | nil => simp
  | cons i rest ih =>
    have hi := ht i (by simp)
    have hr : ∀ k ∈ rest, (P k).body.length = t := by
      intro k hk
      exact ht k (by simp [hk])
    simp [hi, ih hr, Nat.mul_succ, Nat.add_comm]

/-- Recover the usual `x :: middle ++ [y]` presentation from distinct
endpoints, without imposing it as a premise on the constructed path. -/
theorem list_eq_endpoints (l : List V) (x y : V)
    (hhead : l.head? = some x) (hlast : l.getLast? = some y) (hne : x ≠ y) :
    ∃ middle : List V, l = (x :: middle) ++ [y] := by
  cases l with
  | nil => simp at hhead
  | cons a rest =>
    have ha : a = x := by simpa using hhead
    subst a
    cases rest with
    | nil => simp at hlast; exact False.elim (hne hlast)
    | cons b tail =>
      have hr : (b :: tail).getLast? = some y := by simpa using hlast
      obtain ⟨middle, hm⟩ := List.getLast?_eq_some_iff.mp hr
      exact ⟨middle, by simp [hm]⟩

/-! ## The finite factor interface and the complete joining theorem -/

/-- Two directed factor families and their contracted endpoint cycle.

`reverse exceptional` is a dummy entry: none of its vertices, edges or
colours is used. All disjointness/rainbow conditions range over real keys
only. A forward body's final E endpoint is stored in the next reverse
body; a reverse body's final S endpoint is stored in the next forward
body. The sole terminal E endpoint is retained separately.
-/
structure FactorSystem (edge : V → V → C) (I : Type w) (J : Type z) where
  forwardMap : I ≃ J
  externalMap : J ≃ I
  exceptional : J
  start : I → V
  finish : J → V
  forward : I → Segment V
  reverse : J → Segment V
  forward_first : ∀ i, (forward i).first = start i
  forward_last : ∀ i, (forward i).last = finish (forwardMap i)
  reverse_first : ∀ j, (reverse j).first = finish j
  reverse_last : ∀ j, j ≠ exceptional → (reverse j).last = start (externalMap j)
  endpoint_cycle : Equiv.Perm.IsCycleOn (forwardMap.trans externalMap) Set.univ
  body_simple : ∀ k : Sum I J, k ≠ Sum.inr exceptional →
    (factorPiece forward reverse k).body.Nodup
  body_disjoint : ∀ k l : Sum I J,
    k ≠ Sum.inr exceptional → l ≠ Sum.inr exceptional → k ≠ l →
    List.Disjoint (factorPiece forward reverse k).body
      (factorPiece forward reverse l).body
  terminal_fresh : ∀ k : Sum I J, k ≠ Sum.inr exceptional →
    finish exceptional ∉ (factorPiece forward reverse k).body
  color_simple : ∀ k : Sum I J, k ≠ Sum.inr exceptional →
    ((factorPiece forward reverse k).colors edge).Nodup
  color_disjoint : ∀ k l : Sum I J,
    k ≠ Sum.inr exceptional → l ≠ Sum.inr exceptional → k ≠ l →
    List.Disjoint ((factorPiece forward reverse k).colors edge)
      ((factorPiece forward reverse l).colors edge)

namespace FactorSystem

variable (edge : V → V → C) [Fintype I]
variable (F : FactorSystem edge I J)

abbrev initial : V := F.start (F.externalMap F.exceptional)
abbrev terminal : V := F.finish F.exceptional
abbrev piece : Sum I J → Segment V := factorPiece F.forward F.reverse

noncomputable def endpointOrder :
    CycleOrder (F.forwardMap.trans F.externalMap) (F.externalMap F.exceptional) :=
  cycleOrderOfIsCycleOn _ _ F.endpoint_cycle

noncomputable def keys : List (Sum I J) :=
  alternate F.forwardMap (F.endpointOrder edge).order

/-- Explicit, constructed vertex sequence after deleting the virtual edge. -/
noncomputable def path : List V := expand F.piece (F.keys edge) F.terminal

/-- Exactly the factor vertices; the exceptional terminal appears once. -/
def vertexInventory (v : V) : Prop :=
  v = F.terminal ∨ ∃ k : Sum I J,
    k ≠ Sum.inr F.exceptional ∧ v ∈ (F.piece edge k).body

/-- Exactly the colours of actual forward and reverse factors. There is no
virtual-arrow colour in this inventory. -/
def colorInventory (c : C) : Prop :=
  ∃ k : Sum I J, k ≠ Sum.inr F.exceptional ∧ c ∈ (F.piece edge k).colors edge

omit [Fintype I] in
theorem vertexInventory_iff (v : V) : F.vertexInventory edge v ↔
    v = F.terminal ∨ (∃ i, v ∈ (F.forward i).body) ∨
      (∃ j, j ≠ F.exceptional ∧ v ∈ (F.reverse j).body) := by
  simp [vertexInventory, piece, factorPiece, Sum.exists]

omit [Fintype I] in
theorem colorInventory_iff (c : C) : F.colorInventory edge c ↔
    (∃ i, c ∈ (F.forward i).colors edge) ∨
      (∃ j, j ≠ F.exceptional ∧ c ∈ (F.reverse j).colors edge) := by
  simp [colorInventory, piece, factorPiece, Sum.exists]

@[simp] theorem mem_keys (k : Sum I J) :
    k ∈ F.keys edge ↔ k ≠ Sum.inr F.exceptional :=
  alternate_inventory _ _ _ _ k

theorem keys_nodup : (F.keys edge).Nodup :=
  alternate_nodup _ F.forwardMap.injective _ (F.endpointOrder edge).nodup

theorem keys_connect : Connects F.piece (F.keys edge) F.terminal := by
  apply alternate_connects F.forward F.reverse F.forwardMap F.externalMap
    F.start F.finish F.exceptional F.forward_first F.forward_last
    F.reverse_first F.reverse_last
  · exact (F.endpointOrder edge).follows
  · intro i hi
    exact F.externalMap.injective ((F.endpointOrder edge).closes i hi)
  · intro i hi he
    have hm : Sum.inr F.exceptional ∈ F.keys edge := by
      apply (mem_alternate_inr _ _ _).mpr
      exact ⟨i, hi, he⟩
    exact (F.mem_keys edge _).mp hm rfl

theorem path_head : (F.path edge).head? = some F.initial := by
  rw [path, expand_head]
  have hf := (F.endpointOrder edge).first
  cases he : (F.endpointOrder edge).order with
  | nil => simp [he] at hf
  | cons i rest =>
    have hi : i = F.externalMap F.exceptional := by simpa [he] using hf
    subst i
    simpa [keys, he, F.forward_first] using
      anchor_alternate_cons F.forward F.reverse F.forwardMap
        (F.externalMap F.exceptional) rest F.terminal

@[simp] theorem path_last : (F.path edge).getLast? = some F.terminal :=
  expand_last _ _ _

theorem path_simple : (F.path edge).Nodup := by
  apply expand_nodup F.piece (F.keys edge) F.terminal (F.keys_nodup edge)
  · intro i hi
    exact F.body_simple i ((F.mem_keys edge i).mp hi)
  · intro i hi j hj hij
    exact F.body_disjoint i j ((F.mem_keys edge i).mp hi)
      ((F.mem_keys edge j).mp hj) hij
  · intro i hi
    exact F.terminal_fresh i ((F.mem_keys edge i).mp hi)

/-- Ordered edge list equality, stronger than a set equality. -/
theorem path_labels : edgeLabels edge (F.path edge) =
    (F.keys edge).flatMap (fun k => (F.piece edge k).colors edge) :=
  expand_labels edge _ _ _ (F.keys_connect edge)

theorem path_rainbow : (edgeLabels edge (F.path edge)).Nodup := by
  apply expand_rainbow edge F.piece (F.keys edge) F.terminal
    (F.keys_connect edge) (F.keys_nodup edge)
  · intro i hi
    exact F.color_simple i ((F.mem_keys edge i).mp hi)
  · intro i hi j hj hij
    exact F.color_disjoint i j ((F.mem_keys edge i).mp hi)
      ((F.mem_keys edge j).mp hj) hij

theorem path_vertex_inventory (v : V) :
    v ∈ F.path edge ↔ F.vertexInventory edge v := by
  simp only [path, expand_mem, F.mem_keys edge, vertexInventory]
  exact or_comm

theorem path_color_inventory (c : C) :
    c ∈ edgeLabels edge (F.path edge) ↔ F.colorInventory edge c := by
  rw [F.path_labels edge]
  simp only [List.mem_flatMap, F.mem_keys edge, colorInventory]

/-- Closing the constructed path adds exactly the virtual arrow's one
label. This label is not required to differ from any real label. -/
theorem close_adds_only_virtual :
    edgeLabels edge (F.path edge ++ [F.initial]) =
      edgeLabels edge (F.path edge) ++ [edge F.terminal F.initial] := by
  change edgeLabels edge
      (((F.keys edge).flatMap (fun k => (F.piece edge k).body) ++ [F.terminal]) ++ [F.initial]) = _
  rw [List.append_assoc]
  exact edgeLabels_append_pivot edge _ [F.initial] F.terminal


/-- Exact ordered directed-edge coverage, independent of the choice of
colour function. In particular, expansion cannot create a detached cycle. -/
theorem path_edges : edgeLabels (fun a b : V => (a, b)) (F.path edge) =
    (F.keys edge).flatMap
      (fun k => (F.piece edge k).colors (fun a b : V => (a, b))) :=
  expand_labels _ _ _ _ (F.keys_connect edge)

omit [Fintype I] in
theorem endpoints_ne : F.initial ≠ F.terminal := by
  intro he
  apply F.terminal_fresh (Sum.inl (F.externalMap F.exceptional)) (by simp)
  change F.terminal ∈ (F.forward (F.externalMap F.exceptional)).body
  rw [Segment.body, F.forward_first]
  simp [← he]

theorem path_middle : ∃ middle : List V,
    F.path edge = (F.initial :: middle) ++ [F.terminal] :=
  list_eq_endpoints _ _ _ (F.path_head edge) (F.path_last edge) (F.endpoints_ne edge)

/-- Exact paper edge budget when each real factor has length `t`.
There are `|I|` forward and `|I|-1` real reverse paths. -/
theorem path_length_fixed (t : ℕ)
    (ht : ∀ k : Sum I J, k ≠ Sum.inr F.exceptional →
      (F.piece edge k).body.length = t) :
    (F.path edge).length =
      t * Fintype.card I + t * (Fintype.card I - 1) + 1 := by
  have hpos : 0 < Fintype.card I :=
    Fintype.card_pos_iff.mpr ⟨F.externalMap F.exceptional⟩
  have hk : (F.keys edge).length = 2 * Fintype.card I - 1 := by
    rw [keys, alternate_length, (F.endpointOrder edge).length_eq_card]
  have ht' : ∀ k ∈ F.keys edge, (F.piece edge k).body.length = t := by
    intro k h
    exact ht k ((F.mem_keys edge k).mp h)
  change ((F.keys edge).flatMap (fun k => (F.piece edge k).body) ++ [F.terminal]).length = _
  rw [List.length_append, List.length_singleton,
    flatMap_length_fixed _ _ t ht', hk]
  have hm : 2 * Fintype.card I - 1 = Fintype.card I + (Fintype.card I - 1) := by omega
  rw [hm, Nat.mul_add]

theorem real_edge_count_fixed (t : ℕ)
    (ht : ∀ k : Sum I J, k ≠ Sum.inr F.exceptional →
      (F.piece edge k).body.length = t) :
    (edgeLabels edge (F.path edge)).length =
      t * Fintype.card I + t * (Fintype.card I - 1) := by
  rw [edgeLabels_length, F.path_length_fixed edge t ht]
  omega

/-- The deterministic conclusion after joining the segments. It uses the
endpoint cycle and the actual factor lists, and constructs every vertex
and every real directed label exactly once. -/
theorem joinFactors : ∃ vertices : List V,
    vertices.head? = some F.initial ∧
    vertices.getLast? = some F.terminal ∧
    vertices.Nodup ∧
    (∀ v, v ∈ vertices ↔ F.vertexInventory edge v) ∧
    (edgeLabels edge vertices).Nodup ∧
    (∀ c, c ∈ edgeLabels edge vertices ↔ F.colorInventory edge c) ∧
    edgeLabels edge (vertices ++ [F.initial]) =
      edgeLabels edge vertices ++ [edge F.terminal F.initial] := by
  exact ⟨F.path edge, F.path_head edge, F.path_last edge,
    F.path_simple edge, F.path_vertex_inventory edge,
    F.path_rainbow edge, F.path_color_inventory edge,
    F.close_adds_only_virtual edge⟩

end FactorSystem

/-! ## Optional short initial path -/

/-- Prepend an actual short path whose final vertex is the first vertex of
an existing path. The common endpoint is counted once; all edge labels are
paid. -/
theorem prepend_exact (edge : V → V → C) (P : Segment V)
    (tail : List V) (hhead : tail.head? = some P.last)
    (hP : P.body.Nodup) (htail : tail.Nodup)
    (hdis : List.Disjoint P.body tail)
    (hPrainbow : (P.colors edge).Nodup)
    (htrainbow : (edgeLabels edge tail).Nodup)
    (hcdis : List.Disjoint (P.colors edge) (edgeLabels edge tail)) :
    (P.body ++ tail).Nodup ∧
    edgeLabels edge (P.body ++ tail) = P.colors edge ++ edgeLabels edge tail ∧
    (edgeLabels edge (P.body ++ tail)).Nodup ∧
    (P.body ++ tail).head? = some P.first ∧
    (P.body ++ tail).getLast? = tail.getLast? ∧
    (∀ v, v ∈ P.body ++ tail ↔ v ∈ P.body ∨ v ∈ tail) := by
  have he : edgeLabels edge (P.body ++ tail) =
      P.colors edge ++ edgeLabels edge tail := by
    cases hh : tail with
    | nil => simp [hh] at hhead
    | cons a rest =>
      have ha : a = P.last := by simpa [hh] using hhead
      subst a
      exact edgeLabels_append_pivot edge _ _ _
  refine ⟨hP.append htail hdis, he, ?_, ?_, ?_, ?_⟩
  · rw [he]
    exact hPrainbow.append htrainbow hcdis
  · simp [Segment.body]
  · have hn : tail ≠ [] := by intro hn; simp [hn] at hhead
    rw [List.getLast?_append, List.getLast?_eq_some_getLast hn]
    rfl
  · intro v
    exact List.mem_append


/-! ## Directed group differences -/

variable {G : Type u}

/-- Simplicity of a path makes every actual directed difference nonzero.
The closing virtual arrow does not participate in this statement. -/
theorem difference_labels_nonzero [AddGroup G] (l : List G) (hl : l.Nodup) :
    ∀ d ∈ edgeLabels (fun a b : G => b - a) l, d ≠ 0 := by
  induction l with
  | nil => simp [edgeLabels]
  | cons a rest ih =>
    cases rest with
    | nil => simp [edgeLabels]
    | cons b rest =>
      intro d hd
      simp only [edgeLabels, List.mem_cons] at hd
      rcases hd with rfl | hd
      · apply sub_ne_zero.mpr
        intro h
        exact hl.notMem (by simp [h])
      · exact ih hl.of_cons d hd

/-- Ordered directed differences telescope in an additive commutative group. -/
theorem difference_labels_sum [AddCommGroup G] (x y : G) (middle : List G) :
    (edgeLabels (fun a b : G => b - a) ((x :: middle) ++ [y])).sum = y - x := by
  induction middle generalizing x with
  | nil => simp [edgeLabels]
  | cons a rest ih =>
    simp only [List.cons_append, edgeLabels, List.sum_cons]
    have hh := ih a
    simp only [List.cons_append] at hh
    rw [hh]
    abel

namespace FactorSystem

variable [Fintype I] [AddCommGroup G]
variable (F : FactorSystem (fun a b : G => b - a) I J)

/-- Specialization to the actual directed group differences for the path factor. -/
theorem path_difference_nonzero :
    ∀ d ∈ edgeLabels (fun a b : G => b - a) F.path, d ≠ 0 :=
  difference_labels_nonzero _ F.path_simple

theorem path_difference_sum :
    (edgeLabels (fun a b : G => b - a) F.path).sum = F.terminal - F.initial := by
  obtain ⟨middle, hm⟩ := F.path_middle
  rw [hm]
  exact difference_labels_sum _ _ _

/-- A finite target inventory is visited with precisely the required
endpoints and directed differences. This is a finite instance only. -/
theorem joinFactors_on_targets (W D : Set G)
    (hW : ∀ v, F.vertexInventory (fun a b : G => b - a) v ↔ v ∈ W)
    (hD : ∀ d, F.colorInventory (fun a b : G => b - a) d ↔ d ∈ D) :
    ∃ middle : List G,
      ((F.initial :: middle) ++ [F.terminal]).Nodup ∧
      (∀ v, v ∈ (F.initial :: middle) ++ [F.terminal] ↔ v ∈ W) ∧
      (edgeLabels (fun a b : G => b - a)
        ((F.initial :: middle) ++ [F.terminal])).Nodup ∧
      (∀ d, d ∈ edgeLabels (fun a b : G => b - a)
        ((F.initial :: middle) ++ [F.terminal]) ↔ d ∈ D) ∧
      (∀ d ∈ D, d ≠ 0) ∧
      (edgeLabels (fun a b : G => b - a)
        ((F.initial :: middle) ++ [F.terminal])).sum = F.terminal - F.initial := by
  obtain ⟨middle, hm⟩ := F.path_middle
  refine ⟨middle, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hm]
    exact F.path_simple
  · intro v
    rw [← hm, F.path_vertex_inventory]
    exact hW v
  · rw [← hm]
    exact F.path_rainbow
  · intro d
    rw [← hm, F.path_color_inventory]
    exact hD d
  · intro d hd
    apply F.path_difference_nonzero d
    exact F.path_color_inventory (fun a b : G => b - a) d |>.mpr ((hD d).mpr hd)
  · exact difference_labels_sum _ _ _

end FactorSystem


namespace FactorSystem

variable [Fintype I] {n : ℕ} [NeZero n]
variable (F : FactorSystem (fun a b : ZMod n => b - a) I J)

/-- The finite endpoint claim in the supplied project's positive-residue
representation. The project's recursive `pathGaps` has these same
consecutive labels. No density or universal probabilistic supplier is
assumed or proved here. -/
theorem joinFactors_zmod (W D : Finset (ZMod n))
    (hW : ∀ v, F.vertexInventory (fun a b : ZMod n => b - a) v ↔ v ∈ W)
    (hD : ∀ d, F.colorInventory (fun a b : ZMod n => b - a) d ↔ d ∈ D) :
    ∃ middle : List (ZMod n),
      ((F.initial :: middle) ++ [F.terminal]).Nodup ∧
      (∀ v, v ∈ (F.initial :: middle) ++ [F.terminal] ↔ v ∈ W) ∧
      (edgeLabels (fun a b : ZMod n => (b - a).val)
        ((F.initial :: middle) ++ [F.terminal])).Nodup ∧
      (∀ d : ℕ, d ∈ edgeLabels (fun a b : ZMod n => (b - a).val)
        ((F.initial :: middle) ++ [F.terminal]) ↔
        0 < d ∧ d < n ∧ (d : ZMod n) ∈ D) := by
  obtain ⟨middle, hs, hvs, hrs, hcs, hnz, _hsum⟩ :=
    F.joinFactors_on_targets (W : Set (ZMod n)) (D : Set (ZMod n)) hW hD
  refine ⟨middle, hs, hvs, ?_, ?_⟩
  · rw [edgeLabels_map (fun a b : ZMod n => b - a) ZMod.val]
    exact hrs.map (ZMod.val_injective n)
  · intro d
    rw [edgeLabels_map (fun a b : ZMod n => b - a) ZMod.val, List.mem_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      have hgD : g ∈ D := (hcs g).mp hg
      exact ⟨ZMod.val_pos.mpr (hnz g hgD), g.val_lt, by simpa using hgD⟩
    · rintro ⟨_hpos, hlt, hd⟩
      exact ⟨(d : ZMod n), (hcs _).mpr hd, ZMod.val_natCast_of_lt hlt⟩

end FactorSystem


/-! ## A closed, nonvacuous instance with a repeated virtual colour -/

namespace Example

def start (i : Fin 2) : ZMod 7 := if i = 0 then 0 else 3

def finish (i : Fin 2) : ZMod 7 := if i = 0 then 1 else 6

def forward (i : Fin 2) : Segment (ZMod 7) :=
  ⟨start i, [], finish i⟩

def reverse (i : Fin 2) : Segment (ZMod 7) :=
  ⟨finish i, [], start (Equiv.swap 0 1 i)⟩

/-- Forward edges are 0→1 and 3→6; the one real reverse edge is 1→3.
The excluded reverse entry is 6→0. -/
def twoByOneSystem :
    FactorSystem (fun a b : ZMod 7 => b - a) (Fin 2) (Fin 2) where
  forwardMap := Equiv.refl _
  externalMap := Equiv.swap 0 1
  exceptional := 1
  start := start
  finish := finish
  forward := forward
  reverse := reverse
  forward_first := by intro i; rfl
  forward_last := by intro i; rfl
  reverse_first := by intro i; rfl
  reverse_last := by intro i _; rfl
  endpoint_cycle := by
    change Equiv.Perm.IsCycleOn (Equiv.swap (0 : Fin 2) 1) Set.univ
    have hh := Equiv.Perm.isCycleOn_swap (by decide : (0 : Fin 2) ≠ 1)
    have hu : ({(0 : Fin 2), 1} : Set (Fin 2)) = Set.univ := by
      ext i
      fin_cases i <;> simp
    rw [hu] at hh
    exact hh
  body_simple := by decide
  body_disjoint := by
    simp only [List.disjoint_left]
    decide
  terminal_fresh := by decide
  color_simple := by decide
  color_disjoint := by
    simp only [List.disjoint_left]
    decide

theorem example_path :
    twoByOneSystem.path (fun a b : ZMod 7 => b - a) = [0, 1, 3, 6] := by
  decide

theorem example_real_colors :
    edgeLabels (fun a b : ZMod 7 => b - a)
      (twoByOneSystem.path (fun a b : ZMod 7 => b - a)) = [1, 2, 3] := by
  rw [example_path]
  decide

/-- The real path is rainbow although its virtual closing colour is 1,
the same as the real colour of 0→1. No assumption forbids this. -/
theorem virtual_color_collision :
    twoByOneSystem.terminal - twoByOneSystem.initial = (6 : ZMod 7) ∧
    twoByOneSystem.initial - twoByOneSystem.terminal = (1 : ZMod 7) ∧
    (1 : ZMod 7) ∈ edgeLabels (fun a b : ZMod 7 => b - a)
      (twoByOneSystem.path (fun a b : ZMod 7 => b - a)) := by
  rw [example_real_colors]
  decide

end Example

end EndpointFactor
