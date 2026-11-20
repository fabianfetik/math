import CorralFormalization.EndpointProof.Router.Permutation
import CorralFormalization.EndpointProof.Router.Greedy

/-! # Actual local settings act by the installed layer permutation

This finite bridge proves how a selected sublist acts on the endpoints of
a matching layer.  It does not take the desired router permutation or a
realized family of paths as an assumption.
-/
namespace EndpointRouter

open Equiv Equiv.Perm EndpointFactor
open scoped Classical
noncomputable section
universe u v
variable {α : Type u} [Fintype α] [DecidableEq α]

structure MatchingLayer (α : Type u) where
  edges : List (α × α)
  nodup : edges.Nodup
  no_loop : ∀ e ∈ edges, e.1 ≠ e.2
  separate : ∀ e ∈ edges, ∀ d ∈ edges, e ≠ d → [e.1,e.2,d.1,d.2].Nodup

namespace MatchingLayer
variable (L : MatchingLayer α)

def Incident (_L : MatchingLayer α) (i : α) (e : α × α) : Prop := i = e.1 ∨ i = e.2
def Isolated (i : α) : Prop := ¬ ∃ e ∈ L.edges, L.Incident i e

theorem incident_unique (i : α) (e : α × α) (hem : e ∈ L.edges)
    (d : α × α) (hdm : d ∈ L.edges)
    (he : L.Incident i e) (hd : L.Incident i d) : e = d := by
  by_contra hne
  have h := L.separate e hem d hdm hne
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,and_true] at h
  rcases he with he | he <;> rcases hd with hd | hd <;> grind

private theorem chosen_pairwise (chosen : List (α × α)) (hsub : chosen.Sublist L.edges) :
    (chosen.map (fun e => swap e.1 e.2)).Pairwise Equiv.Perm.Disjoint := by
  rw [List.pairwise_map]
  exact (L.nodup.sublist hsub).pairwise_of_forall_ne
    (fun e he d hd hne => disjoint_swap_swap (L.separate e (hsub.subset he) d (hsub.subset hd) hne))

theorem product_left (chosen : List (α × α)) (hsub : chosen.Sublist L.edges)
    (e : α × α) (he : e ∈ L.edges) :
    switchProduct chosen e.1 = if e ∈ chosen then e.2 else e.1 := by
  by_cases hchosen : e ∈ chosen
  · rw [if_pos hchosen]
    have hs : e.1 ∈ (swap e.1 e.2).support := by
      rw [support_swap (L.no_loop e he)]
      simp
    have hh := eq_on_support_mem_disjoint
      (f := swap e.1 e.2) (List.mem_map.mpr ⟨e,hchosen,rfl⟩)
      (L.chosen_pairwise chosen hsub) e.1 hs
    simpa only [swap_apply_left,switchProduct] using hh.symm
  · rw [if_neg hchosen]
    apply notMem_support.mp
    intro hs
    obtain ⟨s,hs,hx⟩ := exists_mem_support_of_mem_support_prod hs
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hs
    have hne : e ≠ d := by intro hed; exact hchosen (hed ▸ hd)
    have h := L.separate e he d (hsub.subset hd) hne
    have hnot : e.1 ∉ (swap d.1 d.2).support := by
      rw [support_swap (L.no_loop d (hsub.subset hd))]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,and_true] at h
      exact ⟨h.1.2.1,h.1.2.2⟩
    exact hnot hx

theorem product_right (chosen : List (α × α)) (hsub : chosen.Sublist L.edges)
    (e : α × α) (he : e ∈ L.edges) :
    switchProduct chosen e.2 = if e ∈ chosen then e.1 else e.2 := by
  by_cases hchosen : e ∈ chosen
  · rw [if_pos hchosen]
    have hs : e.2 ∈ (swap e.1 e.2).support := by
      rw [support_swap (L.no_loop e he)]
      simp
    have hh := eq_on_support_mem_disjoint
      (f := swap e.1 e.2) (List.mem_map.mpr ⟨e,hchosen,rfl⟩)
      (L.chosen_pairwise chosen hsub) e.2 hs
    simpa only [swap_apply_right,switchProduct] using hh.symm
  · rw [if_neg hchosen]
    apply notMem_support.mp
    intro hs
    obtain ⟨s,hs,hx⟩ := exists_mem_support_of_mem_support_prod hs
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hs
    have hne : e ≠ d := by intro hed; exact hchosen (hed ▸ hd)
    have h := L.separate e he d (hsub.subset hd) hne
    have hnot : e.2 ∉ (swap d.1 d.2).support := by
      rw [support_swap (L.no_loop d (hsub.subset hd))]
      simp only [Finset.mem_insert,Finset.mem_singleton,not_or]
      simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,or_false,not_or,and_true] at h
      exact ⟨h.2.1.1,h.2.1.2⟩
    exact hnot hx

theorem product_isolated (chosen : List (α × α)) (hsub : chosen.Sublist L.edges)
    (i : α) (hi : L.Isolated i) : switchProduct chosen i = i := by
  apply notMem_support.mp
  intro hs
  obtain ⟨s,hs,hi'⟩ := exists_mem_support_of_mem_support_prod hs
  obtain ⟨e,he,rfl⟩ := List.mem_map.mp hs
  apply hi
  refine ⟨e,hsub.subset he,?_⟩
  rw [support_swap (L.no_loop e (hsub.subset he))] at hi'
  simpa only [Incident,Finset.mem_insert,Finset.mem_singleton] using hi'

end MatchingLayer

/-- No-loop and nonoverlap data for the two concrete installed layers. -/
def firstMatchingLayer (n : ℕ) : MatchingLayer (Fin n) where
  edges := firstLayer n
  nodup := by
    have hinj : Function.Injective (adjacentEdge n) := by
      intro i j hij
      exact Fin.ext (congrArg (fun p : Fin n × Fin n => p.1.val) hij)
    exact ((List.nodup_finRange (n-1)).filter _).map hinj
  no_loop := by
    intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    intro heq
    have hh := congrArg Fin.val heq
    dsimp [adjacentEdge] at hh
    omega
  separate := firstLayer_disjoint n

def secondMatchingLayer (n : ℕ) : MatchingLayer (Fin n) where
  edges := secondLayer n
  nodup := by
    have hinj : Function.Injective (adjacentEdge n) := by
      intro i j hij
      exact Fin.ext (congrArg (fun p : Fin n × Fin n => p.1.val) hij)
    exact ((List.nodup_finRange (n-1)).filter _).map hinj
  no_loop := by
    intro e he
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    intro heq
    have hh := congrArg Fin.val heq
    dsimp [adjacentEdge] at hh
    omega
  separate := secondLayer_disjoint n

end
end EndpointRouter
