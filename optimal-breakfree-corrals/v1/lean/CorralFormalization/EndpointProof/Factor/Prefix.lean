import CorralFormalization.EndpointProof.Factor.Adapter

/-!
Deterministic attachment of the short initial path used in the path-factor construction.

The prefix and the endpoint path are supplied, not constructed here.  The
statements expose both disjointness obligations and the exact inventories;
they prove neither the probabilistic factor supply nor the endpoint theorem.
`Segment` has at least one edge; the zero-edge case uses the supplied tail
claim directly after identifying the endpoints and inventories.
-/

namespace EndpointFactor

open CorralFormalization.LatinCompletion.TerraceCompletion

/-- Attach an actual nonempty-edge prefix to an existing endpoint path.
The common endpoint occurs once.  Vertex and directed-colour inventories
are matched exactly to the project's `EndpointPathClaim`. -/
theorem endpointPathClaim_prepend {n : ℕ} [NeZero n]
    (P : Segment (ZMod n)) (y : ZMod n) (W₀ D₀ W D : Finset (ZMod n))
    (htail : EndpointPathClaim W₀ D₀ P.last y)
    (hP : P.body.Nodup)
    (hdis : ∀ v ∈ P.body, v ∉ W₀)
    (hPrainbow : (P.colors (fun a b : ZMod n => (b - a).val)).Nodup)
    (hcdis : ∀ d ∈ P.colors (fun a b : ZMod n => (b - a).val),
      (d : ZMod n) ∉ D₀)
    (hW : ∀ v, v ∈ W ↔ v ∈ P.body ∨ v ∈ W₀)
    (hD : ∀ d : ℕ, 0 < d ∧ d < n ∧ (d : ZMod n) ∈ D ↔
      d ∈ P.colors (fun a b : ZMod n => (b - a).val) ∨
        (0 < d ∧ d < n ∧ (d : ZMod n) ∈ D₀)) :
    EndpointPathClaim W D P.first y := by
  obtain ⟨middle, hsimple, hvertices, hrainbow, hcolors⟩ := htail
  let edge : ZMod n → ZMod n → ℕ := fun a b => (b - a).val
  let tail : List (ZMod n) := (P.last :: middle) ++ [y]
  have hhead : tail.head? = some P.last := by simp [tail]
  have hbodyTail : List.Disjoint P.body tail := by
    intro v hv ht
    exact hdis v hv ((hvertices v).mp ht)
  have hcolorTail : List.Disjoint (P.colors edge) (edgeLabels edge tail) := by
    intro d hd ht
    have ht' : d ∈ pathGaps tail := by
      simpa only [edge, edgeLabels_zmod_eq_pathGaps] using ht
    exact hcdis d hd ((hcolors d).mp ht').2.2
  have htailRainbow : (edgeLabels edge tail).Nodup := by
    simpa only [edge, edgeLabels_zmod_eq_pathGaps] using hrainbow
  obtain ⟨hjoined, hlabels, hjoinedRainbow, _, _, _⟩ :=
    prepend_exact edge P tail hhead hP hsimple hbodyTail hPrainbow htailRainbow hcolorTail
  let middle' : List (ZMod n) := P.interior ++ [P.last] ++ middle
  have hlist : P.body ++ tail = ((P.first :: middle') ++ [y]) := by
    simp [Segment.body, tail, middle', List.append_assoc]
  refine ⟨middle', ?_, ?_, ?_, ?_⟩
  · simpa only [← hlist] using hjoined
  · intro v
    rw [← hlist, List.mem_append, hvertices v]
    exact (hW v).symm
  · rw [← hlist, ← edgeLabels_zmod_eq_pathGaps]
    exact hjoinedRainbow
  · intro d
    rw [← hlist, ← edgeLabels_zmod_eq_pathGaps, hlabels, List.mem_append,
      edgeLabels_zmod_eq_pathGaps, hcolors d]
    exact (hD d).symm

end EndpointFactor
