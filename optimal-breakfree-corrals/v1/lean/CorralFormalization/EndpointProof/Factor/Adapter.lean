import CorralFormalization.EndpointProof.Factor.Join
import CorralFormalization.DiversityCompletion.CyclicEndpointInvariants

/-!
Local adapter between the returned finite factor theorem and the exact
endpoint-path proposition already used by the project's paper alignment.
This proves no existence of the factor system and no probabilistic endpoint
theorem: every `FactorSystem` field and both target inventories remain inputs.
-/

namespace EndpointFactor

open CorralFormalization.LatinCompletion.TerraceCompletion

theorem edgeLabels_zmod_eq_pathGaps {n : ℕ} (xs : List (ZMod n)) :
    edgeLabels (fun a b : ZMod n => (b - a).val) xs = pathGaps xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => rfl
    | cons y ys => simpa [edgeLabels, pathGaps] using congrArg (List.cons (y - x).val) ih

theorem FactorSystem.endpointPathClaim {I J : Type*} [Fintype I]
    {n : ℕ} [NeZero n]
    (F : FactorSystem (fun a b : ZMod n => b - a) I J)
    (W D : Finset (ZMod n))
    (hW : ∀ v, F.vertexInventory (fun a b : ZMod n => b - a) v ↔ v ∈ W)
    (hD : ∀ d, F.colorInventory (fun a b : ZMod n => b - a) d ↔ d ∈ D) :
    EndpointPathClaim W D F.initial F.terminal := by
  obtain ⟨middle, hsimple, hvertices, hrainbow, hcolors⟩ := F.joinFactors_zmod W D hW hD
  refine ⟨middle, hsimple, hvertices, ?_, ?_⟩
  · simpa only [edgeLabels_zmod_eq_pathGaps] using hrainbow
  · simpa only [edgeLabels_zmod_eq_pathGaps] using hcolors

end EndpointFactor
