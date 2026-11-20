import CorralFormalization.EndpointProof.Factor.FragmentChecksum
import CorralFormalization.EndpointProof.Probability.LayeredSample.ExactMatching

/-!
# The actual fragment inventory receives exact-matching

This is the mathematical interface at the paper's sole exact closing call.
It uses the physical paths, colours, sets and one already-good layer
sample. It does not construct the paths or prove their edit-distance budget.
-/

open scoped BigOperators
namespace EndpointFactor.FragmentChecksum

open EndpointLayeredSample EndpointMatching.AbsorptionAssembly
open CorralFormalization.EndpointProof.RateBudget.SamplingConstants

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G] [DecidableEq G]

/-- Given a genuine disjoint rainbow fragment family, the original target
checksum forces the checksum of its *actual* remaining colours and endpoints.
exact-matching then supplies the physical closing matching. -/
theorem closingMatching_of_layered_event {m : ℕ} {d : Densities m} {s : Sample G m}
    (hE : ExactMatchingEvent d s)
    (paths : List (List G)) (starts ends used D X Y H : Finset G)
    (hpaths : [] ∉ paths) (hvertices : paths.flatten.Nodup)
    (hcolors : (paths.flatMap (edgeLabels (fun a b : G => b - a))).Nodup)
    (hstarts : (paths.map firstOrZero).toFinset = starts)
    (hends : (paths.map lastOrZero).toFinset = ends)
    (hused : (paths.flatMap (edgeLabels (fun a b : G => b - a))).toFinset = used)
    (hX : X ⊆ starts) (hY : Y ⊆ ends) (hH : H ⊆ D)
    (husedD : used = D \ H) (hXY : X.card = Y.card)
    (hHcard : H.card + X.card = starts.card)
    (hdisjoint : Disjoint (ends \ Y) (starts \ X)) (hzero : (0 : G) ∉ D)
    (htarget : (∑ d ∈ D, d) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hedit : (physicalEditDistance (vertexSet s (lastVertex m))
      (vertexSet s (firstVertex m)) (colourSet s (specialColour m))
      (ends \ Y) (starts \ X) H : ℝ) ≤
        (1 / 10^6 : ℝ) * kappa d.q * (Fintype.card G : ℝ)) :
    Nonempty (PhysicalDifferenceMatching (ends \ Y) (starts \ X) H) := by
  classical
  obtain ⟨hfirst, hlast⟩ := fragmentEndpoints_nodup paths hpaths hvertices
  have hs : starts.card = paths.length := by
    rw [← hstarts, List.toFinset_card_of_nodup hfirst, List.length_map]
  have he : ends.card = paths.length := by
    rw [← hends, List.toFinset_card_of_nodup hlast, List.length_map]
  have hsy := Finset.card_sdiff_add_card_eq_card hX
  have hey := Finset.card_sdiff_add_card_eq_card hY
  have hequal : (ends \ Y).card = (starts \ X).card := by omega
  have hequalH : (ends \ Y).card = H.card := by omega
  have hzH : (0 : G) ∉ H := fun h => hzero (hH h)
  have hchecksum := closing_checksum paths starts ends used D X Y H hfirst hlast hcolors
    hstarts hends hused hX hY hH husedD htarget
  exact exactMatchingEvent_apply hE (ends \ Y) (starts \ X) H hdisjoint hzH
    hequal hequalH hchecksum hedit

/-- Paper-shaped form: the closing bank's required size is derived from the
actual path and colour inventories and the original target cardinality. -/
theorem closingMatching_of_target_inventory {m : ℕ} {d : Densities m} {s : Sample G m}
    (hE : ExactMatchingEvent d s)
    (paths : List (List G)) (W starts ends used D X Y H : Finset G)
    (hpaths : [] ∉ paths) (hvertices : paths.flatten.Nodup)
    (hcolors : (paths.flatMap (edgeLabels (fun a b : G => b - a))).Nodup)
    (hW : paths.flatten.toFinset = W)
    (hstarts : (paths.map firstOrZero).toFinset = starts)
    (hends : (paths.map lastOrZero).toFinset = ends)
    (hused : (paths.flatMap (edgeLabels (fun a b : G => b - a))).toFinset = used)
    (hX : X ⊆ starts) (hY : Y ⊆ ends) (hH : H ⊆ D)
    (husedD : used = D \ H) (hXY : X.card = Y.card)
    (hDcard : D.card + X.card = W.card)
    (hdisjoint : Disjoint (ends \ Y) (starts \ X)) (hzero : (0 : G) ∉ D)
    (htarget : (∑ d ∈ D, d) = (∑ y ∈ Y, y) - ∑ x ∈ X, x)
    (hedit : (physicalEditDistance (vertexSet s (lastVertex m))
      (vertexSet s (firstVertex m)) (colourSet s (specialColour m))
      (ends \ Y) (starts \ X) H : ℝ) ≤
        (1 / 10^6 : ℝ) * kappa d.q * (Fintype.card G : ℝ)) :
    Nonempty (PhysicalDifferenceMatching (ends \ Y) (starts \ X) H) := by
  classical
  have hfirst := (fragmentEndpoints_nodup paths hpaths hvertices).1
  have hstarts_card : starts.card = paths.length := by
    rw [← hstarts, List.toFinset_card_of_nodup hfirst, List.length_map]
  have hfragment_card := fragmentFamily_inventory_card paths W used hpaths hvertices hcolors hW hused
  have hdiff_card := Finset.card_sdiff_add_card_eq_card hH
  rw [← husedD] at hdiff_card
  have hbank_card : H.card + X.card = starts.card := by omega
  exact closingMatching_of_layered_event hE paths starts ends used D X Y H hpaths hvertices
    hcolors hstarts hends hused hX hY hH husedD hXY hbank_card hdisjoint hzero htarget hedit

end
end EndpointFactor.FragmentChecksum
