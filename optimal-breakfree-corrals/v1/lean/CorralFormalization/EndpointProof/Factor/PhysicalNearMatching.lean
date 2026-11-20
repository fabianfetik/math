import CorralFormalization.EndpointProof.Factor.LayeredTransitions
import CorralFormalization.EndpointProof.Factor.ParameterBudget
import CorralFormalization.EndpointProof.Matching.Fractional.RobustWeights.PhysicalCoordinates

/-!
# Decode an ordinary tagged matching into actual directed differences

The transition theorem gives additive tagged hyperedges. This adapter
recovers the actual partial tail/head/colour sets and both bijections,
without assuming a prescribed checksum for the original target.
-/

open scoped BigOperators Classical
namespace EndpointLayeredSample

open EndpointTransitions EndpointFlow.AbelianTransport EndpointFractionalRawEvent
open EndpointMatching.AbsorptionAssembly EndpointMatching.Fractional.RobustWeights

noncomputable section

variable {G : Type*} [Fintype G] [AddCommGroup G]

def PhysicalNearMatching (T : PhysicalTarget G) (lower : ℝ) : Prop :=
  ∃ X Y C : Finset G, X ⊆ T 0 ∧ Y ⊆ T 1 ∧ C ⊆ T 2 ∧
    lower ≤ (X.card : ℝ) ∧ Nonempty (PhysicalDifferenceMatching X Y C)

/-- The unreflected physical sets belonging to a later role choice. -/
def physicalRoleSets {m : ℕ} (s : Sample G m) (roles : Fin 3 → RawRole m) :
    PhysicalTarget G := fun i =>
  match roles i with
  | Sum.inl v => vertexSet s v
  | Sum.inr c => colourSet s c

/-- The `(-X, Y, -C)` signs used for physical differences. -/
def explicitNegative (i : Fin 3) : Bool := decide (i ≠ 1)

theorem signedRoleSet_explicitSigns {m : ℕ} (s : Sample G m)
    (roles : Fin 3 → RawRole m) (i : Fin 3) :
    signedRoleSet s (roles i) (explicitNegative i) = signedSets (physicalRoleSets s roles) i := by
  ext g
  rw [signedSets_mem]
  by_cases hi : i = 1
  · subst i
    cases hrole : roles 1 with
    | inl v => simp [signedRoleSet, signedVertexSet, physicalRoleSets, vertexSet,
        explicitNegative, signCoordinate, hrole]
    | inr c => simp [signedRoleSet, signedColourSet, physicalRoleSets, colourSet,
        explicitNegative, signCoordinate, hrole]
  · cases hrole : roles i with
    | inl v => simp [signedRoleSet, signedVertexSet, physicalRoleSets, vertexSet,
        explicitNegative, signCoordinate, hi, hrole]
    | inr c => simp [signedRoleSet, signedColourSet, physicalRoleSets, colourSet,
        explicitNegative, signCoordinate, hi, hrole]

/-- Reflecting both raw and target sets preserves the one-sided deletion
count exactly, so the actual physical loss budget feeds ordinary-transition unchanged. -/
theorem explicitSignedLoss_card {m : ℕ} (s : Sample G m)
    (roles : Fin 3 → RawRole m) (T : PhysicalTarget G) (i : Fin 3) :
    ((signedRoleSet s (roles i) (explicitNegative i)) \ signedSets T i).card =
      ((physicalRoleSets s roles i) \ T i).card := by
  rw [signedRoleSet_explicitSigns, signedSets, signedSets,
    ← Finset.image_sdiff _ _ (signCoordinate_injective i),
    Finset.card_image_of_injective _ (signCoordinate_injective i)]

/-- ordinary transition lemma's three signed target parts are precisely the exact-matching physical target. -/
theorem targetVertices_signedSets (T : PhysicalTarget G) :
    targetVertices (signedSets T) = signedTarget (T 0) (T 1) (T 2) := by
  ext ⟨i, g⟩
  rw [mem_targetVertices, ← signedCoordinateSet_mem,
    signedCoordinateSet_signedTarget]

/-- Decode the covered part itself, proving containment and preserving the
number of matching edges, even when some numerical coordinates coincide. -/
theorem physicalNearMatching_of_tagged (T : PhysicalTarget G)
    (P : Finset (Vertex G)) (M : Matching P)
    (hP : P ⊆ targetVertices (signedSets T)) (lower : ℝ)
    (hcard : lower ≤ (M.edges.card : ℝ)) : PhysicalNearMatching T lower := by
  have hsub : ∀ i, physicalSets P i ⊆ T i := by
    intro i x hx
    have hx' : (i, signCoordinate i x) ∈ P := by
      simpa [physicalSets, signedSets_mem, signedCoordinateSet_mem] using hx
    have hxt : (i, signCoordinate i x) ∈ signedTarget (T 0) (T 1) (T 2) := by
      rw [← targetVertices_signedSets]
      exact hP hx'
    have hm : signCoordinate i x ∈
        signedCoordinateSet (signedTarget (T 0) (T 1) (T 2)) i :=
      (signedCoordinateSet_mem _ _ _).mpr hxt
    rw [signedCoordinateSet_signedTarget, signedSets_mem, signCoordinate_involutive] at hm
    exact hm
  have hslice : (slice P 0).card = (physicalSets P 0).card := by
    have hs : slice P 0 = (physicalSets P 0).image (fun x => (0, -x)) := by
      calc
        slice P 0 = slice (signedTarget (physicalSets P 0) (physicalSets P 1)
            (physicalSets P 2)) 0 := congrArg (fun W => slice W 0) (signedTarget_physicalSets P).symm
        _ = _ := signedTarget_slice_tail _ _ _
    rw [hs, Finset.card_image_of_injective]
    intro a b h
    exact neg_injective (congrArg Prod.snd h)
  have hsize : (physicalSets P 0).card = M.edges.card := by
    rw [← hslice]
    exact matching_slice_card M 0
  have M' : Matching (signedTarget (physicalSets P 0) (physicalSets P 1) (physicalSets P 2)) := by
    simpa only [signedTarget_physicalSets] using M
  exact ⟨physicalSets P 0, physicalSets P 1, physicalSets P 2,
    hsub 0, hsub 1, hsub 2, by simpa [hsize] using hcard,
    ⟨physicalDifferenceMatching_of_signedMatching M'⟩⟩

/-- The simultaneous layer event supplies actual directed partial matchings
for any later physical target, at the paper's one-sided signed loss budget. -/
theorem LayerTransitionEvent.physicalNearMatching {m : ℕ} {d : Densities m}
    {t η : ℝ} {s : Sample G m} (h : LayerTransitionEvent d t η s)
    (roles : Fin 3 → RawRole m) (negative : Fin 3 → Bool)
    (ha : ∀ i, DensityWindow d.q (roleDensity d (roles i)))
    (T : PhysicalTarget G) (ℓ : ℕ) (hbalance : ∀ i, (T i).card = ℓ)
    (hsize : |(ℓ : ℝ) - d.q * (Fintype.card G : ℝ)| ≤ η * (Fintype.card G : ℝ))
    (hloss : ∀ i, (((signedRoleSet s (roles i) (negative i)) \ signedSets T i).card : ℝ) ≤
      η * (Fintype.card G : ℝ)) :
    PhysicalNearMatching T ((ℓ : ℝ) - t * (Fintype.card G : ℝ)) := by
  have hb : ∀ i, (signedSets T i).card = ℓ := by
    intro i
    rw [signedSets, Finset.card_image_of_injective _ (signCoordinate_injective i), hbalance]
  obtain ⟨P, M, hP, hcard⟩ := h roles negative ha (signedSets T) ℓ hb hsize hloss
  exact physicalNearMatching_of_tagged T P M hP _ hcard

/-- The physical version needs only the paper's unreflected one-sided losses;
the signs and their cardinalities are paid by the preceding lemmas. -/
theorem LayerTransitionEvent.physicalNearMatching_of_physicalLoss
    {m : ℕ} {d : Densities m} {t η : ℝ} {s : Sample G m}
    (h : LayerTransitionEvent d t η s) (roles : Fin 3 → RawRole m)
    (ha : ∀ i, DensityWindow d.q (roleDensity d (roles i)))
    (T : PhysicalTarget G) (ℓ : ℕ) (hbalance : ∀ i, (T i).card = ℓ)
    (hsize : |(ℓ : ℝ) - d.q * (Fintype.card G : ℝ)| ≤ η * (Fintype.card G : ℝ))
    (hloss : ∀ i, (((physicalRoleSets s roles i) \ T i).card : ℝ) ≤
      η * (Fintype.card G : ℝ)) :
    PhysicalNearMatching T ((ℓ : ℝ) - t * (Fintype.card G : ℝ)) := by
  apply h.physicalNearMatching roles explicitNegative ha T ℓ hbalance hsize
  intro i
  simpa only [explicitSignedLoss_card] using hloss i

/-- For paper-admissible densities, the explicit role selection alone pays
the density window: no separate `a_i ∈ [0.9q,q]` assumption is needed. -/
theorem LayerTransitionEvent.physicalNearMatching_explicitRoles
    {m : ℕ} {d : Densities m} {t η : ℝ} {s : Sample G m}
    (h : LayerTransitionEvent d t η s) (hm : 0 < m) (hq : 0 < d.q)
    (hr : d.r ≤ 1/10) (hqr : 100*d.q ≤ d.r)
    (hqk : d.q*((m : ℝ)+12) = 1)
    (roles : Fin 3 → RawRole m) (hroles : ∀ i, NonReserveRole (roles i))
    (T : PhysicalTarget G) (ℓ : ℕ) (hbalance : ∀ i, (T i).card = ℓ)
    (hsize : |(ℓ : ℝ) - d.q * (Fintype.card G : ℝ)| ≤ η * (Fintype.card G : ℝ))
    (hloss : ∀ i, (((physicalRoleSets s roles i) \ T i).card : ℝ) ≤
      η * (Fintype.card G : ℝ)) :
    PhysicalNearMatching T ((ℓ : ℝ) - t * (Fintype.card G : ℝ)) := by
  apply h.physicalNearMatching_of_physicalLoss roles
    (fun i => explicitRole_densityWindow hm d hq hr hqr hqk (roles i) (hroles i))
    T ℓ hbalance hsize hloss

end
end EndpointLayeredSample
